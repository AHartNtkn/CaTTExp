"""Execute the four-slot rectangle and its contextual K15 equality in native P syntax.

The two branches carry xy and zw. The moving slots have one advance each.
The stationary slots keep the order zw. A,B exchange X first with zx, then
with wx. C,D exchange Y first with zy, then with wy. The two active inputs
of the prescribed rectangle are A and D.
"""
from itertools import combinations

from check_interchange_reachability import instantiate
from check_two_moving_native import Evaluator, Route, Value, complete_route, subschema
from interchange_free import tree_generators
from interchange_path_grading import History
from reachability_theory import Block, Cell, EQUATIONS, RULES, chi, paste, r, vertical, word


TREE = [[[[]], [[]]], [[], []]]
SLOTS = {"0/0": "x", "0/1": "y", "1/0": "z", "1/1": "w"}
EVENTS = {("x",): "X", ("y",): "Y", ("w", "x"): "p", ("z", "x"): "q",
          ("w", "y"): "r", ("z", "y"): "s"}


class FourSlots(Evaluator):
    def __init__(self, keep="xyzw"):
        data, globes = tree_generators(TREE)
        assert not globes
        self.generators = {}
        for name, (d, bounds) in data.items():
            s, t = (self.generators[b] for b in bounds) if bounds else (None, None)
            if d == 0:
                trace = name
            elif d == 1:
                branch, index = name.split("/")
                before = sum(SLOTS[f"{branch}/{j}"] in keep for j in range(int(index)))
                trace = (f"{branch}/{before}",)
            elif d == 2:
                branch, version = name.rsplit("/", 1)
                slot = SLOTS[branch]
                trace = ((slot, int(version)),) if slot in keep else ()
            else:
                assert d == 3
                trace = History(s.trace, ((s.trace[0][0],),) if s.trace else ())
                assert trace.end == t.trace
            self.generators[name] = Value(d, s, t, trace)

    def apply(self, name, args):
        value = super().apply(name, args)
        if name == "r" and (not args[0].trace.events or not args[1].trace):
            assert value.source == value.target
            return Value(4, value.source, value.target, Route((value.source.trace,)))
        return value


def notation(history):
    return "".join(EVENTS[e] for e in history.events)


def stationary_split(update, z, w):
    """Construct the two contextual elementary r-cells of equation (12)."""
    before = word(z, chi(update.face(), w))
    after = word(chi(update.face(True), z), w)
    first = paste(before.cell, word(r(update, z), w).cell)
    second = paste(word(z, r(update, w)).cell, after.cell)
    block = r(update, word(z, w))
    return tuple(Block(cell, block.start, block.initial, block.final) for cell in (first, second))


def pieces(evaluate):
    X, Y = (Block.var(Cell(3, name), 0) for name in ("0/0/0/0", "0/1/0/0"))
    z, w = (Block.var(Cell(2, name), 1) for name in ("1/0/0", "1/1/0"))
    eq = next(s for s in EQUATIONS if s.name == "12")
    early, late = stationary_split(X, z, w), stationary_split(Y, z, w)
    for update, split in ((X, early), (Y, late)):
        merged, expanded = subschema(eq, (update.cell, z.cell, w.cell), evaluate)
        assert merged.term == r(update, word(z, w)).cell.term
        assert expanded.term == paste(*(piece.cell for piece in split)).term
    A, B = (word(move, Y.face()).cell for move in early)
    C, D = (word(X.face(True), move).cell for move in late)
    return dict(zip("ABCD", (A, B, C, D))), X, Y, z, w


def erase(history, keep):
    projected = History(tuple(v for v in history.start if v[0] in keep),
                        tuple(e for e in history.events if all(slot in keep for slot in e)))
    assert projected.end == tuple(v for v in history.end if v[0] in keep)
    return projected


def check_rectangle(evaluate, moves):
    # Native routes retain the spectator on the other moving slot and the
    # unexchanged stationary crossing in the relevant temporal prefix/suffix.
    supports = {"A": set("xz"), "B": set("xw"), "C": set("yz"), "D": set("yw")}
    local = {"A": ("pqX", "pXq"), "B": ("pXq", "Xpq"),
             "C": ("rsY", "rYs"), "D": ("rYs", "Yrs")}
    for label, move in moves.items():
        route = evaluate(move.term).trace
        assert route.labels == ("r",)
        assert tuple(map(notation, route.states)) == local[label]
    for size in range(5):
        for subset in combinations("xyzw", size):
            keep = set(subset)
            contracted = FourSlots(keep).read
            preserved = set()
            for label, move in moves.items():
                start, end = evaluate(move.term).trace.states
                image = contracted(move.term)
                assert (image.source.trace, image.target.trace) == (erase(start, keep), erase(end, keep))
                if image.trace.labels:
                    assert image.trace.labels == ("r",) and image.source != image.target
                    preserved.add(label)
                else:
                    assert image.trace == Route((image.source.trace,)) and image.source == image.target
            assert preserved == {label for label, support in supports.items() if support <= keep}
            assert ({"A", "D"} <= preserved) == (size == 4)

    histories = {
        "CDAB": ("pqXrsY", "pqXrYs", "pqXYrs", "pXqYrs", "XpqYrs"),
        "CADB": ("pqXrsY", "pqXrYs", "pXqrYs", "pXqYrs", "XpqYrs"),
        "ABCD": ("pqXrsY", "pXqrsY", "XpqrsY", "XpqrYs", "XpqYrs"),
    }
    routes = {seq: evaluate(complete_route(seq, moves).term) for seq in histories}
    for seq, route in routes.items():
        assert tuple(map(notation, route.trace.states)) == histories[seq]
        assert route.source.trace.start == (("z", 0), ("w", 0), ("x", 0), ("y", 0))
        assert route.target.trace.end == (("x", 1), ("y", 1), ("z", 0), ("w", 0))

    A, B, C, D = (moves[label] for label in "ABCD")
    prefix, suffix = paste(A.s, C), paste(B, D.t)
    delta = next(s for s in RULES if s.name == "delta")
    for seq, face in zip(("CDAB", "CADB"), subschema(delta, (A, D), evaluate)):
        assert evaluate(vertical(prefix, face, suffix).term) == routes[seq]
    return routes["ABCD"].trace.states[2]


def check_block(evaluate, X, Y, z, w, intermediate):
    # At the middle 3-history of ABCD both adjacent rows of the crossing
    # rectangle occur between X and Y, at the correct versions x1 and y0.
    x, y = X.face(True), Y.face()
    xy, zw = word(x, y), word(z, w)
    prefix = word(word(zw, X), y)
    suffix = word(word(x, Y), zw)
    equations = {s.name: s for s in EQUATIONS}
    representatives = []
    for name, args, order in (("7a", (x.cell, y.cell, zw.cell), "XpqrsY"),
                              ("7b", (xy.cell, z.cell, w.cell), "XprqsY")):
        equation = equations[name]
        env = {k: v.term for (k, _), v in zip(equation.variables, args)}
        assert all(evaluate(instantiate(l, env)) == evaluate(instantiate(r, env))
                   for l, r in equation.guards)
        assert instantiate(equation.left, env) == chi(xy, zw).cell.term
        expansion = Cell(3, instantiate(equation.right, env))
        path = vertical(prefix.cell, expansion, suffix.cell)
        value = evaluate(path.term)
        assert value.dim == 3 and notation(value.trace) == order
        representatives.append(value)
    row, column = representatives
    assert row.trace == intermediate and row.trace != column.trace
    assert (row.source, row.target) == (column.source, column.target)


def check():
    evaluate = FourSlots().read
    moves, X, Y, z, w = pieces(evaluate)
    intermediate = check_rectangle(evaluate, moves)
    check_block(evaluate, X, Y, z, w, intermediate)


if __name__ == "__main__":
    check()
    print("Executed four mixed r inputs, both contextual delta faces, both contextual K15 "
          "expansions, and all 16 slot contractions.")
