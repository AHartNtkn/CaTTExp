"""Execute native P terms on the three-slot tree with moving x,y and stationary z.

The left outer branch traverses x then y. Each has two consecutive advances.
The right outer branch has the single stationary slot z. We keep the full
order of 3-events and every intermediate history of each 4-route. The
test checks endpoints and a forward delta instance; it does not decide
reachability between arbitrary parallel routes on the tree.
"""
from dataclasses import dataclass
from functools import cache

from interchange_free import tree_generators
from interchange_reachability import Path
from interchange_two_moving import ground_all
from interchange_path_grading import History, cross, i_faces, r_faces
from reachability_theory import Block, Cell, EQUATIONS, OPERATIONS, RULES, inner, paste, r, word


TREE = [[[[], []], [[], []]], [[]]]


@dataclass(frozen=True)
class Route:
    states: tuple
    labels: tuple = ()

    def then(self, other):
        assert self.states[-1] == other.states[0]
        return Route(self.states + other.states[1:], self.labels + other.labels)

    def in_context(self, action):
        return Route(tuple(action(h) for h in self.states), self.labels)


@dataclass(frozen=True)
class Value:
    dim: int
    source: object
    target: object
    trace: object


def generators():
    data, _ = tree_generators(TREE)
    slots = {"0/0": "x", "0/1": "y", "1/0": "z"}
    result = {}
    for name, (d, bounds) in data.items():
        s, t = (result[b] for b in bounds) if bounds else (None, None)
        if d == 0:
            trace = name
        elif d == 1:
            trace = (name,)
        elif d == 2:
            branch, i = name.rsplit("/", 1)
            trace = ((slots[branch], int(i)),)
        else:
            assert d == 3
            trace = History(s.trace, ((s.trace[0][0],),))
            assert trace.end == t.trace
        result[name] = Value(d, s, t, trace)
    return result


def composition(a, b):
    if a.dim == b.dim:
        if a.dim < 3:
            return a.trace + b.trace
        return a.trace.then(b.trace)
    low, high = (a, b) if a.dim < b.dim else (b, a)
    if low.dim == 1:
        return high.trace
    if low.dim == 2:
        def act(history):
            return history.pad(left=a.trace) if a.dim == 2 else history.pad(right=b.trace)
    else:
        assert low.dim == 3 and high.dim == 4
        def act(history):
            return low.trace.then(history) if a.dim == 3 else history.then(low.trace)
    return act(high.trace) if high.dim == 3 else high.trace.in_context(act)


class Evaluator:
    def __init__(self):
        self.generators = generators()

    @cache
    def apply(self, name, args):
        schema = OPERATIONS[name]
        assert tuple(a.dim for a in args) == schema.inputs, name
        if name[0] in "st" and name[1:].isdigit():
            return args[0].source if name[0] == "s" else args[0].target
        env = {f"x{i}": x for i, x in enumerate(args)}
        assert all(self.read(l, env) == self.read(r, env) for l, r in schema.guards), name
        s = self.read(schema.source, env)
        t = self.read(schema.target, env)
        if name.startswith("id"):
            trace = (History(args[0].trace) if schema.output == 3 else
                     Route((args[0].trace,)) if schema.output == 4 else ())
        elif name.startswith(("comp", "left", "right")):
            trace = composition(*args)
        elif name == "chi":
            trace = cross(*(a.trace for a in args))
        elif name in ("r", "iota"):
            first, last = (r_faces if name == "r" else i_faces)(*(a.trace for a in args))
            trace = Route((first, last), (name,))
        else:
            raise AssertionError(name)
        if schema.output == 3:
            assert (trace.start, trace.end) == (s.trace, t.trace)
        elif schema.output == 4:
            assert (trace.states[0], trace.states[-1]) == (s.trace, t.trace)
            assert all((h.start, h.end) == (s.trace.start, s.trace.end) for h in trace.states)
        return Value(schema.output, s, t, trace)

    def read(self, expr, env=None):
        if env is None:
            env = self.generators
        if isinstance(expr, str):
            return env[expr]
        return self.apply(expr[0], tuple(self.read(child, env) for child in expr[1:]))


def notation(history):
    """x/y advance names carry their value; p=zx, q=zy."""
    version = dict(history.start)
    result = []
    for e in history.events:
        if len(e) == 2:
            result.append({("z", "x"): "p", ("z", "y"): "q"}[e])
        else:
            slot, = e
            version[slot] += 1
            result.append(slot + str(version[slot]))
    return " ".join(result)


def terms():
    def block(d, name, branch=0):
        return Block.var(Cell(d, name), branch)

    x0, x2, y0 = (block(2, name) for name in ("0/0/0", "0/0/2", "0/1/0"))
    X1, X2, Y1, Y2 = (block(3, name) for name in
                       ("0/0/0/0", "0/0/1/0", "0/1/0/0", "0/1/1/0"))
    z = block(2, "1/0/0", 1)
    crossed_x = lambda x: word(word(x, z), y0)
    uncrossed_x = lambda x: word(word(z, x), y0)
    crossed_y = lambda y: word(word(x2, y), z)
    uncrossed_y = lambda y: word(x2, word(z, y))
    A = paste(word(r(X1, z), y0).cell, crossed_x(X2).cell)
    B = paste(uncrossed_x(X1).cell, word(r(X2, z), y0).cell)
    C = paste(word(x2, r(Y1, z)).cell, crossed_y(Y2).cell)
    D = paste(uncrossed_y(Y1).cell, word(x2, r(Y2, z)).cell)
    return dict(zip("ABCD", (A, B, C, D))), X1, Y1, x0, y0, z


def subschema(schema, args, evaluate):
    assert tuple(cell.d for cell in args) == tuple(d for _, d in schema.variables)
    env = {name: v.term for (name, _), v in zip(schema.variables, args)}
    def sub(expr):
        if isinstance(expr, str):
            return env[expr]
        return (expr[0], *(sub(a) for a in expr[1:]))
    assert all(evaluate(sub(l)) == evaluate(sub(r)) for l, r in schema.guards)
    return Cell(4, sub(schema.left)), Cell(4, sub(schema.right))


def complete_route(letters, pieces):
    early, late = pieces["A"].s, pieces["C"].s
    result = None
    for label in letters:
        step = pieces[label]
        if label in "AB":
            action = paste(step, late)
            early = step.t
        else:
            action = paste(early, step)
            late = step.t
        result = action if result is None else paste(result, action)
    return result


def check_grounded_rule(name, source, target):
    """Compare the native faces with the interval compiler's oriented rewrite."""
    def letters(history):
        return ''.join({('x',): 'X', ('y',): 'Y', ('z', 'x'): 'a',
                        ('z', 'y'): 'b'}[event] for event in history.events)

    local = letters(source.states[0])
    prefix = '' if 'a' in local else 'a'
    suffix = '' if 'b' in local else 'b'
    presentation, moves = ground_all(local.count('X'), local.count('Y'))
    lookup = {(edge.source, edge.target, moves[key].kind): key
              for key, edge in presentation.edges.items()}

    def path(route):
        states = [prefix + letters(h) + suffix for h in route.states]
        return Path(states[0], tuple(lookup[a, b, 'i' if label == 'iota' else label]
                                     for a, b, label in zip(states, states[1:], route.labels)))

    lhs, rhs = path(source), path(target)
    assert any(q == rhs and step.rule.startswith(name + ' ') and not step.backwards
               for step, q in presentation.successors(lhs)), name


def check():
    evaluate = Evaluator().read
    pieces, X, Y, x, y, z = terms()
    for name, piece in pieces.items():
        trace = evaluate(piece.term).trace
        assert trace.labels == ("r",) and trace.states[0] != trace.states[1]
    source, target = [evaluate(complete_route(w, pieces).term) for w in ("CDAB", "CADB")]
    assert source.trace != target.trace
    check_grounded_rule("delta", source.trace, target.trace)
    outside = ("p x1 x2 q y1 y2", "x1 x2 p y1 y2 q")
    for route in (source, target):
        assert (notation(route.source.trace), notation(route.target.trace)) == outside
    assert tuple(map(notation, source.trace.states[1:-1])) == (
        "p x1 x2 y1 q y2", "p x1 x2 y1 y2 q", "x1 p x2 y1 y2 q")
    assert tuple(map(notation, target.trace.states[1:-1])) == (
        "p x1 x2 y1 q y2", "x1 p x2 y1 q y2", "x1 p x2 y1 y2 q")

    rules = {s.name: s for s in RULES}
    eqs = {s.name: s for s in EQUATIONS}
    A, B, C, D = (pieces[k] for k in "ABCD")
    before, after = paste(A.s, C), paste(B, D.t)
    for delta_face, expected in zip(subschema(rules["delta"], (A, D), evaluate), (source, target)):
        assert evaluate(paste(paste(before, delta_face), after).term) == expected

    X2 = Cell(3, "0/0/1/0")
    Y2 = Cell(3, "0/1/1/0")
    left = lambda value: paste(value, z.cell.face(1))
    right = lambda value: paste(value, z.cell.face(1, True))
    cases = ((eqs["10"], (X.cell, X2, z.cell),
              ("p x1 x2", "x1 x2 p"), ("x1 p x2",), (("r",), ("r", "r"))),
             (eqs["20"], (left(X.cell), left(X2), y.cell, z.cell),
              ("q x1 x2", "x1 x2 q"), ("x1 q x2",), (("iota",), ("iota", "iota"))),
             (eqs["21"], (x.cell, z.cell, right(Y.cell), right(Y2)),
              ("y1 y2 p", "p y1 y2"), ("y1 p y2",), (("iota",), ("iota", "iota"))),
             (rules["N_L"], (r(X,z).cell, right(Y.cell)),
              ("y1 p x1", "x1 p y1"), ("p x1 y1", "y1 x1 p"), (("iota", "r"), ("r", "iota"))),
             (rules["N_R"], (left(X.cell), r(Y,z).cell),
              ("q y1 x1", "x1 y1 q"), ("y1 q x1", "x1 q y1"), (("r", "iota"), ("iota", "r"))),
             (eqs["14"], (X.cell, y.cell, z.cell),
              ("p q x1", "x1 p q"), ("p x1 q",), (("r",), ("iota", "r"))),
             (eqs["15"], (x.cell, Y.cell, z.cell),
              ("p q y1", "p y1 q"), ("y1 p q",), (("r", "iota"), ("r",))),
             (rules["U_r"], (inner(X, Y).cell, z.cell),
              ("p q y1 x1", "x1 y1 p q"), ("y1 x1 p q", "p q x1 y1"),
              (("r", "iota"), ("iota", "r"))))
    for schema, args, endpoints, middles, labels in cases:
        routes = [evaluate(face.term).trace for face in subschema(schema, args, evaluate)]
        check_grounded_rule(schema.name, *routes)
        assert tuple(q.labels for q in routes) == labels
        for q in routes:
            assert (notation(q.states[0]), notation(q.states[-1])) == endpoints
        assert tuple(notation(h) for q in routes for h in q.states[1:-1]) == middles


if __name__ == "__main__":
    check()
    print("Executed four proper mixed inputs, both contextual delta faces, "
          "all five nontrivial equation families and all three naturality families.")
