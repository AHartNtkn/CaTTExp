"""Execute the extra directed 5-boundaries on disk flags and on the 2×2 grid.

The disk check follows the named 3-events and individual 4-steps. The grid
check retains the moving slot versions and the actual 2-word at every event.
Neither evaluation uses the grounded rewrite tables.
"""
import argparse
from functools import cache

from check_four_slot_native import FourSlots, notation
from check_interchange_reachability import check_native_rule, disk, evaluate, globe_chain, instantiate
from check_two_moving_native import Evaluator, Route, Value, subschema
from interchange_free import read_query, tree_generators
from interchange_reachability import solve, verify
from reachability_theory import Block, Cell, OPERATIONS, RULES, chi, ctx, r, word
from response12_degree_five import EXTRA_RULES


SCHEMAS = {s.name: s for s in (*RULES, *EXTRA_RULES)}


def disk_walk(start, events):
    state = list(start)
    for event in events:
        if event == "C":
            assert [edge[0] for edge in state] == ["b", "a"]
            state.reverse()
        else:
            slot = event[0].lower()
            state[state.index(slot + "0")] = slot + "1"
    return tuple(state)


class DiskPair(Evaluator):
    """Two adjacent 4-globes. A0 and A1 are distinct parallel 3-generators."""

    def __init__(self):
        self.generators = {}
        data, _ = tree_generators([[[[[]]]], [[[[]]]]])
        for name, (d, bounds) in data.items():
            parts = name.split("/")
            s, t = (self.generators[b] for b in bounds) if bounds else (None, None)
            if d < 2:
                trace = (name,)
            elif d == 2:
                trace = ("ab"[int(parts[0])] + parts[-1],)
            elif d == 3:
                trace = ("AB"[int(parts[0])] + parts[-1],)
                assert disk_walk(s.trace, trace) == t.trace
            else:
                trace = Route((s.trace, t.trace), ("xy"[int(parts[0])],))
            self.generators[name] = Value(d, s, t, trace)

    @cache
    def apply(self, name, args):
        op = OPERATIONS[name]
        assert tuple(a.dim for a in args) == op.inputs, name
        if name[0] in "st" and name[1:].isdigit():
            return args[0].source if name[0] == "s" else args[0].target
        env = {f"x{i}": a for i, a in enumerate(args)}
        assert all(self.read(l, env) == self.read(r, env) for l, r in op.guards), name
        s, t = self.read(op.source, env), self.read(op.target, env)

        if name.startswith("id"):
            trace = Route((s.trace,)) if op.output == 4 else ()
        elif name.startswith("comp"):
            a, b = args
            trace = a.trace.then(b.trace) if op.output == 4 else a.trace + b.trace
        elif name.startswith(("left", "right")):
            a, b = args
            low, high = sorted(args, key=lambda v: v.dim)
            trace = high.trace
            if low.dim == 3:
                def insert(events):
                    return a.trace + events if a.dim == 3 else events + b.trace
                trace = trace.in_context(insert)
        elif name == "chi":
            trace = ("C",) if all(a.trace for a in args) else ()
        else:
            assert name in {"r", "t", "h", "iota"}
            # The only nonidentity specialization at an identity input is
            # h(A,id_b) = r(A,b). A 4-step retains its type and both 3-faces.
            if all(a.trace for a in args):
                label = name
            elif name == "h" and args[0].trace and args[1].source.trace:
                label = "r"
            else:
                label = None
            if label:
                trace = Route((s.trace, t.trace), (label,))
            else:
                assert s == t
                trace = Route((s.trace,))
        if op.output == 3:
            assert disk_walk(s.trace, trace) == t.trace
        if op.output == 4:
            assert (trace.states[0], trace.states[-1]) == (s.trace, t.trace)
        return Value(op.output, s, t, trace)


def boundaries(name, args, evaluate, prefix=None, suffix=None):
    faces = subschema(SCHEMAS[name], args, evaluate)
    values = [evaluate(ctx(prefix, f, suffix).term) for f in faces]
    assert values[0].dim == values[1].dim == 4
    assert (values[0].source, values[0].target) == (values[1].source, values[1].target)
    return tuple(v.trace for v in values)


def check_disk_pair():
    evaluate = DiskPair().read
    x, y = (Cell(4, f"{j}/0/0/0/0") for j in (0, 1))
    a, b = x.s, y.s
    cases = (
        ("H_L", (x, b), ("h x", "x h"),
         ("B0 C A0 / A0 B0 C / A1 B0 C", "B0 C A0 / B0 C A1 / A1 B0 C")),
        ("H_R", (a, y), ("y h", "h y"),
         ("B0 C A0 / B1 C A0 / A0 B1 C", "B0 C A0 / A0 B0 C / A0 B1 C")),
        ("K", (x, b), ("t x iota r", "x h t"),
         ("B0 C A0 / C B0 A0 / C B0 A1 / C A1 B0 / A1 C B0",
          "B0 C A0 / B0 C A1 / A1 B0 C / A1 C B0")),
        ("J", (x, y), ("y t x iota r", "x h y t"),
         ("B0 C A0 / B1 C A0 / C B1 A0 / C B1 A1 / C A1 B1 / A1 C B1",
          "B0 C A0 / B0 C A1 / A1 B0 C / A1 B1 C / A1 C B1")),
    )
    for name, args, labels, schedules in cases:
        for route, expected, schedule in zip(boundaries(name, args, evaluate), labels, schedules):
            assert route.labels == tuple(expected.split()), name
            assert route.states == tuple(tuple(s.split()) for s in schedule.split(" / ")), name

    def run(name, left, right, prefix=None, suffix=None):
        return boundaries(name, (left, right), evaluate, prefix, suffix)

    def identity(routes):
        left, right = routes
        assert left == right

    for name, args in (("H_L", (a.unit, b)), ("H_R", (a, b.unit)),
                       ("H_R", (a.s.unit, y)), ("K", (x, b.s.unit))):
        identity(run(name, *args))
    assert run("H_L", x, b.s.unit) == run("U_r", x, b.s)
    assert run("K", a.unit, b) == run("W", a, b)
    assert run("J", x, b.unit) == run("K", x, b)
    assert run("J", a.unit, b.unit) == run("W", a, b)

    # With x an identity, the unit specialization is two directed steps:
    # first W after y at S, then H_R before t1. Compare their meeting route.
    left, right = run("J", a.unit, y)
    variation = run("H_R", a, y)[0]
    w0, w1 = run("W", a, y.t)
    after_y = Route(variation.states[:2], variation.labels[:1])
    assert left == after_y.then(w0)
    hr0, hr1 = run("H_R", a, y)
    final_t = Route(right.states[-2:], right.labels[-1:])
    assert final_t.labels == ("t",)
    assert after_y.then(w1) == hr0.then(final_t)
    assert right == hr1.then(final_t)


def check_grid():
    evaluate = FourSlots().read
    X, Y = (Block.var(Cell(3, n), 0) for n in ("0/0/0/0", "0/1/0/0"))
    z, w = (Block.var(Cell(2, n), 1) for n in ("1/0/0", "1/1/0"))
    left, right = r(X, z).cell, r(Y, w).cell
    p = word(word(z, chi(X.face(), w)), Y.face()).cell
    s = word(word(X.face(True), chi(Y.face(True), z)), w).cell

    def run(name, a, b):
        return boundaries(name, (a, b), evaluate, p, s)

    assert tuple(map(notation, evaluate(left.term).trace.states)) == ("qX", "Xq")
    assert tuple(map(notation, evaluate(right.term).trace.states)) == ("rY", "Yr")
    routes = run("shifted_join", left, right)
    for route, expected, labels in zip(routes, (
            ("prYqXs", "pYrqXs", "pqXYrs", "pXqYrs"),
            ("prYqXs", "prYXqs", "pYrXqs", "pXqYrs")),
            (("r", "iota", "r"), ("r", "r", "iota"))):
        assert tuple(map(notation, route.states)) == expected
        assert route.labels == labels
        assert all(h.start == (("z", 0), ("w", 0), ("x", 0), ("y", 0))
                   and h.end == (("x", 1), ("y", 1), ("z", 0), ("w", 0))
                   for h in route.states)

    for a in (left.s, left.t):
        src, tgt = run("shifted_join", a.unit, right)
        assert src == tgt and src.labels == ("r", "iota")
    for b in (right.s, right.t):
        src, tgt = run("shifted_join", left, b.unit)
        assert (src, tgt) == run("N_L", left, b)
        assert (src.labels, tgt.labels) == (("iota", "r"), ("r", "iota"))


def check_compiler():
    schema = SCHEMAS["shifted_join"]
    env = {"X": "0/0/0/0/0", "Y": "0/1/0/0/0"}
    query = {"tree": [[disk(2), disk(2)]], "source": instantiate(schema.left, env),
             "target": instantiate(schema.right, env)}
    for theory in ("P", "response12"):
        model, a, b = read_query(dict(query, theory=theory))
        assert a != b
        forward, reverse = solve(model, a, b), solve(model, b, a)
        assert verify(model, a, b, forward) and verify(model, b, a, reverse)
        assert not reverse.reachable
        assert forward.reachable == (theory == "response12")
        if forward.reachable:
            step, = forward.steps
            assert not step.backwards and " shifted_join " in step.rule


def check_mixed_weights():
    # Give both variations a nonzero boundary-moment difference. Testing
    # only generating globes would leave the H_L drop identically zero.
    a, b, c, d = globe_chain((3, 2, 2, 3), 0)
    x = evaluate(("r", "a", "b"), {"a": a, "b": b})
    y = evaluate(("t", "c", "d"), {"c": c, "d": d})
    assert x.s.moment > x.t.moment and y.s.moment > y.t.moment
    for name, args, expected in (
        ("H_L", (x, y.s), y.s.t.length * (x.s.moment - x.t.moment)),
        ("H_R", (x.s, y), 0),
        ("K", (x, y.s), 2 * x.t.length * y.s.length),
        ("J", (x, y), 2 * x.t.length * y.t.length),
    ):
        schema = SCHEMAS[name]
        env = dict(zip((v for v, _ in schema.variables), args))
        assert all(evaluate(l, env) == evaluate(r, env) for l, r in schema.guards)
        lhs, rhs = evaluate(schema.left, env), evaluate(schema.right, env)
        assert (lhs.s, lhs.t) == (rhs.s, rhs.t) and lhs.length - rhs.length == expected


def check(all_disks=False):
    check_disk_pair()
    check_grid()
    check_mixed_weights()
    check_compiler()
    if all_disks:
        for schema in EXTRA_RULES:
            if schema.name != "shifted_join":
                check_native_rule(schema, 0, theory="response12")
        print("Verified forward and reverse reachability certificates on all five generic disks.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all-disks", action="store_true",
                        help="also ground the complete generic arity of each outer auxiliary")
    check(parser.parse_args().all_disks)
    print("Verified five directed schema boundaries, their unit specializations, "
          "both shifted-join schedules on the four-slot grid, and native "
          "reachability certificates in P and Response 12 on the suspended disk pair.")
