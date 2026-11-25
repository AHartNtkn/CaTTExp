"""Compile two-counter programs to integral, one-occurrence sheet presentations.

JSON 'program' is a list of ["inc", counter, next], ["test", counter, zero,
decremented], or ["halt"]; counters are 0 or 1 and labels are 0-based. A halt
runs a cleanup and ends at a shared sink with both counters zero. 'input' is
[state, counter0, counter1]. --rows emits actual module relations. --torsion
uses one free coordinate plus finite state labels and an external count of one.
"""
from argparse import ArgumentParser
from dataclasses import dataclass
from itertools import product
import json
from pathlib import Path


@dataclass(frozen=True)
class Side:
    state: int
    period: int
    residue: int


def compile_program(program):
    n = len(program)
    if not n:
        raise ValueError("empty program")
    edges = []
    for q, row in enumerate([*program, ["test", 0, n+1, n], ["test", 1, n+2, n+1]]):
        if row == ["halt"]:
            edges.append((Side(q, 1, 0), Side(n, 1, 0)))
            continue
        op, counter, *dest = row
        if counter not in (0, 1) or len(dest) != {"inc": 1, "test": 2}.get(op):
            raise ValueError("invalid instruction")
        if not all(type(d) is int and 0 <= d < (n if q < n else n+3) for d in dest):
            raise ValueError("invalid destination")
        p = (2, 3)[counter]
        if op == "inc":
            edges.append((Side(q, 1, 0), Side(dest[0], p, 0)))
        else:
            edges.append((Side(q, p, 0), Side(dest[1], 1, 0)))
            for r in range(1, p):
                edges.append((Side(q, p, r), Side(dest[0], p, r)))
    return n+3, edges


def vertex(state, k, dimension, torsion):
    if torsion:
        return (k, *(int(q == state) for q in range(dimension)))
    return dimension*k + state, 1


def generators(side, dimension, torsion):
    offset = vertex(side.state, side.residue, dimension, torsion)
    stride = (side.period if torsion else dimension * side.period, *(0 for _ in offset[1:]))
    return stride, offset


def transfer(vector, source, dest, dimension, torsion):
    # Solve the domain lattice coordinates, then use the same coordinates
    # on the image generators. In finite labels, lifts differ by multiples
    # of six and give the identical output.
    stride, offset = generators(source, dimension, torsion)
    new_stride, new_offset = generators(dest, dimension, torsion)
    if torsion:
        if any(v % 6 for i, v in enumerate(vector[1:]) if i != source.state):
            return None
        j = vector[1 + source.state] % 6
    else:
        j = vector[1]
    h, rest = divmod(vector[0] - j*offset[0], stride[0])
    if rest:
        return None
    y = tuple(h*a + j*b for a, b in zip(new_stride, new_offset))
    return (y[0], *(v % 6 for v in y[1:])) if torsion else y


def present(dimension, edges, conf, torsion):
    q, i, j = conf
    if not 0 <= q < dimension - 3 or min(i, j) < 0:
        raise ValueError("invalid input configuration")
    source = vertex(q, 2**i * 3**j, dimension, torsion)
    sink = vertex(dimension-1, 1, dimension, torsion)
    def col(w, v):
        return [(w, i, c) for i, c in enumerate(v) if c]
    rows = [[([], i, 6)] for i in range(1, len(sink))] if torsion else []
    for a, (s, d) in enumerate(edges, 1):
        for u, v in zip(generators(s, dimension, torsion), generators(d, dimension, torsion)):
            rows.append(col([a], u) + col([], [-c for c in v]))
    return dict(deck_rank=len(edges), rank=len(sink), relations=rows,
                steps=[col([], sink)], face=col([], source))


def run(program, conf, limit, torsion):
    dimension, edges = compile_program(program)
    present(dimension, edges, conf, torsion)  # validate the written input
    q, i, j = conf
    x = vertex(q, 2**i * 3**j, dimension, torsion)
    sink = vertex(dimension-1, 1, dimension, torsion)
    path = []
    seen = set()
    while True:
        if x == sink:
            # If a_l ... a_1 takes input to sink, the sheet at the step
            # must use its inverse, a_1^-1 ... a_l^-1.
            sheet = [-a for a in path]
            value = sink
            for a in reversed(sheet):
                s, d = edges[-a-1]
                value = transfer(value, d, s, dimension, torsion)
            assert value == vertex(q, 2**i * 3**j, dimension, torsion)
            return dict(status="placed", sheet=sheet)
        if x in seen:
            return dict(status="nonhalting cycle")
        if len(path) >= limit:
            return dict(status="step bound reached", transitions=len(path))
        seen.add(x)
        options = [(a, v) for a, (s, d) in enumerate(edges, 1)
                   if (v := transfer(x, s, d, dimension, torsion)) is not None]
        assert len(options) == 1
        a, x = options[0]
        path.append(a)


def line_solver(edges, inputs):
    """Complete commutative monomial rewrites for signed cyclic lattices."""
    def factors(n):
        v, d = {}, 2
        n = abs(n)
        while d*d <= n:
            while n % d == 0:
                v[d] = v.get(d, 0) + 1
                n //= d
            d += 1
        if n > 1:
            v[n] = 1
        return v

    if any(m == 0 or n == 0 for m, n in edges):
        raise ValueError("supply nonzero generators of the cyclic edge lattices")
    primes = sorted({p for z in [*inputs, *(x for edge in edges for x in edge)] for p in factors(z)})
    def monomial(x):
        f = factors(x)
        return (int(x > 0), int(x < 0), *(f.get(p, 0) for p in primes))
    rules, work = [], [(monomial(s*m), monomial(s*n)) for m, n in edges for s in (1, -1)]
    def replace(v, lhs, rhs):
        return tuple(x-l+r for x, l, r in zip(v, lhs, rhs))
    def normal(v):
        while True:
            for lhs, rhs in rules:
                if all(a <= b for a, b in zip(lhs, v)):
                    v = replace(v, lhs, rhs)
                    break
            else:
                return v
    while work:
        l, r = map(normal, work.pop())
        if l == r:
            continue
        if (sum(l), l) < (sum(r), r):
            l, r = r, l
        for old_l, old_r in rules:
            overlap = tuple(max(x, y) for x, y in zip(old_l, l))
            work.append((replace(overlap, l, r), replace(overlap, old_l, old_r)))
        rules.append((l, r))
    def decide(s, d):
        if not s or not d:
            return s == d
        return normal(monomial(s)) == normal(monomial(d))
    return decide


def audit():
    prog = [["test", 0, 3, 1], ["inc", 1, 2], ["inc", 1, 0], ["halt"]]
    dimension, edges = compile_program(prog)
    expected_steps = 0
    for torsion in (False, True):
        for q, i, j in product(range(len(prog)), range(6), range(6)):
            op, *args = prog[q]
            if op == "halt":
                target = len(prog), i, j
            else:
                c, *dest = args
                counts = [i, j]
                if op == "inc":
                    counts[c] += 1
                    target = dest[0], *counts
                elif counts[c]:
                    counts[c] -= 1
                    target = dest[1], *counts
                else:
                    target = dest[0], *counts
            t, u, v = target
            x = vertex(q, 2**i * 3**j, dimension, torsion)
            y = vertex(t, 2**u * 3**v, dimension, torsion)
            got = [(s, d, z) for s, d in edges
                   if (z := transfer(x, s, d, dimension, torsion)) is not None]
            assert len(got) == 1
            s, d, z = got[0]
            assert z == y and transfer(y, d, s, dimension, torsion) == x
            expected_steps += 1
        for i, j in product(range(6), repeat=2):
            result = run(prog, [0, i, j], 100, torsion)
            assert result["status"] == "placed" and len(result["sheet"]) == 5*i+j+4
        cycle = [["inc", 0, 1], ["test", 0, 2, 0], ["halt"]]
        assert run(cycle, [0, 0, 0], 10, torsion)["status"] == "nonhalting cycle"
    # A nonlocal equality can combine many off-path relation multipliers.
    # Compare fixed-word transport to full abelian lattice membership on a
    # finite subtree with extra side branches; every edge contributes both
    # gluing equations at the actual sheets.
    from semistrict_surface_divisible_squares import diagonalize
    size = len(edges)
    root, child = (), (3,)
    vertices = [root, child, (3, 1), (3, -2), (-size,)]
    index = {w: i for i, w in enumerate(vertices)}
    def row_at(w, v):
        row = [0] * (2 * len(vertices))
        row[2*index[w]:2*index[w]+2] = v
        return row
    rows = []
    for w in vertices[1:]:
        a = w[-1]
        s, d = edges[abs(a)-1]
        if a < 0:
            s, d = d, s
        for u, v in zip(generators(s, dimension, False), generators(d, dimension, False)):
            rows.append([i-j for i, j in zip(row_at(w, u), row_at(w[:-1], v))])
    mat, change, pivots = diagonalize(rows, 0, 2*len(vertices))
    lattice_checks = 0
    positive_checks = 0
    w = (3, 1)
    for x0, y0 in product(range(25), repeat=2):
        x, y = (x0, 1), (y0, 1)
        transported = x
        for a in reversed(w):
            if transported is not None:
                transported = transfer(transported, *edges[a-1], dimension, False)
        diff = [i-j for i, j in zip(row_at(w, x), row_at(root, y))]
        v = [sum(c*change[i][j] for i, c in enumerate(diff)) for j in range(len(diff))]
        member = all((v[j] % mat[j][j] == 0 if j < pivots else v[j] == 0) for j in range(len(v)))
        assert member == (transported == y)
        positive_checks += member
        lattice_checks += 1
    assert positive_checks > 0
    # The homogeneous crossing rules below preserve total prime valuation.
    # Their connected components are finite, so exact integer BFS is an
    # independent oracle even for negative membership answers.
    lines = [(4, -6), (9, 10)]
    targets = list(range(-32, 33))
    check_line = line_solver(lines, [*targets, 36])
    rank_one_checks = 0
    for start in (0, 2, -4, 6, -9, 18, 36):
        reached = {start}
        queue = [start]
        for v in queue:
            for m, n in [*lines, *((n, m) for m, n in lines)]:
                if v % m == 0 and (t := v//m*n) not in reached:
                    reached.add(t)
                    queue.append(t)
        for t in targets:
            assert check_line(start, t) == (t in reached)
            rank_one_checks += 1
    print(f"{expected_steps} independent instruction checks; 72 complete signed sheets, two cycle"
          f" rejections, {lattice_checks} lattice checks ({positive_checks} positive) and"
          f" {rank_one_checks} rank-one orbit checks passed")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path)
    parser.add_argument("--line", action="store_true", help="read edges, source and target on a cyclic vertex")
    parser.add_argument("--rows", action="store_true")
    parser.add_argument("--torsion", action="store_true")
    parser.add_argument("--limit", type=int, default=1000)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        if args.line:
            s, d = data["source"], data["target"]
            result = dict(placed=line_solver(data["edges"], [s, d])(s, d))
        else:
            p, c = data["program"], data["input"]
            result = (present(*compile_program(p), c, args.torsion) if args.rows
                      else run(p, c, args.limit, args.torsion))
        print(json.dumps(result))
    else:
        audit()
