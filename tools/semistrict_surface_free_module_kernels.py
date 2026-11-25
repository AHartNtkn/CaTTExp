"""Integral membership and syzygies over a finitely generated free deck.

Input: deck_rank, rank, relations, steps, face. Each column is a list of
[word, coordinate, coefficient] as in semistrict_surface_free_tree_placements.
Outputs signed coefficients for the face in the span of steps (null if
absent), orders (zero denotes infinite), and a presentation on the steps.
--counts also solves placement when the generated steps have finite exponent.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import product
from math import gcd, lcm
from pathlib import Path
import json

from semistrict_surface_divisible_squares import diagonalize
from semistrict_surface_free_tree_placements import local_names, reduced, solve, witness


def identity(n):
    return [tuple(int(i == j) for j in range(n)) for i in range(n)]


def combination(weights, rows, width):
    return tuple(sum(c * row[i] for c, row in zip(weights, rows, strict=True))
                 for i in range(width))


class Lattice:
    def __init__(self, rows, width):
        n = len(rows)
        matrix, self.change, self.rank = diagonalize(
            [list(e + tuple(row)) for e, row in zip(identity(n), rows)], n, width)
        self.n = n
        self.pivots = [matrix[i][n + i] for i in range(self.rank)]
        self.lifts = [r[:n] for r in matrix[:self.rank]]
        self.kernel = [r[:n] for r in matrix[self.rank:]]

    def transformed(self, v):
        return combination(v, self.change, len(v))

    def coords(self, v):
        y = self.transformed(v)
        if any(y[self.rank:]) or any(c % p for c, p in zip(y, self.pivots)):
            return None
        return combination([c // p for c, p in zip(y, self.pivots)], self.lifts, self.n)

    def order(self, v):
        y = self.transformed(v)
        if any(y[self.rank:]):
            return 0
        return lcm(*(abs(p) // gcd(p, c) for c, p in zip(y, self.pivots)))


def polynomial(summands, deck_rank):
    out = defaultdict(int)
    for scalar, word, expr in summands:
        if scalar:
            for w, i, n in expr:
                out[reduced((*word, *w), deck_rank), i] += scalar*n
    return tuple((w, i, n) for (w, i), n in sorted(out.items()) if n)


def poly_combo(weights, expressions, deck_rank, word=()):
    return polynomial(((c, word, e) for c, e in zip(weights, expressions, strict=True)), deck_rank)


def closure(rows, expressions, edges, width, deck_rank):
    rows, expressions = list(rows), list(expressions)
    basis = Lattice(rows, width)
    while True:
        length = len(rows)
        for a, pairs in edges.items():
            if not pairs:
                continue
            x, y = zip(*pairs)
            size = len(x)
            constraints = [*y, *(tuple(-c for c in r) for r in rows)]
            old_exprs = list(expressions)
            for solution in Lattice(constraints, width).kernel:
                v = combination(solution[:size], x, width)
                if basis.coords(v) is None:
                    rows.append(v)
                    expressions.append(poly_combo(solution[size:], old_exprs, deck_rank, (a,)))
                    basis = Lattice(rows, width)
        if length == len(rows):
            return rows, expressions, basis


def analyze(deck_rank, rank, relations, steps, face):
    names, columns = local_names(deck_rank, None, rank, [*relations, *steps, face])
    width = len(names)
    generators = identity(width)
    def vector(col):
        v = [0]*width
        for name, c in col:
            v[names[name]] += c
        return tuple(v)
    vectors = list(map(vector, columns))
    edges = {a: [] for j in range(1, deck_rank+1) for a in (j, -j)}
    for (w, i), j in names.items():
        if w:
            x, y = generators[j], generators[names[w[1:], i]]
            edges[w[0]].append((x, y))
            edges[-w[0]].append((y, x))
    local, _, killed = closure(vectors[:len(relations)], [()] * len(relations), edges, width, deck_rank)
    # A new leaf adds the quotient by the projection on its side of the
    # attaching edge. Every direction occurs on the boundary of every
    # finite subtree (take the last vertex on a ray in that direction).
    projections = [Lattice(local + [x for x, _ in pairs], width) for pairs in edges.values()]
    finite_rank = all(l.rank == width for l in projections)
    fg = all(all(l.coords(v) is not None for v in generators) for l in projections)
    images = vectors[len(relations):-1]
    seed = [(((), i, 1),) for i in range(len(images))]
    rows, exprs, span = closure(local + images, [()] * len(local) + seed, edges, width, deck_rank)
    coords = span.coords(vectors[-1])
    answer = None if coords is None else poly_combo(coords, exprs, deck_rank)
    # Local zero relations and both ends of each restricted edge, expressed
    # using the original steps. Local zero rows already have expression zero.
    syzygies = {poly_combo(z, exprs, deck_rank) for z in Lattice(rows, width).kernel}
    n = len(rows)
    pad = (0,)*width
    for a in range(1, deck_rank+1):
        if not edges[a]:
            continue
        constraints = [x + pad for x in rows] + [pad + y for y in rows]
        constraints += [tuple(-c for c in x+y) for x, y in edges[a]]
        for z in Lattice(constraints, 2*width).kernel:
            parent = poly_combo(z[:n], exprs, deck_rank)
            child = poly_combo(z[n:2*n], exprs, deck_rank)
            syzygies.add(polynomial([(1, (), parent), (-1, (a,), child)], deck_rank))
    syzygies.discard(())
    return dict(coordinates=answer, relations=sorted(syzygies),
                finitely_generated_abelian=fg, rational_rank=(width-killed.rank if finite_rank else None),
                orders=[killed.order(s) for s in images], face_order=killed.order(vectors[-1]))


def placements(data, result, counts):
    steps = data["steps"]
    if len(counts) != len(steps) or any(type(c) is not int or c < 0 for c in counts):
        raise ValueError("one nonnegative count per step required")
    if result["coordinates"] is None:
        return None
    if any(n == 0 for n in result["orders"]):
        raise ValueError("the finite-exponent placement solver requires torsion steps")
    if not steps:
        return []
    modulus = max(2, lcm(*result["orders"]))
    minima = solve(data["deck_rank"], modulus, len(steps),
                   [[((), i, 1)] for i in range(len(steps))], result["coordinates"], result["relations"])
    return witness(minima, counts, modulus)


def audit():
    def unit(w=(), c=1, i=0):
        return [(w, i, c)]
    def substitute(col, images, d):
        return polynomial(((n, w, images[i]) for w, i, n in col), d)

    # The free augmentation ideal has the two indicated free generators.
    # The third supplied generator is redundant, with a noncommuting syzygy.
    aa, bb = (1,), (2,)
    aug = [unit(aa) + unit(c=-1), unit(bb) + unit(c=-1),
           unit((1, 2)) + unit(c=-1)]
    data = dict(deck_rank=2, rank=1, relations=[], steps=aug)
    found = analyze(**data, face=unit((2, 1, -2, -1)) + unit(c=-1))
    assert found["coordinates"] is not None and found["orders"] == [0, 0, 0]
    assert found["rational_rank"] is None and not found["finitely_generated_abelian"]
    for row in found["relations"]:
        assert not substitute(row, aug, 2)
    quotient = dict(deck_rank=2, rank=3, relations=found["relations"], steps=[])
    assert analyze(**quotient, face=unit(i=2) + unit(c=-1) + unit(aa, -1, 1))["face_order"] == 1
    assert analyze(**quotient, face=unit(i=2) + unit(c=-1) + unit(bb, -1, 1))["face_order"] == 0
    assert analyze(**data, face=unit())["coordinates"] is None

    # Independent integer model for C_m x Z: a shears (x,y) -> (x+y,y),
    # b negates x. Compute all candidate signed spans by ordinary gcd.
    cases = 0
    for m in (2, 3, 4, 6):
        rels = [unit(c=m), unit(aa)+unit(c=-1), unit(aa,i=1)+unit(c=-1,i=1)+unit(c=-1),
                unit(bb)+unit(), unit(bb,i=1)+unit(c=-1,i=1)]
        for h in range(1, 4):
            steps = [unit(c=h), unit(c=2,i=1)]
            for i, j in product(range(3), range(3)):
                face = unit(c=i) + unit(c=j,i=1)
                out = analyze(2, 2, rels, steps, face)
                assert out["rational_rank"] == 1 and out["finitely_generated_abelian"]
                assert out["orders"] == [m//gcd(h,m), 0]
                assert out["face_order"] == (0 if j else m//gcd(i,m))
                assert (out["coordinates"] is not None) == (not j%2 and not i%gcd(m,h,2))
                def evaluate(col):
                    x = y = 0
                    for w, k, c in col:
                        u, v = ((1, 0), (0, 1))[k]
                        for a in reversed(w):
                            u = (-u if abs(a) == 2 else u+a*v) % m
                        x, y = x+c*u, y+c*v
                    return x % m, y
                for row in out["relations"]:
                    assert evaluate(substitute(row, steps, 2)) == (0, 0)
                if out["coordinates"] is not None:
                    assert evaluate(substitute(out["coordinates"], steps, 2)) == evaluate(face)
                cases += 1
    # Response 243: this element survives integrally despite vanishing at
    # every finite modulus. Its translates all have exponent two.
    y = unit(bb) + unit(c=-2)
    data = dict(deck_rank=2, rank=1, relations=[unit(aa)+unit(c=-2), unit(bb,2)+unit(c=-4)],
                steps=[y], face=y)
    found = analyze(**data)
    assert found["orders"] == [2] and found["face_order"] == 2
    assert found["rational_rank"] == 1 and not found["finitely_generated_abelian"]
    assert placements(data, found, [1]) is not None
    assert placements(data, found, [0]) is None
    for depth in range(1, 6):
        root = unit((2,) + (-1,)*depth) + unit((-1,)*depth, -2)
        assert analyze(2, 1, data["relations"], [], root)["face_order"] == 2**(depth+1)
    print(f"{cases} integral action comparisons, free augmentation syzygies, five Prüfer roots,"
          " and an exact torsion placement invisible in all ambient finite quotients passed")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path)
    parser.add_argument("--counts", nargs="*", type=int)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        result = analyze(**data)
        if args.counts is not None:
            result["sheets"] = placements(data, result, args.counts)
        print(json.dumps(result))
    else:
        audit()
