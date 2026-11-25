"""Realize finite-exponent modules inside the divisible part of fifth homotopy.

Input to --compile is {modulus, rank, relations, hopfs?}. A relation is a
column of [g, i, c], where g is [left_word, right_word] in a product of two
free groups. The first two letters of the left factor supply the free pair.
At modulus two each requested Hopf column introduces a fourth sphere.
Output rows are on integral fifth spheres, plus the stated Hopf attachments.
With --example evaluate such a column on one fifth sphere, for the explicit
raw Z x C3 and joined C2 x C3 group-basis readings of Response 246.
"""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import lcm
from pathlib import Path
import json

from semistrict_surface_free_module_kernels import analyze

IDENTITY = ((), ())
A = ((1,), ())
B = ((2,), ())


def reduce_word(w):
    result = []
    for a in w:
        if type(a) is not int or not a:
            raise ValueError("use signed nonzero integer letters")
        if result and result[-1] == -a:
            result.pop()
        else:
            result.append(a)
    return tuple(result)


def times(g, h):
    return tuple(reduce_word((*v, *w)) for v, w in zip(g, h, strict=True))


def increment(i, modulus):
    return [(B, i, 1), (IDENTITY, i, -modulus)]


def expand(col, modulus):
    values = defaultdict(int)
    for g, i, c in col:
        for h, _, n in increment(i, modulus):
            values[times(g, h), i] += n*c
    return [(g, i, c) for (g, i), c in sorted(values.items()) if c]


def compile_module(modulus, rank, relations, hopfs=()):
    if modulus < 2 or rank < 1 or (hopfs and modulus != 2):
        raise ValueError("use a nontrivial modulus, positive rank and binary Hopf coefficients")
    if any(not 0 <= i < rank for col in [*relations, *hopfs] for _, i, _ in col):
        raise ValueError("a column uses an unknown generator")
    rels = []
    for i in range(rank):
        rels.append([(A, i, 1), (IDENTITY, i, -modulus)])
        rels.append([(g, j, modulus*c) for g, j, c in increment(i, modulus)])
    return dict(fifth_spheres=rank, fourth_spheres=len(hopfs),
                reversible_rows=rels+[expand(r, modulus) for r in relations],
                hopf_values=[expand(col, modulus) for col in hopfs])


def normal_form(col, modulus):
    """Evaluate a finite integral sphere sum before adding the input relations."""
    rational, torsion = defaultdict(Fraction), defaultdict(Fraction)
    for g, i, c in col:
        left, right = map(reduce_word, g)
        cut = len(left)
        while cut and abs(left[cut-1]) <= 2:
            cut -= 1
        coset = left[:cut], right
        z, table = Fraction(1), {}
        for a in reversed(left[cut:]):
            table = {reduce_word((a, *w)): v for w, v in table.items()}
            if a > 0:
                if a == 2:
                    table[()] = (table.get((), 0) + z/modulus) % 1
                z *= modulus
            else:
                z /= modulus
                if a == -2:
                    table[(-2,)] = (table.get((-2,), 0) - z/modulus) % 1
        rational[coset, i] += c*z
        for w, v in table.items():
            key = times(coset, (w, ())), i
            torsion[key] = (torsion[key] + c*v) % 1
    return ({k:v for k, v in rational.items() if v}, {k:v for k, v in torsion.items() if v})


def example(col):
    q, d = normal_form(col, 2)
    if q or any((2*v).denominator != 1 for v in d.values()):
        return {"raw": False, "joined": False, "in_bounded_layer": False}
    def read(quotient):
        support = set()
        for ((left, right), i), v in d.items():
            if i != 0 or any(abs(a) > 2 for a in (*left, *right)):
                raise ValueError("the example has two free letters per factor and one fifth sphere")
            first = sum((a == 1)-(a == -1) for a in left)-sum((a == 1)-(a == -1) for a in right)
            second = sum((a == 2)-(a == -2) for a in left)-sum((a == 2)-(a == -2) for a in right)
            if int(2*v) % 2:
                support.symmetric_difference_update({(first % 2 if quotient else first, second % 3)})
        return not support
    return {"raw": read(False), "joined": read(True), "in_bounded_layer": True}


def finite_weight(col, modulus=2):
    """Separate a nonzero rational projection over F(a,b) x F(c,d)."""
    if any(i or any(abs(a)>2 for w in g for a in w) for g,i,_ in col):
        raise ValueError("the example uses two generators per factor and one sphere")
    rational, _ = normal_form(col, modulus)
    if not rational:
        return None
    sample = next(iter(rational.values()))
    ring = modulus*abs(sample.numerator)+1
    sites = {()}
    for (_, w), _i in rational:
        sites.update(w[j:] for j in range(len(w)))
    vertices = sorted(sites)
    index = {x:i for i,x in enumerate(vertices)}
    perms = {}
    for a in (1, 2):
        move = {index[x]: index[y] for x in vertices if (y := reduce_word((a, *x))) in sites}
        missing = sorted(set(index.values()) - set(move.values()))
        move.update(zip(sorted(set(index.values()) - move.keys()), missing, strict=True))
        perms[a] = move
        perms[-a] = {y:x for x,y in move.items()}
    residual = [0]*len(vertices)
    for (left, right), _, c in col:
        x = index[()]
        for a in reversed(right):
            x = perms[a][x]
        h = sum(1 if a>0 else -1 for a in left)
        residual[x] = (residual[x] + c*pow(modulus, h, ring)) % ring
    assert any(residual)
    return dict(coefficient_modulus=ring, left_scalar=modulus, root=index[()],
                right_actions=[[perms[a][j] for j in range(len(vertices))] for a in (1,2)],
                residual=residual)


def audit():
    # Check the integral linear presentation against independent word reduction
    # in the tree solver, including sums above and below the exponent layer.
    words = [(), (1,), (-1,), (2,), (-2,), (1, 2), (2, 1), (-2, -1), (2, -1)]
    tests = 0
    for m in (2, 3, 6):
        result = compile_module(m, 1, [])
        rels = [[(g[0], i, c) for g,i,c in row] for row in result["reversible_rows"]]
        for w,v in product(words, repeat=2):
            col = [((w, ()), 0, 1), ((v, ()), 0, -1)]
            q,d = normal_form(col, m)
            actual = analyze(2, 1, rels, [], [(g[0], i, c) for g, i, c in col])["face_order"]
            assert actual == (0 if q else lcm(*(f.denominator for f in d.values())))
            tests += 1

    # With a larger left factor as well as an independent right factor,
    # test the exact location of every surviving translated torsion letter.
    shifts = [((w, v), i, 1) for w in (*words, (3, 1, -2), (2, 3, -1))
              for v in ((), (1, -2), (2, 1)) for i in (0, 1)]
    for m in (2, 6):
        for g, i, _ in shifts:
            q, d = normal_form(expand([(g, i, 1)], m), m)
            assert not q and d == {(g, i):Fraction(1, m)}

    # Finite example with one added Hopf row corresponding to a^2.
    def difference(g):
        return [(g, 0, 1), (IDENTITY, 0, -1)]
    relators = [((1,), (1,)), ((2,), (2,)), ((2, 2, 2), ()), ((1, 2, -1, -2), ())]
    ctx = compile_module(2, 1, [difference(g) for g in relators], [difference(((1, 1), ()))])
    for row in ctx["reversible_rows"]:
        assert example(row)["raw"]
    h = example(ctx["hopf_values"][0])
    assert h == {"raw":False, "joined":True, "in_bounded_layer":True}
    results = defaultdict(int)
    for n, k in product(range(-8, 9), repeat=2):
        left = (1 if n > 0 else -1,)*abs(n) + (2 if k > 0 else -2,)*abs(k)
        c = example(expand(difference((left, ())), 2))
        assert c["raw"] == (n == 0 and k % 3 == 0)
        assert c["joined"] == (n % 2 == k % 3 == 0)
        results[c["raw"],c["joined"]] += 1
    assert not example([(IDENTITY, 0, 1)])["in_bounded_layer"]
    # This root is genuinely of order four and outside the Hopf layer.
    assert not example([(((2,-1), ()), 0, 1), (((-1,), ()), 0, -2)])["in_bounded_layer"]
    for w, v in product(words, repeat=2):
        col = [(((), w), 0, 1), (((), v), 0, -1)]
        reading = finite_weight(col)
        assert (reading is None) == (w == v)
        if reading:
            assert sum(reading["residual"]) == reading["coefficient_modulus"]
    assert finite_weight(ctx["hopf_values"][0]) is None
    print(f"{tests} order comparisons, {2*len(shifts)} independent translated generator readings,"
          f" 289 face pairs ({results[False,True]} joined-only) and 81 finite-weight tests passed")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--compile", type=Path)
    parser.add_argument("--example", type=Path)
    parser.add_argument("--finite", type=Path, help="construct a separating finite weight for the example")
    args = parser.parse_args()
    if args.compile:
        print(json.dumps(compile_module(**json.loads(args.compile.read_text()))))
    elif args.finite:
        print(json.dumps(finite_weight(json.loads(args.finite.read_text()))))
    elif args.example:
        print(json.dumps(example(json.loads(args.example.read_text()))))
    else:
        audit()
