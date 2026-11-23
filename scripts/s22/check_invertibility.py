"""Finite checks for the Boolean Gray model in the recorded-inverses response."""

from __future__ import annotations

import sys
from collections import Counter
from dataclasses import dataclass
from functools import cache
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from gray_globe_comparison import atom


@dataclass(frozen=True)
class Cell:
    bit: int
    source: Cell | None = None
    target: Cell | None = None

    def __post_init__(self):
        assert self.bit in (0, 1)
        if self.source is None or self.target is None:
            assert self.source is self.target is None
        else:
            assert parallel(self.source, self.target)
            assert self.bit <= min(self.source.bit, self.target.bit)


def parallel(s, t):
    return (s.source, s.target) == (t.source, t.target)


def identity(s):
    return Cell(s.bit, s, s)


def then(f, g):
    assert f.source is not None and f.target == g.source
    return Cell(min(f.bit, g.bit), f.source, g.target)


def whisker(bit, f):
    """Left or right multiplication by an object of E."""
    if f.source is None:
        return Cell(max(bit, f.bit))
    return Cell(max(bit, f.bit), whisker(bit, f.source), whisker(bit, f.target))


def check_globes():
    zero, one = Cell(0), Cell(1)
    layer = [zero, one]
    counts = []
    for _ in range(5):
        layer = [Cell(bit, s, t) for s, t in product(layer, repeat=2)
                 if parallel(s, t) for bit in range(min(s.bit, t.bit) + 1)]
        for f, g in product(layer, repeat=2):
            if (f.source, f.target) == (g.target, g.source):
                if then(f, g) == identity(f.source) and then(g, f) == identity(g.source):
                    assert f == identity(f.source)
        counts.append(len(layer))

    # aa has tensor unit 0 and p = 1. The object x in ab has label 1.
    p = x = one
    u, v = Cell(0, zero, p), Cell(0, p, zero)
    assert then(u, v) == identity(zero)
    assert then(v, u) != identity(p)
    pu, pv = whisker(p.bit, u), whisker(p.bit, v)
    assert whisker(x.bit, u) == whisker(x.bit, v) == identity(x)
    f = Cell(0, identity(x), identity(x))
    assert f != identity(identity(x))
    pf = whisker(p.bit, f)
    # The target interprets each marked comparison as the actual identity
    # at its displayed source. Check its target at the same globular type.
    for source, target in ((then(u, v), identity(zero)),
                           (then(pu, pv), identity(pu.source)),
                           (then(pv, pu), identity(pv.source)),
                           (pf, identity(whisker(p.bit, f.source)))):
        assert identity(source).target == target
    print(f"Gauntness in globular degrees 1–5 ({counts} cells). "
          "All four marked boundaries agree, and f is a nonidentity.")


def check_split_branch():
    """Follow the nonidentity cancellation through successive based globes."""
    base = identity(Cell(1))
    q = Cell(0, base, base)
    for _ in range(8):
        unit = identity(base)
        outgoing = Cell(0, q, unit)
        returning = Cell(0, unit, q)
        assert then(outgoing, returning) == identity(q)
        defect = then(returning, outgoing)
        assert defect.source == defect.target == unit
        assert defect != identity(unit)
        assert whisker(1, defect) == identity(unit)
        base, q = unit, defect
    print("Eight split contractions reproduce a nonidentity defect at the next base.")


# In a face address 0 and 1 are vertices and STAR denotes the whole interval.
STAR = 2


@cache
def faces(n):
    return tuple(product((0, 1, STAR), repeat=n))


def subcomplexes(n):
    all_faces = faces(n)
    inclusions = [(i, j) for i, f in enumerate(all_faces) for j, g in enumerate(all_faces)
                  if all(a == b or b == STAR for a, b in zip(f, g))]
    return [frozenset(f for f, bit in zip(all_faces, bits) if bit)
            for bits in product((0, 1), repeat=len(all_faces))
            if all(bits[i] >= bits[j] for i, j in inclusions)]


def tensor(left, m, right, n):
    return frozenset(a + b for a in faces(m) for b in faces(n) if a in left or b in right)


def replace_at(face, i, vertex):
    return face[:i] + (vertex,) + face[i+1:]


def paste(left, right, n, i):
    for f in faces(n):
        if f[i] == 1 and ((f in left) != (replace_at(f, i, 0) in right)):
            return None
    return frozenset(f for f in faces(n)
                     if (f[i] == 0 and f in left) or (f[i] == 1 and f in right)
                     or (f[i] == STAR and f in left and f in right))


def check_cubical_product():
    intervals, squares = subcomplexes(1), subcomplexes(2)
    assert (len(intervals), len(squares)) == (5, 48)
    checks = 0
    for left, right, i in product(squares, squares, (0, 1)):
        merged = paste(left, right, 2, i)
        if merged is None:
            continue
        for interval in intervals:
            assert tensor(merged, 2, interval, 1) == paste(
                tensor(left, 2, interval, 1), tensor(right, 2, interval, 1), 3, i)
            assert tensor(interval, 1, merged, 2) == paste(
                tensor(interval, 1, left, 2), tensor(interval, 1, right, 2), 3, i + 1)
            checks += 2
    for a, b, c in product(intervals, repeat=3):
        assert tensor(tensor(a, 1, b, 1), 2, c, 1) == tensor(a, 1, tensor(b, 1, c, 1), 2)
    print(f"{checks} cubical composition tests and {len(intervals)**3} associativity tests.")


def hemispheres(cube, face):
    """Meet over facets with negative/positive coefficient in the cubical boundary."""
    labels = [1, 1]
    sign = 0
    for i, coordinate in enumerate(face):
        if coordinate == STAR:
            for endpoint in (0, 1):
                labels[endpoint ^ sign] &= replace_at(face, i, endpoint) in cube
            sign ^= 1
    return tuple(labels)


def check_alternators():
    # The square classifying the 2-loop f has green boundary and red interior.
    f = frozenset(faces(2)) - {(STAR, STAR)}
    assert hemispheres(f, (STAR, STAR)) == (1, 1)
    alternators = end_faces = interior_faces = 0
    for r, start in product(range(1, 8), (0, 1)):
        unit_endpoints = [(start + i) % 2 for i in range(r)]
        cube = f
        for n, unit in enumerate(reversed(unit_endpoints), 2):
            # u and v each have the one green vertex mapping to p.
            cube = tensor({(1 - unit,)}, 1, cube, n)
        top = (STAR,) * (r + 2)
        assert top not in cube
        assert hemispheres(cube, top) == ((0, 1) if start == 0 else (1, 0))
        alternators += 1
        for i, unit in enumerate(unit_endpoints):
            assert replace_at(top, i, 1 - unit) in cube  # p acts constantly
            reduced = replace_at(top, i, unit)
            assert reduced not in cube
            boundary = hemispheres(cube, reduced)
            if r == 1:
                assert boundary == (1, 1)  # f
            elif i in (0, r - 1):
                assert set(boundary) == {0, 1}  # shorter alternator
                end_faces += 1
            else:
                # Equal adjacent letters after omitting an interior slot.
                # The two parallel faces and their filler have the same label.
                assert boundary == (0, 0)
                interior_faces += 1
    print(f"{alternators} oriented alternators through hom degree 9, "
          f"{end_faces} shorter end faces and {interior_faces} interior identity controls.")


def strip_table(m, start, end):
    """Send the principal atom of I ⊗ D^m to [2] ⊗ a based m-cell q."""
    def chain_image(chain):
        result = Counter()
        for (line_degree, side), (globe_degree, _) in chain:
            if globe_degree not in (0, m):
                continue  # The positive proper faces of q are iterated identities.
            label = "x" if globe_degree == 0 else "q"
            if line_degree == 0:
                vertex = (start, end)[side]
                result[vertex, vertex, label] += 1
            else:
                for vertex in range(start, end):
                    result[vertex, vertex + 1, label] += 1
        return result

    rows = atom(((1, 2), (m, 2)))
    return [(chain_image(source), chain_image(target)) for source, target in rows]


def whisker_tile(rows, edge):
    # Whisker by an ordinary edge at x. Only the two lowest rows change.
    whisker = Counter({(*edge, "x"): 1})
    rows[0] = (Counter({(0, 0, "x"): 1}), Counter({(2, 2, "x"): 1}))
    rows[1] = tuple(side + whisker for side in rows[1])
    return rows


def check_cylinder_strip():
    for m in range(2, 10):
        left = whisker_tile(strip_table(m, 0, 1), (1, 2))
        right = whisker_tile(strip_table(m, 1, 2), (0, 1))
        whole = strip_table(m, 0, 2)
        assert left[:m] == right[:m] == whole[:m]
        assert left[m][1] == right[m][0] == Counter({(1, 1, "q"): 1})
        assert left[m][0] == whole[m][0] == Counter({(0, 0, "q"): 1})
        assert right[m][1] == whole[m][1] == Counter({(2, 2, "q"): 1})
        for side in (0, 1):
            assert left[m+1][side] + right[m+1][side] == whole[m+1][side]
    print("Steiner strip in hom degrees 2–9: all lower rows, signed interfaces "
          "and both top chains agree.")


if __name__ == "__main__":
    check_globes()
    check_split_branch()
    check_cubical_product()
    check_alternators()
    check_cylinder_strip()
