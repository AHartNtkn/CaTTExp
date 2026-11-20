"""Lift a projected cubical 2-cell between prescribed strict paths."""
import argparse
from collections import defaultdict
from functools import cache
from itertools import pairwise, product

from gray_globe_comparison import face, strict_cells
from gray_globe_cubical_corner import cube_label, project, section, symbols
from gray_globe_section import trim


@cache
def path_word(path):
    state = symbols(path[0][0][0])
    edges = {symbols(g) for g in path[1][0]} if len(path) > 1 else set()
    word = []
    while edges:
        i, edge = next((i, bits) for i, x in enumerate(state) if x == 0
                       and (bits := state[:i] + (2,) + state[i+1:]) in edges)
        edges.remove(edge)
        state = state[:i] + (1,) + state[i+1:]
        word.append(i)
    assert state == symbols(path[0][1][0])
    return tuple(word)


def square_at(start, word, pos):
    bits = list(start)
    for i in word[:pos]:
        bits[i] = 1
    for i in word[pos:pos+2]:
        bits[i] = 2
    return cube_label(bits)


def swap(word, pos):
    a, b = word[pos:pos+2]
    return word[:pos] + (b, a) + word[pos+2:]


@cache
def visible_crossings(z):
    if len(z) < 3:
        return ()
    lifted = section(z)
    word = path_word(face(lifted, 0))
    start = symbols(lifted[0][0][0])
    pending = set(lifted[2][0])
    visible = []
    while pending:
        pos, square = next((pos, g) for pos, (a, b) in enumerate(pairwise(word))
                           if a < b and (g := square_at(start, word, pos)) in pending)
        a, b = word[pos:pos+2]
        if b == a+1:
            visible.append(a)
        pending.remove(square)
        word = swap(word, pos)
    assert word == path_word(face(lifted, 1))
    return tuple(visible)


@cache
def inversions(word):
    return frozenset((b, a) for i, a in enumerate(word) for b in word[i+1:] if b < a)


def relative_lift(z, p, q):
    """Return the 2-tableau, identity padding included, or None if the ends obstruct it."""
    assert p[0] == q[0]
    assert (project(p), project(q)) == tuple(trim(face(z, i)) if len(z) == 3 else z
                                            for i in (0, 1))
    word, target = path_word(p), path_word(q)
    if not inversions(word) <= inversions(target):
        return None
    start = symbols(p[0][0][0])
    squares = []

    def advance(allowed):
        nonlocal word
        while True:
            pos = next((i for i, (a, b) in enumerate(pairwise(word)) if (a, b) in allowed), None)
            if pos is None:
                return
            squares.append(square_at(start, word, pos))
            word = swap(word, pos)

    for a in visible_crossings(z):
        # Close Inv(word) under the single new relation a+1 before a.
        old = inversions(word)
        lower = [u for u in word if u == a or (u, a) in old]
        upper = [v for v in word if v == a+1 or (a+1, v) in old]
        allowed = old | set(product(lower, upper))
        assert allowed <= inversions(target)
        advance(allowed)
        assert inversions(word) == allowed
    advance(inversions(target))
    assert word == target
    def edges(w):
        return w[1][0] if len(w) > 1 else ()
    chain = tuple(sorted(squares))
    return p[:1] + ((edges(p), edges(q)), (chain, chain))


def check(h):
    level = strict_cells((1,)*h, 2)
    fibres = defaultdict(set)
    truth = defaultdict(set)
    for cell in level:
        z = project(cell)
        p, q = (trim(face(cell, i)) for i in (0, 1))
        fibres[project(p)].add(p)
        fibres[project(q)].add(q)
        truth[z].add((p, q))
    counts = [0, 0]
    for z, witnesses in truth.items():
        s, t = (tuple(trim(face(z, i)) for i in (0, 1)) if len(z) == 3 else (z, z))
        for p, q in product(fibres[s], fibres[t]):
            lifted = relative_lift(z, p, q)
            assert (lifted is not None) == ((p, q) in witnesses)
            if lifted is not None:
                assert lifted in level and project(lifted) == z
                assert tuple(trim(face(lifted, i)) for i in (0, 1)) == (p, q)
            counts[lifted is None] += 1
    print(f'Width {h}: {len(truth)} projected cells, {counts[0]} liftable and '
          f'{counts[1]} obstructed prescribed path pairs.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('width', type=int)
    args = parser.parse_args()
    if args.width < 1:
        parser.error('width must be positive')
    check(args.width)
