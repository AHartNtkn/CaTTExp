"""Construct raw single-crossing insertions between positive square-quotient faces."""
import argparse
from itertools import combinations, permutations, product

from semistrict_surface_square_quotient import (
    SquareQuotient, evaluate, inverse, multiply, parse_word, spelling,
)


def cycles(p):
    seen = set()
    for i in range(len(p)):
        if i in seen:
            continue
        orbit = []
        while i not in seen:
            orbit.append(i)
            seen.add(i)
            i = p[i]
        yield sorted(orbit)


def distance(p, q):
    return len(p)-sum(1 for _ in cycles(multiply(inverse(p), q)))


def lowering_swap(p, q):
    for cycle in cycles(multiply(inverse(p), q)):
        if len(cycle) == 1:
            continue
        for i, j in combinations(cycle, 2):
            for source, end in ((True, p), (False, q)):
                if end[i] > end[j]:
                    other = list(end)
                    other[i], other[j] = other[j], other[i]
                    return source, tuple(other)
    raise AssertionError('distinct endpoints have a descent on a relative cycle')


def crossing(p, lower):
    w = spelling(p, 0)
    for i in range(len(w)):
        if evaluate(len(p), w[:i]+w[i+1:]) == lower:
            return w, i
    raise AssertionError('the inverted pair must cross in a reduced spelling')


def witness(n, left, right):
    p, q = evaluate(n, left), evaluate(n, right)
    k, end = len(left), len(right)
    spare = end-k-distance(p, q)
    if spare < 0:
        return None
    assert spare % 2 == 0
    forward, backward = [], []
    w = left
    for _ in range(spare):
        forward.append((w, len(w), 1))
        w += (1,)
    k += spare
    while p != q:
        source, lower = lowering_swap(p, q)
        if source:
            w, i = crossing(p, lower)
            pad = (1, 1)*((k-len(w))//2)
            forward.append((pad+w, len(pad)+i, w[i]))
            p, k = lower, k+1
        else:
            w, i = crossing(q, lower)
            pad = (1, 1)*((end-len(w))//2)
            forward_word = pad+w[:i]+w[i+1:]
            backward.append((forward_word, len(pad)+i, w[i]))
            q, end = lower, end-1
    assert k == end
    return forward + backward[::-1]


def verify(n, left, right, path):
    if path is None:
        return
    w = left
    for before, i, x in path:
        assert len(before) == len(w) and evaluate(n, before) == evaluate(n, w)
        assert 0 <= i <= len(before) and 1 <= x < n
        w = before[:i]+(x,)+before[i:]
    assert len(w) == len(right) and evaluate(n, w) == evaluate(n, right)


def checks():
    judgments = insertions = 0
    for n in range(2, 6):
        model = SquareQuotient(n, [(2, (), (1,))]) if n <= 4 else None
        states = [(p, h) for p in permutations(range(n)) for h in range(2)]
        for (p, a), (q, b) in product(states, repeat=2):
            l, r = spelling(p, a), spelling(q, b)
            path = witness(n, l, r)
            verify(n, l, r, path)
            if model:
                for signed in (False, True):
                    assert model.reachable((p, a), (q, b), signed) == (path is not None)
                judgments += 1
            if path is not None:
                insertions += len(path)
    old = tuple(parse_word(s) for s in ('3,2,1,1,1,1', '2,1,3,2,2,1,3,2'))
    path = witness(4, *old)
    assert len(path) == 2
    verify(4, *old, path)
    print(f'{judgments} raw/signed comparisons, {insertions} verified insertions through width five')
    print('Response 54 boundary (source spelling, zero-based slot, inserted letter)', path)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--width', type=int)
    ap.add_argument('--faces', nargs=2, type=parse_word)
    args = ap.parse_args()
    if args.faces is None:
        checks()
    else:
        if args.width is None or args.width < 2:
            ap.error('--faces requires --width at least two')
        path = witness(args.width, *args.faces)
        verify(args.width, *args.faces, path)
        print('raw insertion certificate', path)
