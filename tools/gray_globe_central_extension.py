"""Check the common four-dimensional boundary for extending the (3,3) atom by pure axes."""
from collections import Counter

from gray_globe_attachments import ordered_factors
from gray_globe_comparison import face
from gray_globe_factorizations import profile, rank, truncate
from gray_globe_section import cells
from gray_globe_strip_squares import exchanges, minimal_shape, peel
from gray_globe_three_blocks import endpoints
from gray_path_wedge import compose


def central_row(row):
    sites = set(map(rank, row))
    return {(2, 3), (3, 2)} <= sites and not sites & {(1, 4), (4, 1)}


def compare_words():
    witnessed = {patch for sites, patch in exchanges() if sites == (1, 4)}
    counts = Counter()
    for z in endpoints():
        first = peel(z, (0, 1, 4, 3))
        last = peel(z, (0, 4, 1, 3))
        if first == last:
            counts['same'] += 1
            continue
        i, j = [k for k, (a, b) in enumerate(zip(first, last)) if a != b]
        assert j == i+1
        pair = compose(first[i], first[j], 3)
        assert {rank(g) for g in pair[4][0]} == {(1, 3), (4, 0)}
        assert pair in witnessed
        assert pair == compose(last[i], last[j], 3)
        counts['exchange'] += 1
    print('Critical four-state comparisons:', dict(counts))


def check():
    compare_words()
    critical_four = endpoints()
    shapes = set()
    remaining = set()
    counts = Counter()
    states = [set(), set()]
    for w in cells((5, 5)):
        if len(w) <= 5:
            continue
        sites = profile(w)
        if (4, 3) in sites or (3, 4) in sites:
            continue
        good = central_row(w[5][0])
        assert good == central_row(w[5][1])
        if good:
            assert all(truncate(w, 4, d) in critical_four for d in (0, 1))
            assert not {(4, 1), (1, 4)} & sites
            assert all(max(r, s) <= 3 or min(r, s) == 0 for r, s in sites)
            if len(w) >= 7:
                assert all(central_row(face(w, d)[5][0]) for d in (0, 1))
            counts['with atom' if (3, 3) in sites else 'shared'] += 1
        if len(w) != 7 or len(w[6][0]) != 1 or (3, 3) not in sites:
            continue
        (shapes if good else remaining).add(minimal_shape(w))
        for d in (0, 1):
            states[not good].add(minimal_shape(face(w, d)))
        if not good:
            # Put the incident degree-five pair in one group at cut four.
            owner = {p: 0 if p == (3, 3) or p in ((2, 3), (3, 2)) else p[0]+1
                     for p in sites if sum(p) > 4}
            pieces = ordered_factors(w, 4, owner)
            central, = [p for p in pieces if (3, 3) in profile(p)]
            assert central_row(central[5][0])
            assert all(p == central or len(p) == 6 and len(p[5][0]) == 1 for p in pieces)
            # At cut four all operands share their lower 3-poles and glue at
            # exactly the four-state provided by their signs.
            for a, b in zip(pieces, pieces[1:]):
                assert a[:4] == b[:4] and a[4][1] == b[4][0]
    assert (len(shapes), len(remaining)) == (25, 96) and shapes.isdisjoint(remaining)
    print('Covered cells in the selected five-rows:', dict(counts))
    print('Single (3,3) shapes and distinct signed five-faces:',
          (len(shapes), len(states[0])), (len(remaining), len(states[1])))


if __name__ == '__main__':
    check()
