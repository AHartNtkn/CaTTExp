"""Literal colour lifts and geometric intersections of signed seam facets."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from graphlib import CycleError, TopologicalSorter
from itertools import product
from pathlib import Path

from catt import comp2, infer, subst_tm, subst_ty, v
from emit_agda import Emitter
from relative_coherence_coloured_faces import visible
from relative_coherence_hidden_seam import identity
from relative_coherence_seam_cycles import compatible, two_bridges
from relative_coherence_spherical_fibres import catt_context, ring
from relative_coherence_strip_fibres import Complex, lane_charts, substitute


def inverse_erasure(base, colours):
    """All typed preimages of one raw term. Each new variable maps into base."""
    old = tuple(map(v, range(len(base))))
    domain = base + tuple(infer(base, value) for value in colours)
    sigma = old + tuple(colours)

    @cache
    def lifts(term):
        found = {v(i) for i, value in enumerate(sigma) if value == term}
        if term[0] == 'coh':
            _, arity, boundary, args = term
            partial = [()]
            for ty, arg in zip(arity, args):
                partial = [prefix + (value,) for prefix in partial for value in lifts(arg)
                           if infer(domain, value) == subst_ty(ty, prefix)]
            found.update(('coh', arity, boundary, args1) for args1 in partial)
        return frozenset(found)

    return domain, sigma, lifts


def check_raw_lifts(agda_path):
    emitter = Emitter()

    def certify(label, ctx, erasure, erased, values):
        if agda_path:
            for i, value in enumerate(sorted(values)):
                emitter.check_type(f"{label}-{i}", ctx, value, infer(ctx, value))
                emitter.check_eq(f"{label}-{i}", value, erasure, erased)

    base, _, rows = catt_context(6)
    # A_2 spans signal 1 and seam 2. Decorate the stationary lanes on its sides.
    a2 = v(len(base) - 13 + 2)
    left = comp2(base, 1, rows[1]['p'], rows[1]['p'])
    right = comp2(base, 1, rows[5]['d'], rows[5]['d'])
    domain, sigma, lifts = inverse_erasure(base, (left, right))
    h, j = v(len(base)), v(len(base) + 1)

    def padded(ctx, x, y):
        block = comp2(ctx, 0, x, a2)
        return comp2(ctx, 0, block, comp2(ctx, 0, rows[4]['l'], y))

    term = padded(base, left, right)
    for raise_dim in (False, True):
        erased = identity(base, term) if raise_dim else term
        expected = {padded(domain, x, y) for x, y in product((left, h), (right, j))}
        if raise_dim:
            expected = {identity(domain, value) for value in expected}
        assert lifts(erased) == expected
        certify("identity" if raise_dim else "padded", domain, sigma, erased, expected)
        for value in expected:
            assert subst_ty(infer(domain, value), sigma) == infer(base, erased)
            assert subst_tm(value, sigma) == erased

    # A variable may cover a whole composite, or one or both of its subterms.
    domain, sigma, lifts = inverse_erasure(base, (right, rows[5]['d']))
    inner = (rows[5]['d'], j)
    expected = {h} | {comp2(domain, 1, a, b) for a, b in product(inner, repeat=2)}
    assert lifts(right) == expected
    assert all(subst_tm(term, sigma) == right for term in expected)
    certify("nested", domain, sigma, right, expected)
    if agda_path:
        agda_path.write_text(emitter.module(agda_path.stem, "Typed colour lifts and their literal images."))
    print("Six-seam syntax: 4 lifts of a padded 3-term, 4 of its identity, 5 nested loop lifts.")


def check_cuts():
    # d,e name the consumed and produced occurrences. x,y,w project to a
    # separator on the left, right or both; u,v include repeated letters.
    images = dict(x=('h', ''), y=('', 'h'), w=('h', 'h'), u=('h', 'dd'),
                  v=('hh', 'h'), n=('d', 'd'))
    rules = {'A': {0: ('d', '')}, 'B': {0: ('', 'e')}}
    cases = Counter()
    for length in range(4):
        for letters in product(images, repeat=length):
            fixed = ''.join(letters)
            for cut in range(length + 1):
                before = fixed[:cut] + 'd' + fixed[cut:]
                # Run the old local rules in both orders, retaining port positions.
                ends = []
                for order in ('AB', 'BA'):
                    words = {before}
                    for event in order:
                        words = {substitute((chart,), rules, (), 1)[0] for word in words
                                 for chart in lane_charts(word, (event,), rules, 0)}
                    ends.append(words)
                assert ends[0] == ends[1] == {fixed[:i] + 'e' + fixed[i:]
                                               for i in range(length + 1)}
                for after in ends[0]:
                    delta = []
                    for side in range(2):
                        def position(prefix):
                            return sum(images[c][side].count('h') for c in prefix)
                        delta.append(position(after.split('e')[0]) - position(before.split('d')[0]))
                    assert delta[0] * delta[1] >= 0
                    cases[tuple((d > 0) - (d < 0) for d in delta)] += 1
    assert set(cases) == set(product((-1, 0, 1), repeat=2)) - {(-1, 1), (1, -1)}
    print(f"{sum(cases.values())} paired gap tests, {len(cases)} realized sign pairs.")


def cubical_betti(free, feasible):
    faces = [face for face in product((-1, 0, 1), repeat=len(free))
             if feasible({axis for axis, sign in zip(free, face) if sign == 0})]
    if not faces:
        return ()
    indices = {face: i for i, face in enumerate(faces)}
    sizes, ranks = Counter(), Counter()
    pivots = {}
    for face in faces:
        dim = face.count(0)
        sizes[dim] += 1
        column = 0
        for j, sign in enumerate(face):
            if sign == 0:
                for end in (-1, 1):
                    column ^= 1 << indices[face[:j] + (end,) + face[j + 1:]]
        while column:
            pivot = column.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = column
                ranks[dim] += 1
                break
            column ^= pivots[pivot]
    return tuple(sizes[d] - ranks[d] - ranks[d + 1] for d in range(max(sizes) + 1))


def check_chart_intersections(name, data, k, feasible):
    space = Complex(*data)
    assert len(space.components) == 1
    signs = [visible(cell, k, require_visible=False) for cell in space.cells]
    checked = 0
    # 0 = unsigned, +/-1 = one facet, 2 = both facets.
    for request in product((0, -1, 1, 2), repeat=k):
        both = {i for i, s in enumerate(request) if s == 2}
        free = [i for i, s in enumerate(request) if not s]
        cells = {i for i, sign in enumerate(signs)
                 if all(not s or not x or s == x for s, x in zip(request, sign))}
        assert all(set(space.facets[i]) <= cells for i in cells)
        observed = space.betti(cells) if cells else ()
        predicted = cubical_betti(free, lambda extra: feasible(both | extra))
        while predicted and predicted[-1] == 0:
            predicted = predicted[:-1]
        assert observed == predicted, (name, request, observed, predicted)
        checked += 1
    print(f"{name}: {len(space.cells)} histories, all {checked} signed intersections verified.")


def six_seam_nerve():
    # Check actual signal precedence by sorting, independently of the cycle formula.
    edges = [(2 * i + 1, 2 * i + 2) for i in range(6)] + [(12, 0)]
    counts = Counter()
    for request in product((0, -1, 1, 2), repeat=6):
        graph = TopologicalSorter()
        for a, b in edges:
            graph.add(b, a)
        for i, s in enumerate(request):
            if s == 2:
                graph.add(2 * i + 1, 2 * i)
        try:
            tuple(graph.static_order())
            geometric = True
        except CycleError:
            geometric = False
        assert geometric == (request != (2,) * 6)
        counts['geometric'] += geometric and any(request)
        counts['literal'] += 2 not in request and any(request)
    assert counts == {'literal': 728, 'geometric': 4094}
    print("Six seams: 4096 temporal tests, 728 nonempty literal nerve faces, 4094 geometric.")


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    check_raw_lifts(parser.parse_args().agda)
    check_cuts()
    for k in (2, 3):
        check_chart_intersections(f'ring {k}', ring(k), k, lambda hidden: len(hidden) < k)
    check_chart_intersections('overlapping cycles', two_bridges(), 3, compatible)
    initial, final, rules, typed = ring(2)
    del rules['Z']
    check_chart_intersections('open chain', (('m',) + initial[1:], final[:-1] + ('m',), rules, typed),
                              2, lambda hidden: True)
    six_seam_nerve()
