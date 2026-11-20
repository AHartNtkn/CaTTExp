"""Construct signed colourings from a support cocycle and test their carried degree."""
from argparse import ArgumentParser
from functools import cache
from itertools import combinations, product
import json
from pathlib import Path

from canonical_gray_cube import build_cube
from catt import STAR, check_ctx, comp2, tdim, v
from relative_coherence_based_columns import Brackets
from relative_coherence_colour_degree import add_scaled, immutable, relative_columns
from relative_coherence_face_transfer import Transfer, lift, reduced
from relative_coherence_integral_degree import integral_test
from relative_coherence_simplex_carrier import orientation


def marginal(measure, positions, modulus):
    result = {}
    for word, coefficient in measure.items():
        key = tuple(word[i] for i in positions)
        add_scaled(result, {key: 1}, coefficient)
    return reduced(result, modulus)


def signed_colours(vertices, supports, k, cocycle, modulus=0):
    """Realize an ordered (k-1)-cocycle by proper marginals on the given supports."""
    assert k >= 2
    supports = [frozenset(s) for s in supports]
    vertices = tuple(sorted(vertices))
    assert all(s <= set(vertices) for s in supports)

    @cache
    def local(names):
        # A monotone surjection onto k blocks is specified by the k-1 cuts.
        # Its cocycle reads 1 on a face visiting every block. The coefficients
        # are triangular on faces starting with names[0].
        measure = {}
        cuts = list(combinations(range(1, len(names)), k-1))
        residues = {t: cocycle.get((names[0], *(names[i] for i in t)), 0) for t in cuts}
        for t in cuts:
            a = residues[t]
            if modulus:
                a %= modulus
            if not a:
                continue
            starts, ends = (0, *t), (*t, len(names))
            for indices in product(*(range(lo, hi) for lo, hi in zip(t, ends[1:]))):
                residues[indices] -= a
            for use in product((0, 1), repeat=k):
                word = tuple((j+1)*use[j] for j, (lo, hi) in enumerate(zip(starts, ends))
                             for _ in range(lo, hi))
                add_scaled(measure, {word: 1}, a*(-1)**use.count(0))
        measure = reduced(measure, modulus)
        # Check every face, including those which avoid names[0].
        for ix in combinations(range(len(names)), k):
            moment = sum(a*orientation(word) for word, a in marginal(measure, ix, modulus).items()
                         if set(word) == set(range(1, k+1)))
            assert not reduced({0: moment-cocycle.get(tuple(names[i] for i in ix), 0)}, modulus)
        return measure

    # Inclusion-exclusion extends compatible marginals to one finite chain on
    # all label functions. Every added coordinate gets colour zero.
    intersections = {}
    for support in supports:
        delta = {support: 1}
        for s, n in intersections.items():
            add_scaled(delta, {s & support: 1}, -n)
        add_scaled(intersections, delta, 1)
    result = {}
    for support, n in intersections.items():
        names = tuple(sorted(support))
        for word, a in local(names).items():
            labels = dict(zip(names, word))
            extension = tuple(labels.get(i, 0) for i in vertices)
            add_scaled(result, {extension: 1}, n*a)
    result = reduced(result, modulus)
    for s in supports:
        names = tuple(sorted(s))
        m = marginal(result, [vertices.index(i) for i in names], modulus)
        assert m == local(names) and all(len(set(word)) <= k for word in m)
    return result


def simplex_boundary(chain):
    out = {}
    for simplex, n in chain.items():
        for j in range(len(simplex)):
            add_scaled(out, {simplex[:j]+simplex[j+1:]: 1}, n*(-1)**j)
    return out


def support_test(supports, cycle, k, modulus=0):
    """Fill the support cycle or return a cocycle detecting it."""
    assert modulus == 0 or modulus >= 2
    assert not reduced(simplex_boundary(cycle), modulus)
    faces = {f for s in supports for f in combinations(sorted(s), k)}
    assert set(cycle) <= faces
    transpose = {f: {} for f in sorted(faces)}
    cofaces = {g for s in supports for g in combinations(sorted(s), k+1)}
    for g in sorted(cofaces):
        for i in range(k+1):
            transpose[g[:i]+g[i+1:]][g] = (-1)**i
    if modulus:
        for f in faces:
            transpose[f][f] = modulus
    result = integral_test(transpose, {f: cycle.get(f, 0) for f in transpose})
    if 'potential' in result:
        filling = {g: a for g,a in result['potential'].items() if len(g) == k+1}
        assert reduced(simplex_boundary(filling), modulus) == reduced(cycle, modulus)
        return {'potential': filling}
    if modulus:
        # The extra diagonal gives m*a=0 mod d for each returned coefficient.
        # Express the corresponding character a/d in units of 1/m.
        d = result['modulus']
        assert d and all(modulus*a % d == 0 for a in result['chain'].values())
        row = reduced({f: modulus*a//d for f,a in result['chain'].items()}, modulus)
        degree = sum(n*row.get(f, 0) for f,n in cycle.items()) % modulus
        assert degree
        return {'modulus': modulus, 'chain': row, 'degree': degree}
    return result


def typed_test(ctx, chain, k, supports=None, modulus=0):
    assert k >= 2
    check_ctx(ctx)
    assert all(0 <= i < len(ctx) and tdim(ctx[i])+1 == k for i in chain)
    vertices = range(ctx.count(STAR))
    p = Brackets(len(vertices))
    mapped = lift(ctx, vertices, p)
    calc = Transfer(p, k)
    x = {}
    for i,n in chain.items():
        add_scaled(x, {mapped[i][1]: 1}, n)
    bd = calc.boundary(x, modulus)
    if supports is None:
        supports = [calc.names(i) for i in bd]
    assert all(any(calc.names(i) <= set(s) for s in supports) for i in bd)
    cycle = {}
    for i,a in bd.items():
        add_scaled(cycle, calc.image(i), a)
    result = support_test(supports, reduced(cycle, modulus), k, modulus)
    if 'potential' in result:
        print(f'Support boundary fills with {len(result["potential"])} simplices.')
        return None
    m = result['modulus']
    mu = signed_colours(vertices, supports, k, result['chain'], m)
    q = Brackets(k+1)
    coloured = {}
    for c,n in mu.items():
        labels = lift(p.ctx, c, q)
        for i,a in x.items():
            add_scaled(coloured, {labels[i][1]: 1}, n*a)
    cols, degrees = relative_columns(q.ctx, list(range(k+1)), k)
    bd = {}
    for i,n in coloured.items():
        add_scaled(bd, cols[i], n)
    d = sum(n*degrees[i] for i,n in coloured.items())
    assert not reduced(bd,m) and reduced({0: d}, m) == reduced({0: result['degree']}, m)
    assert reduced({0: d}, m)
    print(f'{len(mu)} signed colourings, {len(reduced(coloured,m))} typed brackets survive, '
          f'degree {d % m if m else d}, modulus {m} (0 for integers).')
    return mu


def projective_plane():
    facets = [tuple(map(int, s)) for s in ('012','013','024','035','045',
                                           '125','134','145','234','235')]
    return facets, simplex_boundary({(0,1,4): 1})


def torsion_triangle():
    facets, cycle = projective_plane()
    # Exhibit an integral relation for precisely this cycle.
    for signs in product((-1, 1), repeat=len(facets)):
        if simplex_boundary(dict(zip(facets, signs))) == {f: 2*n for f, n in cycle.items()}:
            break
    else:
        raise AssertionError('missing integral double')
    # Individually proper colourings always have zero degree. Also enumerate
    # them to compare the single-colouring test with the signed construction.
    proper = 0
    for c in product(range(3), repeat=6):
        if all(len({c[i] for i in s}) <= 2 for s in facets):
            proper += 1
            assert len({c[i] for i in (0,1,4)}) <= 2
    # In the typed parameter, take the bracket (0->1->4) => (0->4).
    p = Brackets(6)
    a, b, short = (p.bracket(v(i), v(j)) for i,j in ((0,1),(1,4),(0,4)))
    path = comp2(p.ctx, 0, a, b)
    g = p.bracket(path, short)
    print(f'Missing triangle: boundary of ten signed faces is twice its cycle; '
          f'{proper} individually proper colourings, all degree zero.')
    assert typed_test(p.ctx, {g[1]: 1}, 2, facets)
    assert typed_test(p.ctx, {g[1]: 1}, 2, facets, 4)
    assert typed_test(p.ctx, {g[1]: 1}, 2, facets, 3) is None
    assert typed_test(p.ctx, {g[1]: 1}, 2, [*facets, (0,1,4)]) is None
    assert typed_test(p.ctx, {g[1]: 1}, 2)


def suspended_torsion(k):
    """Test the class on the suspended support complex, with no typing premise."""
    facets, cycle = projective_plane()
    seed = support_test(facets, cycle, 2)
    assert seed['modulus'] == 2
    witness = {f for f,n in seed['chain'].items() if n % 2}
    vertices = 6
    for _ in range(2, k):
        tips = (vertices, vertices+1)
        facets = [(*f, t) for f in facets for t in tips]
        witness = {(*f, tips[0]) for f in witness}
        cycle = {(*f, t): a * s for f,a in cycle.items() for t,s in zip(tips, (1,-1))}
        vertices += 2
    assert not simplex_boundary(cycle)
    mu = signed_colours(range(vertices), facets, k, dict.fromkeys(witness,1), 2)
    degree = sum(n * a * orientation(tuple(word[i] for i in f))
                 for word,n in mu.items() for f,a in cycle.items()
                 if {word[i] for i in f} == set(range(1,k+1)))
    assert degree % 2
    print(f'Rank {k} suspended carrier: {len(facets)} supports, {len(mu)} signed colourings, '
          f'boundary pairing {degree%2} modulo two.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, help='JSON with context, degree, chain and optional supports and modulus')
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        typed_test(immutable(data['context']), {int(i): n for i,n in data['chain'].items()},
                   data['degree'], data.get('supports'), data.get('modulus', 0))
    else:
        torsion_triangle()
        cube, _ = build_cube()
        assert typed_test(cube, {len(cube)-1: 1}, 3)
        suspended_torsion(6)
