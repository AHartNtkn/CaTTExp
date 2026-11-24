"""Compare typed planar change charts, their scalar insertions and their flat images."""

from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction
from itertools import permutations, product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_gap_braids import observe
from semistrict_surface_planar_occurrences import component_transport


def typed(order, path, arities, offsets):
    for g in order:
        i = offsets[g]
        s, t = arities[g]
        if path[i:i+len(s)] != s:
            return False
        path = path[:i]+t+path[i+len(s):]
    return True


def classes(words, rules):
    lookup = {}
    for root, transport, rigid in component_transport(set(words), rules):
        assert rigid
        for w in transport:
            lookup[w] = root
    return lookup


def keep(w, subset):
    return tuple(row for row in w if row[0] in subset)


def event_words(names, arities, offsets, flat=False):
    return {tuple((g, offsets[g]) for g in order) for order in permutations(names)
            if flat or typed(order, 'aaa', arities, offsets)}


def audit(arities, offsets, ordinary, rods, scalars):
    names = ordinary + rods + scalars
    flattened = {g: ('a'*len(s), 'a'*len(t)) for g, (s, t) in arities.items()}
    central_set, flat_set = set(ordinary+rods), set(rods+scalars)
    full = classes(event_words(names, arities, offsets), arities)
    centre = classes(event_words(ordinary+rods, arities, offsets), arities)
    flat = classes(event_words(rods+scalars, flattened, offsets, True), flattened)
    bare = classes(event_words(rods, flattened, offsets, True), flattened)
    lookup = {}
    for w, root in full.items():
        key = centre[keep(w, central_set)], flat[keep(w, flat_set)]
        previous = lookup.setdefault(key, root)
        assert root == previous
    expected = {(c, f) for c, f in product(set(centre.values()), set(flat.values()))
                if bare[keep(c, rods)] == bare[keep(f, rods)]}
    assert set(lookup) == expected and len(set(lookup.values())) == len(expected)
    return full, centre, flat, bare, lookup


def tier_extensions(centre, flat, arities, offsets, ordinary, rods, scalars):
    # For each actual central circuit insert its unary vertices at rational
    # heights into every flat weak order, including a tie of both portless points.
    flat_set = set(rods+scalars)
    count = 0
    for c in set(centre.values()):
        lanes = [[g for g, i in c if i <= k < i+len(arities[g][0])] for k in range(3)]
        for f in flat:
            events = [g for g, i in f]
            for cuts in product((0, 1), repeat=len(f)-1):
                heights = {events[0]: 0}
                for a, b, cut in zip(events, events[1:], cuts):
                    heights[b] = heights[a]+cut
                if any(any(heights[a] >= heights[b] for a,b in zip(marked, marked[1:]))
                       for lane in lanes if (marked := [g for g in lane if g in rods])):
                    continue
                def independent(a, b):
                    return (offsets[a]+len(arities[a][0]) <= offsets[b] or
                            offsets[b]+len(arities[b][0]) <= offsets[a])
                if any(heights[a] == heights[b] and not independent(a,b)
                       for i,a in enumerate(events) for b in events[i+1:]):
                    continue
                for lane in lanes:
                    stops = [-1, *[i for i,g in enumerate(lane) if g in rods], len(lane)]
                    for i,j in zip(stops, stops[1:]):
                        lo = heights[lane[i]] if i >= 0 else -1
                        hi = heights[lane[j]] if j < len(lane) else len(f)
                        for k in range(i+1,j):
                            heights[lane[k]] = lo + Fraction(k-i,j-i)*(hi-lo)
                    assert all(heights[a] < heights[b] for a,b in zip(lane,lane[1:]))
                # Break ties by the supplied planar order between retained points.
                order = sorted(heights, key=lambda g: (heights[g], events.index(g) if g in flat_set else -1))
                assert typed(order, 'aaa', arities, offsets)
                assert [g for g in order if g in flat_set] == events
                count += 1
    return count


def run():
    # A is a two-wire change from aa to ba at its spatial poles. Both
    # expansions are genuine circuits with these poles and different gate lists.
    rules = {'X':('a','b'), 'Y':('b','a'), 'U':('a','a'),
             'A':('aa','ba'), 'B':('aa','aa'), 's':('',''), 't':('','')}
    offsets = {'X':0,'Y':0,'U':1,'A':0,'B':1,'s':1,'t':1}
    # The stationary return Y restores lane 0 after the first colour change;
    # a separate late X makes the actual central scheduling order matter.
    ordinary, rods, scalars = ('X','Y','U'), ('A','B'), ('s','t')
    full, centre, flat, _, lookup = audit(rules, offsets, ordinary, rods, scalars)
    tiers = tier_extensions(centre, flat, rules, offsets, ordinary, rods, scalars)
    print('typed serial spellings', len(full), 'mixed classes', len(lookup),
          'flat tier lifts', tiers)
    # Expand a temporal cube face to a source or target, retaining the new
    # unary gates in the centre; deleting A in the flat reader must give the
    # corresponding scalar chart even after its spatial barrier disappears.
    for rod, label, replacement in [
            ('A', 'source', [('a1',0,'a','b')]),
            ('A', 'target', [('a1',0,'a','b'), ('a2',0,'b','a'),
                             ('a3',0,'a','b'), ('a4',1,'a','a')]),
            ('B', 'source', [('b1',1,'a','a')]),
            ('B', 'target', [('b2',2,'a','a'), ('b3',2,'a','a')])]:
        new_rules = dict(rules)
        for g,i,s,t in replacement:
            new_rules[g] = s,t
        remaining = set(rods + scalars) - {rod}
        flat_rules = {g: ('a'*len(s), 'a'*len(t)) for g,(s,t) in rules.items()}
        flat_faces = classes(event_words(remaining, flat_rules, offsets, True), flat_rules)
        expanded = {}
        for w in full:
            expanded[w] = tuple(row for g,i in w
                                for row in ([(u,j) for u,j,_,_ in replacement] if g == rod else [(g,i)]))
        def signature(w):
            lanes = tuple(tuple(g for g,i in w if i <= k < i+len(new_rules[g][0])) for k in range(3))
            return lanes, flat_faces[keep(w, remaining)]
        images = defaultdict(set)
        for w, new in expanded.items():
            assert typed([g for g,i in new], 'aaa', new_rules, {g:i for g,i in new})
            images[full[w]].add(signature(new))
            assert keep(new, remaining) == keep(w, remaining)
        assert all(len(v) == 1 for v in images.values())
        print(rod, label, 'expanded mixed classes', len(images),
              'distinct face classes', len({next(iter(v)) for v in images.values()}))


def single_change(output):
    ctx = (STAR, STAR, STAR, arr(STAR, v(0), v(1)), arr(STAR, v(1), v(2)))
    ctx += (arr(infer(ctx, v(3)), v(3), v(3)), arr(infer(ctx, v(4)), v(4), v(4)))
    lower = comp2(ctx, 0, v(5), v(6))
    upper = comp2(ctx, 0, comp2(ctx, 1, v(5), v(5)), v(6))
    pole = identity(ctx, identity(ctx, v(1)))
    rod_type = arr(infer(ctx, lower), lower, upper)
    scalar_type = arr(infer(ctx, pole), pole, pole)
    ctx += (rod_type, scalar_type)
    check_ctx(ctx)
    endpoints = [observe([(0,2), (1,1)], (0,1), [(0,s)]) for s in (-1,1)]
    (start, left), (end, right) = endpoints
    assert start == end and left['scalar', 1] != right['scalar', 1]
    assert all(left['wire', j] == right['wire', j] for j in range(2))
    if output:
        name = 'UnaryGapChange'
        emitter = Emitter()
        emitter.check_type('change', ctx, v(7), rod_type)
        emitter.check_type('gap', ctx, v(8), scalar_type)
        g = emitter.ctx(ctx)
        emitter.checks.append(f'typed : {g} ⊢ctx\ntyped = from-just (checkCtx {g})\n')
        (output / (name+'.agda')).write_text(emitter.module(name, __doc__))
    print('one compound change and one internal scalar: opposite exchanges have distinct gap braids')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    run()
    single_change(args.agda_dir)
