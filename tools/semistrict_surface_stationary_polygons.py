"""Decide mutual degree-four surface reachability by positive braid cuts."""
from argparse import ArgumentParser
from collections import deque
from itertools import product
import json
from pathlib import Path

from semistrict_surface_joint_labels import positive_normal
from semistrict_surface_polygon_grades import resolution
from semistrict_surface_serial_polygons import frames
from semistrict_surface_signed_width_two import Movies, Presentation, Rule


def spelling(factors):
    """A reduced adjacent-transposition spelling of each permutation braid."""
    result = []
    for perm in factors:
        order = list(range(len(perm)))
        for i, name in enumerate(perm):
            j = order.index(name, i)
            for k in range(j, i, -1):
                result.append(k)
                order[k-1], order[k] = order[k], order[k-1]
    return result


def coset(width, prefix, start, end):
    # Reverse the word so that right parabolic divisors become initial atoms.
    factors = positive_normal(width, reversed(prefix))
    while factors:
        first = list(factors[0])
        where = [0]*width
        for pos, name in enumerate(first):
            where[name] = pos
        g = next((i for i in range(width-1) if (i+1 < start or i >= end)
                  and where[i] > where[i+1]), None)
        if g is None:
            break
        a, b = where[g], where[g+1]
        first[a], first[b] = first[b], first[a]
        factors = positive_normal(width, spelling((first, *factors[1:])))
    return factors


def decide(model, source, first, second):
    if model.attachments:
        raise ValueError('stationary polygon comparison requires a positive 3-computad')
    u, end = model.parse(source, first)
    v, other = model.parse(source, second)
    if end != other:
        raise ValueError('expected parallel readings')
    arities = [(len(r.source), len(r.target)) for r in model.pres.rules]
    resolved = resolution(source, (first, second), arities, 'swap')
    def reject(reason):
        return dict(surface=False, mutual=False, obstruction=reason)
    if resolved is None:
        return reject('named incidence')
    widths, flow, graph, readings = resolved
    width = sum(widths)
    def inspect(reading, records):
        word, placements = frames(source, graph, flow, reading, records)
        cuts = {}
        for p, (before, partition, length) in placements.items():
            i = before[2]
            offset = sum(size for _, size in partition[:i])
            cuts[p] = (offset, offset + partition[i][1], length)
        return word, cuts
    a, x = inspect(readings[0], u)
    b, y = inspect(readings[1], v)
    if any(y[p][0] < x[p][0] for p in x):
        return reject('a polygon loses temporal mass')
    if positive_normal(width, a) != positive_normal(width, b):
        return reject('different total unit braids')
    if any(y[p][0] > x[p][0] for p in x):
        return dict(surface=None, mutual=False, reason='positive temporal gain',
                    temporal_gain=sum(y[p][0]-x[p][0] for p in x))
    for p, (start, stop, length) in x.items():
        if coset(width, a[:length], start, stop) != coset(width, b[:y[p][2]], start, stop):
            return reject('different passive polygon cuts')
    order = list(x)
    position = {p:i for i, p in enumerate(y)}
    for i, p in enumerate(order):
        for q in order[i+1:]:
            if position[q] < position[p] and max(x[p][0], x[q][0]) < min(x[p][1], x[q][1]):
                return reject('inverted polygons occupy overlapping unit intervals')
    return dict(surface=True, mutual=True, resolved_width=width)


def reversible_class(model, source, word):
    """Independent exhaustion on the original positioned positive readings."""
    from semistrict_surface_raw_movie_graph import read, steps
    found = {word}
    todo = deque([word])
    while todo:
        w = todo.popleft()
        _, windows = read(model, source, w)
        nexts = []
        for j in range(len(w)-1):
            (p, i), (q, k) = w[j:j+2]
            a, b = windows[j]
            c, d = windows[j+1]
            if k+c <= i:
                nexts.append(w[:j]+((q,k),(p,i+d-c))+w[j+2:])
            elif k >= i+b:
                nexts.append(w[:j]+((q,k+a-b),(p,i))+w[j+2:])
        for j, (p, k) in enumerate(w[:-2]):
            if p == 'swap':
                for z in (k-1,k+1):
                    if z >= 0 and w[j:j+3] == steps((k,z,k)):
                        nexts.append(w[:j]+steps((z,k,z))+w[j+3:])
        for v in nexts:
            if v not in found:
                model.parse(source, v)
                found.add(v)
                todo.append(v)
    return found


def checks():
    from collections import defaultdict
    from random import Random
    from semistrict_surface_raw_movie_graph import raw_compare, steps
    s = ((0, 's'),)
    bubble = ((0, 'b'), (0, 'd'))
    model = Movies(Presentation({'f': (0, 0)}, {'s': ('', ''), 'b': ('', 'f'), 'd': ('f', '')},
                                [Rule('', s, bubble), Rule('', bubble, s)], {'s': 0, 'b': 0}), '')
    source = s*3
    x = steps((1, 0, 1)) + ((0, 0), (0, 2))
    y = steps((0, 1, 0)) + ((0, 1), (0, 0))
    assert decide(model, source, x, y)['mutual'] and not raw_compare(model, source, x, y)['raw']
    assert y in reversible_class(model, source, x)
    rng = Random(8)
    grouped = defaultdict(list)
    for _ in range(1050):
        w, h = (), source
        for _ in range(rng.randrange(3, 8)):
            choices = [(('swap', i), model.swap(h, i, True)) for i in range(len(h)-1)]
            choices.extend(((p, i), result[0]) for i in range(len(h)) for p in (0, 1)
                           if (result := model.named(h, p, i)) is not None)
            action, h = rng.choice([(op, t) for op, t in choices if t is not None])
            w += (action,)
        grouped[h, len(w)].append(w)
    comparisons = positive = 0
    for group in grouped.values():
        for w in group[::4]:
            component = reversible_class(model, source, w)
            for v in [*rng.sample(group, min(3,len(group))), *sorted(component, key=repr)[::17]]:
                assert decide(model, source, w, v)['mutual'] == (v in component)
                positive += v in component
                comparisons += 1
    # Check the parabolic-tail algorithm against the faithful Artin action
    # of relative braids, independently via packet meridians and prefix products.
    from semistrict_surface_packet_meetings import cut
    from semistrict_surface_scalar_meetings import hurwitz
    seen, cuts = {}, 0
    for n in (3,4):
        for length in range(5):
            for w in product(range(1,n), repeat=length):
                frame = tuple((j+1,) for j in range(n))
                for g in w:
                    frame = hurwitz(frame, g-1, True)
                assert positive_normal(n,spelling(positive_normal(n,w))) == positive_normal(n,w)
                for i in range(n):
                    for j in range(i+1,n+1):
                        c = coset(n,w,i,j)
                        k = cut(frame,i,j-i)
                        for left, right in ((('c',c), k), (('k',k), c)):
                            assert seen.setdefault((n,i,j,left),right) == right
                        cuts += 1
    return dict(placed_comparisons=comparisons, mutually_reachable=positive, packet_cut_checks=cuts,
                split_bubble_reverse_cube=True)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--query', type=Path)
    args = parser.parse_args()
    if args.query:
        q = json.loads(args.query.read_text())
        if q.get('attachments'):
            raise ValueError('expected a 3-computad')
        rules = [Rule(r['path'], tuple(map(tuple, r['source'])), tuple(map(tuple, r['target'])))
                 for r in q['rules']]
        model = Movies(Presentation(q['edges'], q['marks'], rules, q.get('mark_roots')), q['start'])
        source = tuple(map(tuple, q['source']))
        model.pres.walk(model.start, source, q.get('vertex'))
        answer = decide(model, source, q['first'], q['second'])
    else:
        answer = checks()
    print(json.dumps(answer))
