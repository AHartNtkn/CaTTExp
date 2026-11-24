"""Expand a positive Gray polygon movie to a scalar crossing word and bound its steps."""

from argparse import ArgumentParser
from collections import Counter
from itertools import product
import json
from math import prod
from pathlib import Path

from semistrict_surface_crossing_prefixes import forced_counts, word_face
from semistrict_surface_polygon_grades import resolution
from semistrict_surface_positive_movies import crossings, moves, trace, windows


def rectangle(offset, left, right):
    """Exchange adjacent temporal blocks, bringing the right block to the front."""
    return tuple(offset + i + j for j in range(right) for i in reversed(range(left)))


def cable(initial, reading, rules, weights):
    trace(initial, reading, rules)
    widths = list(weights)
    if len(widths) != len(initial) or any(w < 2 or w % 2 for w in widths):
        raise ValueError('supply one positive even width per input')
    letters = []
    for name, i in reading:
        offset = sum(widths[:i])
        if name == 'X':
            a, b = widths[i:i + 2]
            letters.extend(rectangle(offset, a, b))
            widths[i:i + 2] = b, a
        else:
            a, b = map(len, rules[name])
            total = sum(widths[i:i + a])
            if total % (2 * b):
                raise ValueError('cannot split into even integral cables')
            letters.append(offset)
            widths[i:i + a] = [total // b] * b
    return tuple(letters), tuple(widths)


def movie_bound(initial, source, target, rules, weights=None):
    if 'X' in rules or any(not a or not b for a, b in rules.values()):
        raise ValueError('reserve X for crossings and use nonempty polygon sides')

    def labels(reading):
        return Counter(name for name, _ in reading if name != 'X')
    if labels(source) != labels(target):
        return None
    if weights is None:
        arities = {n:(len(l),len(r)) for n,(l,r) in rules.items()}
        resolved = resolution(initial,(source,target),arities,'X')
        if resolved is None:
            return None
        input_widths,flow,graph,readings = resolved
        weights = [2*w for w in input_widths]
        def expand(reading):
            widths,letters = list(weights),[]
            for i,p in reading:
                offset = sum(widths[:i])
                if p is None:
                    x,y = widths[i:i+2]
                    letters.extend(rectangle(offset,x,y))
                    widths[i:i+2] = y,x
                else:
                    _,ins,outs = graph[p]
                    letters.append(offset)
                    widths[i:i+len(ins)] = [2*flow[e] for e in outs]
            return tuple(letters),tuple(widths)
        (first,a),(last,b) = map(expand,readings)
    else:
        first,a = cable(initial,source,rules,weights)
        last,b = cable(initial,target,rules,weights)
    if a != b or trace(initial, source, rules)[0] != trace(initial, target, rules)[0]:
        return None
    table = forced_counts(sum(weights), 3, word_face(first), word_face(last))
    if table is None:
        return None
    return sum(sum(q.values()) for q in table.values())


def top_count(factors):
    """Count positive cubes in the image of a tensor chart; factors are its
    ordered decorated intervals (one width) and polygons (a pair of width lists).
    """
    counts = []
    for factor in factors:
        if isinstance(factor, int):
            if factor < 2 or factor % 2:
                raise ValueError('bad interval width')
            counts.append(factor)
        else:
            u, v = factor
            if (not u or not v or sum(u) != sum(v)
                    or any(w < 2 or w % 2 for w in (*u, *v))):
                raise ValueError('bad lifted polygon')
            counts.append(1)
    return prod(counts)


def checks():
    totals = Counter()
    for a, b in product(range(1, 4), repeat=2):
        rules = {'P': ('a' * a, 'a' * b)}
        for kind, src, dst in windows(a + 1, rules):
            if kind == 'cube':
                continue
            initial = 'a' * (a + 1)
            widths = tuple(2 * b * (1 + (i % 2)) for i in range(a + 1))
            lone = widths[0 if kind == 'left' else -1]
            assert movie_bound(initial, src, dst, rules, widths) == lone
            assert movie_bound(initial, dst, src, rules, widths) is None
            totals['signed prism counts'] += 2
    for widths in product((2, 4), repeat=3):
        src, dst = crossings((0, 1, 0)), crossings((1, 0, 1))
        assert movie_bound('aaa', src, dst, {}, widths) == prod(widths)
        assert movie_bound('aaa', dst, src, {}, widths) is None
        totals['signed triple counts'] += 2

    rules = {'P': ('a', 'aa'), 'Q': ('aa', 'a')}
    reading = (('P', 0), ('Q', 2), ('X', 1), ('P', 0))
    # Strict interchange moves a length-changing box across another box.
    for kind, other in moves('aaa', reading, rules):
        if kind == 'exchange':
            assert movie_bound('aaa', reading, other, rules) == 0
            totals['expanded strict exchanges'] += 1
    # The incidence resolution is invariant across two successive mixed moves.
    start = (('P', 0),) + crossings((1, 0)) + (('P', 0),) + crossings((1, 0))
    first = next(other for kind, other in moves('aa', start, rules) if kind == 'right')
    last = next(other for kind, other in moves('aa', first, rules)
                if kind == 'right' and other != start)
    v = movie_bound('aa', start, first, rules)
    w = movie_bound('aa', first, last, rules)
    assert v > 0 and w > 0 and movie_bound('aa', start, last, rules) == v + w
    totals['successive mixed steps'] += 2

    # Independent cellular check. In one spatial column the chosen polygon
    # has one active square and padded idle strands. For interval cables every
    # strand has one active edge. Product cells choose one active cell per axis.
    for length in range(1, 6):
        for factors in product((2, 4, ((6,), (2, 2, 2)), ((2, 4), (6,)), ((6,), (2,4))), repeat=length):
            choices = [range(f) if isinstance(f, int) else (0,) for f in factors]
            assert sum(1 for _ in product(*choices)) == top_count(factors)
            totals['positive tensor top chains'] += 1
    for k, n in sorted(totals.items()):
        print(f'{n:,} {k}')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces', type=Path, help='same scalar movie JSON as Response 101')
    args = parser.parse_args()
    if args.faces:
        data = json.loads(args.faces.read_text())
        src, dst = (tuple(map(tuple, data[k])) for k in ('source', 'target'))
        answer = movie_bound(data['initial'], src, dst, data['rules'])
        print(json.dumps({'scalar_cube_budget': answer}))
    else:
        checks()
