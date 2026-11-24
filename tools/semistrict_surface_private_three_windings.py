"""Decide old private degree-four surface comparisons on three positioned events.

--faces FILE uses the positioned private movie format of Response 134.
"""
from argparse import ArgumentParser
from collections import deque
from dataclasses import dataclass
from itertools import combinations
from math import lcm
import json
from pathlib import Path

from semistrict_surface_group_encoding import matrix
from semistrict_surface_history_group import exchange
from semistrict_surface_private_winding import solve as winding


def multiply(m, n):
    a, b, c, d = m
    u, v, w, x = n
    return a*u+b*w, a*v+b*x, c*u+d*w, c*v+d*x


def power(generator, exponent):
    return (1, exponent, 0, 1) if generator == 1 else (1, 0, -exponent, 1)


@dataclass(frozen=True)
class Curve:
    intercept: tuple
    slope: tuple
    period: int
    domain: frozenset

    def point(self, k):
        if (k % self.period if self.period else k) in self.domain:
            m = tuple(a+k*b for a, b in zip(self.intercept, self.slope))
            return k, min(m, tuple(-x for x in m))
        return None


def orbit(h, generator, ports):
    """Integer powers of one partially defined bijection at a named history."""
    states = {0: h}
    for direction in (1, -1):
        k, here = 0, h
        while (here := exchange(here, direction*generator, ports)) is not None:
            k += direction
            if here == h:
                return k, states
            states[k] = here
    return 0, states


def families(anchor, ports, passive, suffix=0):
    path, h, _ = anchor
    a = matrix(path)
    if not passive:
        return Curve(a, (0,)*4, 0, frozenset([len(path)]))
    period, histories = orbit(h, passive, ports)
    shift = len(path) + (1 if suffix > 0 else -1 if suffix < 0 else 0)
    allowed = [p+shift for p, state in histories.items()
               if not suffix or exchange(state, suffix, ports) is not None]
    domain = frozenset(k % period if period else k for k in allowed)
    b = matrix((suffix,)) if suffix else (1, 0, 0, 1)
    def at(k):
        return multiply(multiply(a, power(passive, k-shift)), b)
    zero = at(0)
    return Curve(zero, tuple(v-u for u, v in zip(zero, at(1))), period, domain)


def samples(curves):
    special = {k for c in curves if not c.period for k in c.domain}
    period = lcm(*(c.period for c in curves if c.period))
    for a, b in combinations(curves, 2):
        for sign in (-1, 1):
            offsets = [x-sign*y for x, y in zip(a.intercept, b.intercept)]
            slopes = [x-sign*y for x, y in zip(a.slope, b.slope)]
            for u, v in zip(offsets, slopes):
                if v:
                    k, r = divmod(-u, v)
                    if not r and all(x+k*y == 0 for x, y in zip(offsets, slopes)):
                        special.add(k)
                    break
    representatives = set(special)
    for residue in range(period):
        k = residue
        while k in special:
            k += period
        representatives.add(k)
    return {c: frozenset(p for k in representatives if (p := c.point(k)) is not None)
            for c in curves}


def anchors(h, ports, steps):
    path, marks, counts = [], {}, [0]*len(h)
    for op, i in steps:
        if op == 'X':
            path.append(i+1)
            h = exchange(h, i+1, ports)
        else:
            e = h[i][1]
            marks[e, counts[e]] = tuple(path), h, i
            counts[e] += 1
    return marks, (len(path), matrix(path))


def solve(data):
    base = winding(data)
    n = len(data['history'])
    if n < 3 or base['obstruction']:
        return base
    if n != 3:
        raise ValueError('expected at most three temporal events')
    h = tuple((p, e) for e, (p, _) in enumerate(data['history']))
    ports = {e: data['marks'][label] for e, (_, label) in enumerate(data['history'])}
    source, beta = anchors(h, ports, data['source'])
    target, other = anchors(h, ports, data['target'])
    if beta != other:
        return dict(surface_filler=False, obstruction='total braid')
    stages, all_curves = {}, set()
    for m, a in source.items():
        b = target[m]
        i, j = a[2], b[2]
        assert i <= j
        def family(anchor, g=0, end=0):
            c = families(anchor, ports, g, end)
            all_curves.add(c)
            return c
        if i == j:
            c = family(a, (2, 0, 1)[i])
            wanted = len(b[0]), matrix(b[0])
            if c.point(wanted[0]) != wanted:
                return dict(surface_filler=False, obstruction='stationary checkpoint')
            stages[m] = {i: [c]}
            continue
        s = stages[m] = {}
        if i == 0:
            s[0] = [family(a, 2)]
        if j == 2:
            s[2] = [family(b, 1)]
        s[1] = ([family(a)] if i == 1 else [family(a, 2, t) for t in (1, -1)],
                [family(b)] if j == 1 else [family(b, 1, t) for t in (2, -2)])
    table = samples(all_curves)
    sites, starts, ends, advances = {}, {}, {}, {}
    for m, s in stages.items():
        previous = []
        for i in sorted(s):
            if i == 1 and len(s) > 1:
                left, right = s[i]
                middle = frozenset.union(*(table[c] for c in left)) & frozenset.union(*(table[c] for c in right))
                if not middle:
                    return dict(surface_filler=False, obstruction='no common middle checkpoint')
                sets = [frozenset([p]) for p in sorted(middle)]
            else:
                sets = [table[s[i][0]]]
            keys = [(m, i, k) for k in range(len(sets))]
            sites.update(zip(keys, sets))
            for key in previous:
                advances[key] = keys
            if not previous:
                assert len(keys) == 1
                starts[m] = keys[0]
            previous = keys
        assert len(previous) == 1
        ends[m] = previous[0]
    first = tuple(starts[m] for m in source)
    last = tuple(ends[m] for m in target)
    def steps(word):
        for k, x in enumerate(word):
            for nxt in advances.get(x, ()):
                yield word[:k]+(nxt,)+word[k+1:]
            if k+1 < len(word):
                y = word[k+1]
                if x[0][0] != y[0][0] and x[1] != y[1] and not sites[x].isdisjoint(sites[y]):
                    yield word[:k]+(y, x)+word[k+2:]
    queue, seen = deque([first]), {first}
    while queue:
        w = queue.popleft()
        if w == last:
            return dict(surface_filler=True, states_seen=len(seen))
        for q in steps(w):
            if q not in seen:
                seen.add(q)
                queue.append(q)
    return dict(surface_filler=False, obstruction='update order', states_seen=len(seen))


def checks():
    from semistrict_surface_acyclic_private_movies import Traces
    from semistrict_surface_private_simple_braid import read
    from semistrict_surface_private_divisor_movies import Divisors
    from semistrict_surface_private_histories import closure
    from semistrict_surface_signed_private_model import Ball
    from semistrict_surface_single_power import spellings

    base = dict(edges={}, initial=[], start_vertex=0, scalar_at={'s': 0}, marks={'s': [[], []]},
                higher=[{'p': ['s', 's']}], history=((0, 's'),)*3)
    h = base['history']
    chart = Traces(base['marks'], base['higher'][0], {})
    beta = (1, 2, 1)*2
    interval = Divisors(h, base['marks'], beta)
    ball = Ball(h, base['marks'], 6)
    records = {}
    for pure in spellings(beta):
        for a in (0, 2, 4, 6):
            for b in {a, 6}:
                for i in range(3):
                    for j in range(3):
                        movie = [('X', g-1) for g in pure]
                        movie.insert(b, ('p', j))
                        movie.insert(a, ('p', i))
                        trace = read(chart, h, movie)[2]
                        w = ball.word(movie, trace)
                        records[w] = (movie, trace, interval.word(movie, trace))
    total = double = positive = 0
    for w, (source, trace, inside) in records.items():
        reach = closure(w, lambda q: (v for _, v in ball.steps(q)))
        div = closure(inside, lambda q: (v for _, v in interval.steps(q)))
        for z, (target, other, goal) in records.items():
            upper = {m[:2]: m[2] for m in other}
            if any((e, j) not in upper or s & ~upper[e, j] for e, j, s in trace):
                continue
            value = solve(dict(base, source=source, target=target))['surface_filler']
            assert value == (z in reach) == (goal in div), (source, target, value)
            total += 1
            if any((upper[e, j]^s).bit_count() == 2 for e, j, s in trace):
                double += 1
                positive += value

    named = ((0, 0), (0, 1), (0, 2))
    ports = {e: ([], []) for e in range(3)}
    after = exchange(exchange(named, 1, ports), 2, ports)
    left = families(((), named, 0), ports, 2, 1)
    right = families(((1, 2), after, 2), ports, 1, -2)
    for k in range(-100, 101):
        assert left.point(k) == right.point(k) is not None
    # Only the positive crossing of independent occupied sites can start here.
    # Each passive orbit has a genuine endpoint.
    ordered = ((2, 0), (1, 1), (0, 2))
    occupied = {e: (['x'], ['x']) for e in range(3)}
    for g in (1, 2):
        period, states = orbit(ordered, g, occupied)
        assert period == 0 and set(states) == {0, 1}
    spatial = dict(base, edges={'x': [0, 0]}, initial=['x']*3, scalar_at={},
                   marks={'s': [['x'], ['x']]}, history=[(p, 's') for p, _ in ordered])
    source = [('p', 0), ('X', 0), ('X', 1)]
    target = [('X', 0), ('X', 1), ('p', 2)]
    assert solve(dict(spatial, source=source, target=target))['surface_filler']
    assert not solve(dict(spatial, source=target, target=source))['surface_filler']
    from semistrict_surface_private_braid_windows import factor, join
    from semistrict_surface_private_heap_order import solve as raw
    def crosses(word):
        return [('X', g-1) for g in word]
    a, b = (1,), (2, 1, 1, 1, 2, 2)
    common = join(a, b)
    holes = dict(base, source=crosses(a)+[('p', 0)]+crosses(factor(a, common)),
                 target=crosses(b)+[('p', 2)]+crosses(factor(b, common)))
    assert winding(holes)['obstruction'] is None
    assert solve(holes)['obstruction'] == 'no common middle checkpoint'
    failure = dict(base, source=[('p', 0)]+crosses((2, 1, 2, 1, 2, 1)),
                   target=crosses((1, 2, 1))+[('p', 2)]+crosses((1, 2, 1)))
    assert solve(failure)['surface_filler'] and not raw(failure)['raw_filler']
    print(f'{total} full-twist comparisons agree with signed-ball and positive-divisor search; '
          f'{double} involve two gains ({positive} inhabited). '
          'Infinite middle families and bounded occupied-site orbits checked.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces', type=Path)
    args = parser.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()))))
    else:
        checks()
