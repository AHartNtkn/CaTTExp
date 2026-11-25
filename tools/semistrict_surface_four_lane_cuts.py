"""Decide rank-three, degree-six named binary cut words on four labelled lanes.

JSON events are pairs of lane numbers (0..3). Alternatively supply a signed
scalar movie under "movie". Each letter gives "after" (fired event indices),
"pair" (oriented lane names), and an optional signed integral "multiple".
"""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path

from semistrict_surface_scalar_leaves import read_edges
from semistrict_surface_spatial_antichain import add, bracket, inverse

LANES = frozenset(range(4))
PAIRS = list(combinations(range(4), 2))


def stage_list(events):
    stages = []
    for i, pair in enumerate(events):
        side = frozenset(pair)
        if len(side) != 2 or not side <= LANES:
            raise ValueError('a binary site needs two distinct lanes from 0..3')
        frame = tuple(sorted((tuple(sorted(side)), tuple(sorted(LANES - side)))))
        if not stages or frame != stages[-1][0]:
            stages.append((frame, ([], [])))
        stages[-1][1][frame.index(tuple(sorted(side)))].append(i)
    return stages or [(((0, 1), (2, 3)), ([], []))]


def movie_events(movie):
    initial, _, _, _, steps = read_edges(movie)
    if len(initial) != 4:
        raise ValueError('expected four initial strands')
    lane = dict(zip(initial, range(4)))
    events = []
    for _, ins, outs, _ in steps:
        if len(ins) != 2 or len(outs) != 2:
            raise ValueError('expected binary sites')
        pair = [lane[w] for w in ins]
        events.append(pair)
        lane.update(zip(outs, pair))
    return events


def commute(a, b):
    return (a[0] - b[0]) * (a[1] - b[1]) >= 0


def append_power(word, point, power):
    # Move the new syllable left across commuting letters until it can
    # combine with the same vertex, or until a noncommuting letter blocks it.
    if not power:
        return
    for i in reversed(range(len(word))):
        p, n = word[i]
        if p == point:
            if n + power:
                word[i] = (p, n + power)
            else:
                word.pop(i)
            return
        if not commute(p, point):
            break
    word.append((point, power))


def reading(frame, columns, word):
    centre, mixed = Counter(), []
    for after, pair, power in word:
        t = [len(after.intersection(col)) for col in columns]
        a, b = pair
        if (a in frame[1]) and (b in frame[0]):
            a, b, power = b, a, -power
        side = int(a in frame[1])
        if b in frame[side]:
            add(centre, ('within', side, t[side]), power if a < b else -power)
            continue
        # At a cut the first wire is the local basis v; the second is u-v,
        # where u is the sum continued across all sites of that column.
        def modes(i, lane):
            return [(t[i], 1)] if lane == frame[i][0] else [(-1, 1), (t[i], -1)]
        for i, sign_a in modes(0, a):
            for j, sign_b in modes(1, b):
                amount = power * sign_a * sign_b
                if min(i, j) < 0:
                    add(centre, ('cross', i, j), amount)
                else:
                    append_power(mixed, (i, j), amount)
    return dict(central=sorted(centre.items()), grid=mixed)


def solve(data):
    events = movie_events(data['movie']) if 'movie' in data else data['events']
    stages = stage_list(events)
    word = []
    for entry in data['word']:
        after, pair = frozenset(entry['after']), tuple(entry['pair'])
        if not after <= set(range(len(events))) or len(pair) != 2 or len(set(pair) & LANES) != 2:
            raise ValueError('invalid event index or oriented pair')
        power = entry.get('multiple', 1)
        if type(power) is not int:
            raise ValueError('expected integral multiplicity')
        for j in after:
            if any(i not in after and set(events[i]).intersection(events[j]) for i in range(j)):
                raise ValueError('fired events do not form a cut')
        word.append((after, pair, power))
    reports = [reading(frame, columns, word) for frame, columns in stages]
    return dict(raw_fills=all(not (v['central'] or v['grid']) for v in reports), stages=reports)


def seed(d):
    if d < 1:
        raise ValueError('each column needs a positive length')

    def letter(i, j):
        return [dict(after=[*range(i), *range(d, d + j)], pair=[0, 2])]
    # Each difference collapses to zero across its designated event.
    # The antidiagonal projection of that difference is a free generator.
    left = [letter(i, d - i) + inverse(letter(i + 1, d - i)) for i in range(d)]
    right = [letter(d - j, j) + inverse(letter(d - j, j + 1)) for j in range(d)]
    # Start with distinct antidiagonal generators. The running commutator
    # then has zero abelianization and cannot commute with a basis letter.
    word = bracket(left[0], right[0])
    for leaf in left[1:] + right[1:]:
        word = bracket(word, leaf)
    return dict(events=[(0, 1)] * d + [(2, 3)] * d, word=word)


def contract(data, site):
    def shift(after):
        return [i - int(i > site) for i in after if i != site]
    return dict(events=data['events'][:site] + data['events'][site + 1:],
                word=[dict(entry, after=shift(entry['after'])) for entry in data['word']])


def audit():
    words = 0
    for n in range(6):
        for events in product(PAIRS, repeat=n):
            predecessors = []
            for j, pair in enumerate(events):
                pred = set()
                for i, other in enumerate(events[:j]):
                    if set(pair) & set(other):
                        pred |= {i} | predecessors[i]
                predecessors.append(pred)
            earlier = set()
            for _, columns in stage_list(events):
                for col in columns:
                    for k, j in enumerate(col):
                        assert predecessors[j] == earlier.union(col[:k])
                earlier.update(*columns)
            words += 1
    transfers = 0
    events = [(0, 1), (2, 3), (1, 2), (0, 3), (1, 2), (2, 3)]
    for bits in product((False, True), repeat=len(events)):
        after = [i for i, b in enumerate(bits) if b]
        if any(i not in after and set(events[i]) & set(events[j]) for j in after for i in range(j)):
            continue
        for j, ports in enumerate(events):
            if j in after or any(i not in after and set(events[i]) & set(ports) for i in range(j)):
                continue
            stationary = sorted(LANES.difference(ports))
            for pairs in [[stationary], *[[(i, p) for p in ports] for i in stationary]]:
                below = [dict(after=after, pair=pair) for pair in pairs]
                above = [dict(after=[*after, j], pair=pair) for pair in pairs]
                assert solve(dict(events=events, word=below + inverse(above)))['raw_fills']
                transfers += 1
    from semistrict_surface_scalar_leaves import sample
    movie = sample(['a'] * 4, [(0, 2, 2), (2, 2, 2), (1, 2, 2)], [[], [-2]])
    assert movie_events(movie) == [[0, 1], [2, 3], [2, 1]]
    # A seam sphere is the same class at both adjacent stage endpoints.
    both = [dict(after=[0, 1], pair=[0, 3])]
    assert not solve(dict(movie=movie, word=both))['raw_fills']
    print(f'{words} incidence orders agree with independent dependence closure; '
          f'{transfers} signed marker and spectator transfers pass on a three-stage history.')
    for d in range(1, 5):
        data = seed(d)
        result = solve(data)
        assert not result['raw_fills']
        free = []
        for (i, j), exponent in result['stages'][0]['grid']:
            if i + j == d:
                if free and free[-1][0] == i:
                    exponent += free.pop()[1]
                if exponent:
                    free.append((i, exponent))
        assert free
        for j in range(2 * d):
            assert solve(contract(data, j))['raw_fills']
        print(f'{2*d} events: {len(data["word"])} signed spheres, '
              f'{len(free)} reduced antidiagonal syllables, every single contraction fills.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, nargs='?')
    parser.add_argument('--seed', type=int)
    args = parser.parse_args()
    if args.seed is not None:
        print(json.dumps(seed(args.seed)))
    elif args.input:
        print(json.dumps(solve(json.loads(args.input.read_text()))))
    else:
        audit()
