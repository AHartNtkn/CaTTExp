"""Decide directed movies on a scalar Gray base with positive named polygons.

JSON input has rules {name: [source, target]}, an initial word, and two lists
of [name, zero-based offset] steps. Use "X" for an adjacent positive crossing.
Words are lists of event labels (strings also work for single-letter labels).
"""

from argparse import ArgumentParser
from collections import Counter, deque
from fractions import Fraction
from itertools import product
import json
from pathlib import Path


def sides(name, rules):
    if name == 'X':
        return 2, 2
    a, b = rules[name]
    return len(a), len(b)


def trace(initial, reading, rules, weights=None):
    word = tuple(initial)
    mass = tuple(map(Fraction, weights if weights is not None else (1,) * len(word)))
    height = moment = Fraction(0)
    for name, i in reading:
        a, b = sides(name, rules)
        if i < 0 or i + a > len(word):
            raise ValueError('step outside the temporal word')
        prefix = sum(mass[:i])
        if name == 'X':
            moment += prefix * mass[i] * mass[i + 1]
            labels = word[i:i + 2][::-1]
            shares = mass[i:i + 2][::-1]
        else:
            source, labels = rules[name]
            if word[i:i + a] != tuple(source):
                raise ValueError('polygon source mismatch')
            height += prefix
            shares = (sum(mass[i:i + a]) / b,) * b
        word = word[:i] + tuple(labels) + word[i + a:]
        mass = mass[:i] + shares + mass[i + a:]
    return word, mass, height, moment


def crossings(indices):
    return tuple(('X', i) for i in indices)


def windows(width, rules):
    for i in range(width - 2):
        yield 'cube', crossings((i, i + 1, i)), crossings((i + 1, i, i + 1))
    for name in rules:
        a, b = sides(name, rules)
        for i in range(width - a):
            before, after = ((name, i),), ((name, i + 1),)
            yield 'left', crossings(range(i, i + a)) + before, after + crossings(range(i, i + b))
            yield 'right', before + crossings(reversed(range(i, i + b))), crossings(reversed(range(i, i + a))) + after


def moves(initial, reading, rules):
    width = len(initial)
    for k, (name, i) in enumerate(reading):
        a, b = sides(name, rules)
        if k + 1 < len(reading):
            other, j = reading[k + 1]
            c, d = sides(other, rules)
            swapped = None
            if j + c <= i:
                swapped = ((other, j), (name, i + d - c))
            elif j >= i + b:
                swapped = ((other, j + a - b), (name, i))
            if swapped is not None:
                yield 'exchange', reading[:k] + swapped + reading[k + 2:]
        for kind, lhs, rhs in windows(width, rules):
            if reading[k:k + len(lhs)] == lhs:
                yield kind, reading[:k] + rhs + reading[k + len(lhs):]
        width += b - a


def solve(initial, source, target, rules):
    if 'X' in rules or any(not a or not b for a, b in rules.values()):
        raise ValueError('use positive polygon sides and reserve X for crossings')
    src, dst = (trace(initial, r, rules) for r in (source, target))
    polygons = Counter(name for name, _ in source if name != 'X')
    if (src[:2] != dst[:2] or polygons != Counter(name for name, _ in target if name != 'X')
            or dst[2] < src[2]):
        return None
    m = max((len(rules[name][1]) for name in polygons), default=1)
    mixed_budget = int((dst[2] - src[2]) * m ** polygons.total())
    delta = max((abs(len(rules[name][0]) - len(rules[name][1])) for name in polygons), default=0)
    length_limit = len(source) + mixed_budget * delta
    queue = deque([source])
    previous = {source: None}
    while queue:
        node = queue.popleft()
        if node == target:
            witness = []
            while previous[node] is not None:
                parent, kind = previous[node]
                witness.append((kind, node))
                node = parent
            return list(reversed(witness))
        for kind, successor in moves(initial, node, rules):
            if successor in previous or len(successor) > length_limit:
                continue
            _, _, h, j = trace(initial, successor, rules)
            if h > dst[2] or (h == dst[2] and j > dst[3]):
                continue
            previous[successor] = node, kind
            queue.append(successor)
    return None


def checks():
    counts = Counter()
    # Enumerate literal readings on several labels with concurrent, overlapping
    # and repeated polygons. Verify the direction on nonuniform rational masses.
    rules = {'split': ('a', 'bc'), 'merge': ('bc', 'a'), 'tag': ('a', 'a')}
    def visit(initial, weights, word, reading, depth):
        data = trace(initial, reading, rules, weights)
        for kind, other in moves(initial, reading, rules):
            image = trace(initial, other, rules, weights)
            assert image[:2] == data[:2]
            if kind == 'exchange':
                assert data == image and ('exchange', reading) in moves(initial, other, rules)
            elif kind == 'cube':
                assert image[2] == data[2] and image[3] > data[3]
            else:
                assert image[2] > data[2]
            counts[kind] += 1
        if depth:
            for name in ('X', *rules):
                a, _ = sides(name, rules)
                for i in range(len(word) - a + 1):
                    if name != 'X' and word[i:i + a] != tuple(rules[name][0]):
                        continue
                    end, *_ = trace(word, ((name, i),), rules)
                    visit(initial, weights, end, reading + ((name, i),), depth - 1)
    for masses in product((Fraction(1, 3), Fraction(2), Fraction(5, 2)), repeat=3):
        weights = (Fraction(7, 4), *masses, Fraction(1))
        left, right = (trace('aaaaa', crossings(w), rules, weights)
                       for w in ((1, 2, 1), (2, 1, 2)))
        assert right[3] - left[3] == masses[0] * masses[1] * masses[2]
        counts['exact weighted cube increments'] += 1
    for initial in ('aba', 'abc', 'bca', 'aaaa'):
        weights = tuple(Fraction(i + 2, i + 1) for i in range(len(initial)))
        visit(initial, weights, tuple(initial), (), 3)
    # Full small-component oracle, without target height or moment pruning.
    # With a single split, crossings can grow by at most three in this sector:
    # each of its three outside input events can be passed at most once at unit mass.
    initial = 'aaaa'
    for prefix in product(range(3), repeat=2):
        start = crossings(prefix + (0, 1, 0)) + (('split', 2),)
        queue, found = deque([start]), {start}
        while queue:
            node = queue.popleft()
            for _, successor in moves(initial, node, rules):
                if successor not in found:
                    found.add(successor)
                    queue.append(successor)
        for target in found:
            assert solve(initial, start, target, rules) is not None
            assert (solve(initial, target, start, rules) is not None) == (
                trace(initial, start, rules)[2:] == trace(initial, target, rules)[2:])
            counts['directed component pairs'] += 1
    for label, count in sorted(counts.items()):
        print(f'{count:,} {label}')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces', type=Path)
    args = parser.parse_args()
    if args.faces:
        case = json.loads(args.faces.read_text())
        source, target = (tuple(map(tuple, case[k])) for k in ('source', 'target'))
        witness = solve(case['initial'], source, target, case['rules'])
        print(json.dumps({'reachable': witness is not None, 'moves': witness}))
    else:
        checks()
