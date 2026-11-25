"""Decide integral based two-cycles of two scalars in a gap with moving rods."""

from argparse import ArgumentParser
from collections import Counter
from itertools import permutations, product
import json
from pathlib import Path

from semistrict_surface_gap_braids import observe
from semistrict_surface_gap_linking import push
from semistrict_surface_gap_spheres import dimension, members, partitions, restrict, splits
from semistrict_surface_history_group import inv, reduced


def anchor(cell):
    return tuple(i for chart in cell for i in members(chart))


def chart_moves(chart, new):
    order = members(chart)
    height = {i: k for k, r in enumerate(chart) for i in r}
    for final, b in enumerate(new):
        j = order.index(b)
        while j > final:
            a = order[j-1]
            sign = (height[b] > height[a]) - (height[b] < height[a])
            # Names 0,1 are scalars; their two temporal exchanges coincide.
            yield j-1, 0 if a < 2 and b < 2 else sign
            order[j-1:j+1] = b, a
            j -= 1


def facet_sign(left, right):
    inversions = sum(a > b for a in left for b in right)
    return (-1)**(len(left) + inversions)


def boundary(cell):
    temporal = sum(len(members(c)) - 1 for c in cell)
    offset = before = 0
    for k, chart in enumerate(cell):
        for h, row in enumerate(chart):
            for left, right in splits(row):
                new = chart[:h] + (left, right) + chart[h+1:]
                yield cell[:k] + (new,) + cell[k+1:], (), (-1)**temporal * facet_sign(left, right)
        block = members(chart)
        for left, right in splits(block):
            face = cell[:k] + (restrict(chart, left), restrict(chart, right)) + cell[k+1:]
            if dimension(face) == dimension(cell)-1:
                route = tuple((i+offset, s) for i, s in chart_moves(chart, left+right))
                yield face, route, (-1)**before * facet_sign(left, right)
        before += len(block)-1
        offset += len(block)


def advance(state, moves):
    """Rods carry free-group meridians; scalars carry left sheet translations."""
    state = list(state)
    for i, sign in moves:
        if not 0 <= i < len(state)-1:
            raise ValueError('move position out of range')
        (a, u), (b, v) = state[i:i+2]
        if sign not in ((0,) if max(a, b) < 2 else (-1, 1)):
            raise ValueError('rods require signed crossings; scalar/scalar sign is zero')
        if sign > 0 and a >= 2:
            v = reduced(u + v + (inv(u) if b >= 2 else ()))
        elif sign < 0 and b >= 2:
            u = reduced(inv(v) + u + (v if a >= 2 else ()))
        state[i:i+2] = (b, v), (a, u)
    return tuple(state)


def initial(order):
    return tuple((i, (i-1,) if i >= 2 else ()) for i in order)


def value(cell, state):
    if any(chart == ((0, 1),) for chart in cell):
        words = dict(state)
        return reduced(inv(words[1]) + words[0])
    return None


def validate(cell, n):
    names = [i for chart in cell for row in chart for i in row]
    if (not cell or any(not c or any(not row for row in c) for c in cell)
            or any(type(i) is not int for i in names) or sorted(names) != list(range(n))
            or any(len(row) > 1 and set(row) != {0, 1} for c in cell for row in c)):
        raise ValueError('expected nonempty temporal blocks and planar rows using each name exactly once')


def sum_chain(n, chain):
    slots = [(1, 1)]*2 + [(0, 2)]*(n-2)
    order = tuple(range(n))
    start = initial(order)
    differential = Counter()
    answer = Counter()
    for cell, path, coefficient in chain:
        validate(cell, n)
        if type(coefficient) is not int or dimension(cell) != 2:
            raise ValueError('expected an oriented two-cell with integer multiplicity')
        state = advance(start, path)
        if tuple(i for i, _ in state) != anchor(cell):
            raise ValueError('path does not reach the canonical cell vertex')
        for face, moves, sign in boundary(cell):
            end, actions = observe(slots, order, path + moves)
            assert end == anchor(face)
            differential[face, tuple(actions.values())] += coefficient * sign
        label = value(cell, state)
        if label is not None:
            answer[label] += coefficient
    if any(differential.values()):
        raise ValueError('the integral boundary in the named universal cover is nonzero')
    return {word: c for word, c in answer.items() if c}


def planar_charts(block):
    for order in permutations(block):
        yield tuple((i,) for i in order)
        for j, (a, b) in enumerate(zip(order, order[1:])):
            if {a, b} == {0, 1}:
                yield tuple((i,) for i in order[:j]) + ((a, b),) + tuple((i,) for i in order[j+2:])


def audit_boundaries(n):
    counts = Counter()
    hits = 0
    for blocks in partitions(tuple(range(n))):
        temporal = n-len(blocks)
        if not 1 <= temporal <= 3:
            continue
        for cell in product(*(planar_charts(block) for block in blocks)):
            d = dimension(cell)
            if d not in (2, 3):
                continue
            counts[d] += 1
            start = initial(anchor(cell))
            twice = Counter()
            coboundary = Counter()
            for face, route, sign in boundary(cell):
                state = advance(start, route)
                assert tuple(i for i, _ in state) == anchor(face)
                label = value(face, state) if d == 3 else None
                if label is not None:
                    hits += 1
                    coboundary[label] += sign
                for ridge, steps, incidence in boundary(face):
                    twice[ridge, advance(state, steps)] += sign * incidence
            assert not any(coboundary.values()) and not any(twice.values())
    print(n-2, 'rods; two-cells', counts[2], 'three-cells', counts[3], 'wall facets', hits)


def sphere(path, coefficient=1):
    rods = tuple(((i,),) for i in range(2, 4))
    return [(((row,),) + rods, path, sign*coefficient)
            for row, sign in [((0, 1), 1), ((1, 0), -1)]]


def audit_loops():
    for m in range(1, 7):
        for puncture in range(m):
            # Pass earlier rods above their cuts, circle this one, and return.
            approach = tuple((i, 1) for i in range(1, puncture+1))
            loop = approach + ((puncture+1, 1),)*2 + tuple((i, -s) for i, s in reversed(approach))
            start = initial(range(m+2))
            expected = list(start)
            expected[1] = (1, (puncture+1,))
            assert advance(start, loop) == tuple(expected)
    # From a,b,R,S place b after both rods. The approach is then cancelled.
    approach = ((1, -1), (2, -1))
    def route(word):
        braid = push(word, 2)
        turn = tuple((abs(x), 1 if x > 0 else -1) for x in braid)
        return approach + turn + tuple((i, -s) for i, s in reversed(approach))
    gamma = route((1, 2, -1, -2))
    # Moving the two punctures around each other conjugates the pushing word.
    rod_loop = ((2, 1), (2, 1))
    transported = rod_loop + gamma + ((2, -1), (2, -1))
    base = sum_chain(4, sphere(()))
    pushed = sum_chain(4, sphere(gamma))
    moved = sum_chain(4, sphere(transported))
    assert base == {(): 1} and len({*base, *pushed, *moved}) == 3
    assert sum_chain(4, sphere(gamma) + sphere(gamma, -1)) == {}
    print('meridians at the base, after a commutator, and after moving the rods:', base, pushed, moved)
    for open_chain in (sphere(())[:1], sphere(())[:1] + sphere(gamma)[1:]):
        try:
            sum_chain(4, open_chain)
        except ValueError as e:
            assert 'boundary' in str(e)
        else:
            raise AssertionError('accepted a chain with nonzero lifted boundary')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path, help='JSON with rods and chain entries {cell,path,coefficient}')
    args = parser.parse_args()
    if args.input:
        try:
            data = json.loads(args.input.read_text())
            rods = data['rods']
            if type(rods) is not int or rods < 0:
                raise ValueError('rods must be a nonnegative integer')
            entries = [(tuple(tuple(tuple(r) for r in c) for c in entry['cell']),
                        tuple(tuple(m) for m in entry['path']), entry['coefficient']) for entry in data['chain']]
            result = sum_chain(rods+2, entries)
        except (KeyError, ValueError, TypeError) as e:
            parser.error(str(e))
        print('null sphere:', not result)
        print('nonzero signed meridian coefficients:', result)
    else:
        for n in range(2, 6):
            audit_boundaries(n)
        audit_loops()
