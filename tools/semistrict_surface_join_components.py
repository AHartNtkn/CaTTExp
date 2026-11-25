"""Check which connected planar components move under a positioned exchange movie.

JSON input has edges, rules, root, path, history, left and right. The last two
are signed adjacent exchanges from the history to the same positioned history.
Component vertex numbers refer to the original history, starting at zero.
Alternatively supply edges, rules, root, a connected bubble, and repairs
(each with root, path, history, left and right) to test the size certificate.
"""
import argparse
from collections import defaultdict
from itertools import product
import json
from pathlib import Path

from semistrict_surface_braid_reflection import end_vertex
from semistrict_surface_bubble_transfer import block_word
from semistrict_surface_history_group import exchange


def components(edges, rules, root, path, history):
    end_vertex(edges, root, path)
    wires = [(e, None) for e in path]
    neighbours = defaultdict(set)
    boundary = set()
    for i, (position, name) in enumerate(history):
        vertex, left, right = rules[name]
        word = ''.join(e for e, _ in wires)
        if not (0 <= position <= len(word) and word.startswith(left, position)
                and end_vertex(edges, root, word[:position]) == vertex
                and end_vertex(edges, vertex, left) == end_vertex(edges, vertex, right)):
            raise ValueError('ill-typed rewrite')
        for _, producer in wires[position:position + len(left)]:
            if producer is None:
                boundary.add(i)
            else:
                neighbours[i].add(producer)
                neighbours[producer].add(i)
        wires[position:position + len(left)] = [(e, i) for e in right]
    boundary.update(i for _, i in wires if i is not None)
    unseen = set(range(len(history)))
    closed = set()
    while unseen:
        group = {unseen.pop()}
        stack = list(group)
        while stack:
            more = unseen & neighbours[stack.pop()]
            unseen -= more
            group |= more
            stack.extend(more)
        if group.isdisjoint(boundary):
            closed.add(frozenset(group))
    return closed, ''.join(e for e, _ in wires)


def track(data, movie):
    marks = {name: (left, right) for name, (_, left, right) in data['rules'].items()}
    history = tuple(map(tuple, data['history']))
    indices = list(range(len(history)))
    for crossing in movie:
        i = abs(crossing) - 1
        if not 0 <= i < len(indices) - 1:
            raise ValueError('exchange outside the history')
        history = exchange(history, crossing, marks)
        if history is None:
            raise ValueError('exchange of dependent or incorrectly ordered events')
        indices[i], indices[i + 1] = indices[i + 1], indices[i]
    return history, indices


def compare(data):
    args = data['edges'], data['rules'], data['root'], data['path']
    start, _ = components(*args, data['history'])
    end, left = track(data, data['left'])
    other, right = track(data, data['right'])
    if end != other:
        raise ValueError('movies have different targets')
    target, _ = components(*args, end)
    def pullback(order):
        return {c: frozenset(order[i] for i in c) for c in target}
    a, b = pullback(left), pullback(right)
    if set(a.values()) != start or set(b.values()) != start:
        raise ValueError('exchange failed to preserve component incidence')
    return sorted(sorted(a[c]) for c in target if a[c] != b[c])


def certificate(data):
    history = data['bubble']
    size = len(history)
    common = dict(edges=data['edges'], rules=data['rules'])
    groups, end = components(data['edges'], data['rules'], data['root'], '', history)
    if end or not size or groups != {frozenset(range(size))}:
        raise ValueError('expected one connected nonempty empty-to-empty history')
    for repair in data['repairs']:
        moved = compare(dict(repair, **common))
        if any(len(component) == size for component in moved):
            return False
    return True


def checks():
    rules = {'open': ('x', '', 'f'), 'tick': ('x', 'f', 'f'),
             'close': ('x', 'f', ''), 'split': ('x', 'f', 'ff'),
             'merge': ('x', 'ff', 'f')}
    data = dict(edges={'f': ('x', 'x')}, rules=rules, path='', root='x', left=[])
    def wire(k):
        return [(0, 'open')] + [(0, 'tick')] * k + [(0, 'close')]
    for k in range(12):
        history = wire(k)
        n = len(history)
        data.update(history=2 * history, right=block_word(n, (1,)))
        assert compare(data) == [list(range(n)), list(range(n, 2*n))]
        # Cutting the connected component across an internal wire now anchors it.
        assert components(data['edges'], rules, 'x', '', history[:-1])[0] == set()
        assert components(data['edges'], rules, 'x', 'f', history[1:])[0] == set()
    placements = 0
    for small, outer in product(range(3), range(1, 6)):
        local = wire(small)
        n = len(local)
        swap = block_word(n, (1,))
        for cut in range(1, outer + 2):
            boundary = wire(outer)
            # Insert into a live gap in a larger connected wire's history.
            data.update(history=boundary[:cut] + 2 * local + boundary[cut:],
                        right=[cut + x for x in swap])
            assert compare(data) == [list(range(cut, cut + n)), list(range(cut + n, cut + 2*n))]
            placements += 1
    # An interior connected graph can branch and merge.
    split = [(0, x) for x in ('open', 'split', 'merge', 'close')]
    data.update(history=2 * split, right=block_word(4, (1,)))
    assert compare(data) == [list(range(4)), list(range(4, 8))]
    repairs = [dict(root='x', history=2 * wire(k), path='', left=[],
                    right=block_word(k + 2, (1,))) for k in range(5)]
    for k in range(10):
        data.update(bubble=wire(k), repairs=repairs)
        assert certificate(data) == (k >= 5)
    return placements


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        if 'bubble' in data:
            print('raw separation certified' if certificate(data) else 'size test inconclusive')
        else:
            print(json.dumps(compare(data)))
    else:
        print(f'12 diagonal block exchanges, 24 cut fragments, {checks()} placed repairs and 10 repair-family queries checked (including a branched bubble control)')
