"""Classify named positioned history groups by braids of connected components.

--faces FILE reads a private positioned history. --loop W additionally tests a
signed braid (comma-separated one-based letters) at the returned grouped root.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import chain, combinations
import json
from pathlib import Path

from semistrict_surface_history_group import HistoryGroup, inv, realize
from semistrict_surface_private_histories import solve as validate
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_single_power import output_order


class Partition:
    def __init__(self):
        self.parent = {}

    def at(self, x):
        root = self.parent.setdefault(x, x)
        while root != self.parent[root]:
            root = self.parent[root]
        while x != root:
            previous = self.parent[x]
            self.parent[x] = root
            x = previous
        return root

    def unite(self, a, b):
        a, b = self.at(a), self.at(b)
        if a != b:
            self.parent[b] = a


class Components:
    def __init__(self, start, ports, width):
        wires = [-1]*width
        connected, spots = Partition(), Partition()
        incoming, touches = {}, {}
        for j, (p, e) in enumerate(start):
            k, l = map(len, ports[e])
            for v in wires[p:p+k]:
                connected.unite(e, v)
            incoming[e] = j, p
            touches[e] = [(j, q) for q in range(p, p+k+1)]+[(j+1, q) for q in range(p, p+l+1)]
            for q in range(p+1):
                spots.unite((j, q), (j+1, q))
            for q in range(p+k, len(wires)+1):
                spots.unite((j, q), (j+1, q-k+l))
            wires[p:p+k] = [e]*l
        for v in wires:
            connected.unite(-1, v)
        anchored = connected.at(-1)
        groups = defaultdict(list)
        for _, e in start:
            v = connected.at(e)
            if v != anchored:
                groups[v].append(e)
        self.skeleton = {min(es): frozenset(es) for es in groups.values()}
        self.face = {}
        interior = {}
        for c, es in self.skeleton.items():
            first = min(es, key=lambda e: incoming[e][0])
            outer = spots.at(incoming[first])
            self.face[c] = outer
            for e in es:
                for s in touches[e]:
                    f = spots.at(s)
                    if f != outer:
                        assert interior.get(f, c) == c
                        interior[f] = c
        self.parent = {c: interior.get(f) for c, f in self.face.items()}
        self.subtree = {c: set(s) for c, s in self.skeleton.items()}
        for c, s in self.skeleton.items():
            ancestor = self.parent[c]
            while ancestor is not None:
                self.subtree[ancestor].update(s)
                ancestor = self.parent[ancestor]
        children = defaultdict(list)
        for c, f in self.face.items():
            children[f].append(c)
        self.faces = list(children.values())

    def packets(self, h, ports):
        positions = {e: i for i, (_, e) in enumerate(h)}
        blocks = {}
        for c, s in self.subtree.items():
            locs = sorted(positions[e] for e in s)
            start, end = locs[0], locs[-1]+1
            if end-start != len(s):
                return None
            gap, length = h[start][0], 0
            for p, e in h[start:end]:
                k, l = map(len, ports[e])
                if p < gap or p+k > gap+length:
                    return None
                length += l-k
            if length:
                return None
            blocks[c] = (start, end, gap)
        result = []
        for children in self.faces:
            face = sorted((blocks[c], c) for c in children)
            for ((_, i, p), _), ((j, _, q), _) in zip(face, face[1:]):
                if i != j or p != q:
                    return None
            result.append(tuple((c, i, j) for (i, j, _), c in face))
        return result


def restrict(n, word, selected):
    chosen = [i in selected for i in range(n)]
    out = []
    for g in word:
        i = abs(g)-1
        if chosen[i] and chosen[i+1]:
            out.append((1+sum(chosen[:i]))*(1 if g > 0 else -1))
        chosen[i], chosen[i+1] = chosen[i+1], chosen[i]
    return tuple(out)


def cabling(face, word):
    sizes = [j-i for _, i, j in face]
    offset = face[0][1]
    out = []
    for g in word:
        i = abs(g)-1
        k = offset+sum(sizes[:i])
        a, b = sizes[i:i+2]
        if g < 0:
            a, b = b, a
        step = tuple(k+j+l for j in range(b) for l in range(a, 0, -1))
        out.extend(step if g > 0 else inv(step))
        sizes[i], sizes[i+1] = sizes[i+1], sizes[i]
    return tuple(out)


def twist(i, j):
    return tuple(range(i+1, j))*(j-i)


class Group:
    def __init__(self, history, marks, width):
        h = tuple((p, e) for e, (p, _) in enumerate(history))
        self.ports = {e: marks[label] for e, (_, label) in enumerate(history)}
        self.graph = HistoryGroup(h, self.ports)
        self.parts = Components(h, self.ports, width)
        for root, path in self.graph.tree_paths.items():
            packets = self.parts.packets(root, self.ports)
            if packets is not None:
                break
        else:
            raise AssertionError('no grouped vertex for the component tree')
        self.root, self.path = root, path
        self.packets = packets
        self.loc = {e: i for i, (_, e) in enumerate(root)}
        self.n = len(h)

    def ordinary_part(self, pure):
        factors = [(face, restrict(self.n, pure, {i for _, i, _ in face})) for face in self.packets]
        return tuple(chain.from_iterable(cabling(face, w) for face, w in factors)), [w for _, w in factors]

    def split(self, word):
        if any(not 1 <= abs(g) < self.n for g in word):
            raise ValueError('crossing outside the temporal width')
        order = tuple(range(self.n))
        if tuple(output_order(order, tuple(map(abs, word)))) != order:
            return dict(framed=False, actual=False)
        turns = {}
        for c, s in self.parts.skeleton.items():
            if len(s) >= 2:
                a, b = sorted(s)[:2]
                shadow = restrict(self.n, word, {self.loc[a], self.loc[b]})
                count = sum(1 if g > 0 else -1 for g in shadow)
                assert count % 2 == 0
                turns[c] = count//2
        adjusted = tuple(word)
        coefficients = {}
        for c, k in turns.items():
            power = k-turns.get(self.parts.parent[c], 0)
            if power:
                coefficients[c] = power
                s = self.parts.subtree[c]
                t = twist(min(self.loc[e] for e in s), 1+max(self.loc[e] for e in s))
                adjusted += (inv(t) if power > 0 else t)*abs(power)
        real, factors = self.ordinary_part(adjusted)
        framed = braid_image(self.n, adjusted) == braid_image(self.n, real)
        return dict(framed=framed, actual=framed and not coefficients, frame_turns=coefficients,
                    factors=factors, unframed_word=real)

    def verify_generators(self):
        unique = {}
        for loop in self.graph.braids.values():
            w = inv(self.path)+loop+self.path
            action = braid_image(self.n, w)
            if action not in unique:
                assert self.split(w)['actual']
                unique[action] = w
        checked = 0
        for face in self.packets:
            for i, j in combinations(range(len(face)), 2):
                around = tuple(range(j, i+1, -1))
                pure = around+(i+1, i+1)+inv(around)
                cable = cabling(face, pure)
                assert realize(self.root, self.root, cable, self.ports) is not None
                assert self.split(cable)['actual']
                checked += 1
        return len(unique), checked


def solve(data, loop=None):
    h = tuple(map(tuple, data['history']))
    validate({**data, 'source': h, 'target': h})
    group = Group(h, data['marks'], len(data['initial']))
    chart, abstract = group.verify_generators()
    result = dict(root_path=group.path, packets=group.packets, histories=group.graph.vertices,
                  chart_generators_checked=chart, pure_generators_checked=abstract)
    if loop is not None:
        result['loop'] = group.split(loop)
    return result


def checks():
    from random import Random
    rng = Random(164)
    ports = {str((k, l)): (['x']*k, ['x']*l) for k in range(3) for l in range(3)}
    charts = loops = generators = decisions = 0
    for _ in range(150):
        width = rng.randrange(3)
        live = width
        h = []
        for _ in range(rng.randrange(3, 6)):
            k = rng.randrange(min(2, live)+1)
            l = rng.randrange(3)
            h.append((rng.randrange(live-k+1), str((k, l))))
            live += l-k
        group = Group(h, ports, width)
        a, b = group.verify_generators()
        charts += 1
        loops += a
        generators += b
        for _ in range(20):
            # Probe ambient pure braids, including signed windings unavailable
            # in the positioned graph. Compare to independent right fractions.
            w = ()
            for _ in range(rng.randrange(4)):
                i, j = sorted(rng.sample(range(len(h)), 2))
                u = tuple(range(j, i+1, -1))
                atom = u+(i+1, i+1)+inv(u)
                w += rng.choice((atom, inv(atom)))
            actual = realize(group.root, group.root, w, group.ports) is not None
            assert group.split(w)['actual'] == actual
            decisions += 1

    marks = {'s': ([], []), 'u': ([], ['x']), 'd': (['x'], []),
             'U': ([], ['x', 'x']), 'D': (['x', 'x'], [])}
    # Inner bubble and scalar in a bounded face, plus an outer scalar.
    nested = [(0, 's'), (0, 'U'), (1, 's'), (1, 'u'), (1, 'd'), (0, 'D')]
    group = Group(nested, marks, 0)
    assert sorted(map(len, group.packets)) == [2, 2]
    group.verify_generators()
    loops_at_faces = [cabling(f, (1, 1)) for f in group.packets]
    a, b = loops_at_faces
    assert braid_image(6, a+b) == braid_image(6, b+a)
    assert group.parts.parent[3] == 1
    outer, inner = twist(1, 6), twist(3, 5)
    framed = group.split(outer+inv(inner)+a+b)
    assert framed['framed'] and not framed['actual'] and framed['frame_turns'] == {1: 1, 3: -1}
    assert braid_image(6, framed['unframed_word']) == braid_image(6, a+b)
    # Three mobile connected bubbles give a full noncommuting pure factor.
    triple = Group([(0, 'u'), (0, 'd')]*3, marks, 0)
    assert triple.verify_generators()[1] == 3
    face, = triple.packets
    x, y = (cabling(face, (j, j)) for j in (1, 2))
    assert braid_image(6, x+y) != braid_image(6, y+x)
    print(f'{charts} positioned charts: {loops} distinct rooted generators and {generators} '
          f'pure block generators checked, {decisions} independent ambient membership tests. '
          'Nested independent windings, two framing corrections, and a nonabelian triple verified.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces', type=Path)
    parser.add_argument('--loop', help='comma-separated signed braid at the grouped root')
    args = parser.parse_args()
    if args.faces:
        word = tuple(map(int, args.loop.split(','))) if args.loop else None
        print(json.dumps(solve(json.loads(args.faces.read_text()), word)))
    else:
        checks()
