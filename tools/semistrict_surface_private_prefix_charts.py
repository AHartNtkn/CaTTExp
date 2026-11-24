"""Eliminate passive paths in private positioned movies using ambient Artin cuts.

The default search decides all private inputs by the component-framing bound.
A requested small radius can leave a comparison open.
"""
from argparse import ArgumentParser
from collections import defaultdict, deque
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_component_braids import Group
from semistrict_surface_history_group import exchange, inv, realize
from semistrict_surface_meridian_transport import Cut, meridian, prod, transport
from semistrict_surface_private_winding import solve as winding
from semistrict_surface_scalar_meetings import exhausted, hurwitz
from semistrict_surface_shared_edge import braid_image


def records(frame):
    left, result = (), {}
    for a in frame:
        result[meridian(a)[1]] = Cut(left, a)
        left = prod(left, a)
    return result


def scalar_blocks(h, ports):
    ends = []
    for i, (p, e) in enumerate(h):
        if i and not any(ports[e]) and h[i-1][0] == p and not any(ports[h[i-1][1]]):
            ends[-1] += 1
        else:
            ends.append(i+1)
    return ends


def grouped_chart(group):
    n = len(next(iter(group.tree_paths)))
    trivial = braid_image(n, ())
    loops = {braid_image(n, w): w for w in group.braids.values()}
    loops.pop(trivial, None)
    candidates = sorted(group.tree_paths, key=lambda h: len(scalar_blocks(h, group.marks)))
    for h in candidates:
        p = group.tree_paths[h]
        ends = scalar_blocks(h, group.marks)
        for loop in loops.values():
            frame = braid_image(n, inv(p)+loop+p)
            if any(prod(*frame[:i]) != tuple(range(1, i+1)) for i in ends[:-1]):
                break
        else:
            return h


class PrefixChart:
    def __init__(self, h, ports):
        self.root, self.ports = h, ports
        f = braid_image(len(h), ())
        self.layer = [(f, h, ())]
        self.seen = {f}
        self.gains = defaultdict(dict)
        self.meet = {}
        self.record(f, h, ())

    def record(self, frame, h, path):
        letters = records(frame)
        for x, y in combinations(letters.values(), 2):
            self.meet[x, y] = self.meet[y, x] = path
        for i in range(len(h)-1):
            e = meridian(frame[i])[1]
            for g in (i+1, -i-1):
                if exchange(h, g, self.ports) is not None:
                    after = hurwitz(frame, i, g > 0)
                    dest = records(after)[e]
                    self.gains[letters[e]][dest] = path, g

    def grow(self):
        next_layer = []
        for frame, h, path in self.layer:
            for i in range(len(h)-1):
                for g in (i+1, -i-1):
                    k = exchange(h, g, self.ports)
                    if k is None:
                        continue
                    f = hurwitz(frame, i, g > 0)
                    if f not in self.seen:
                        self.seen.add(f)
                        q = path+(g,)
                        next_layer.append((f, k, q))
                        self.record(f, k, q)
        self.layer = next_layer

    def read(self, prefix, movie):
        path, cuts, anchors, counts = tuple(prefix), {}, {}, defaultdict(int)
        h = self.follow(path)
        frame = braid_image(len(h), path)
        for name, i in movie:
            if name == 'X':
                path += (i+1,)
                h = exchange(h, i+1, self.ports)
                assert h is not None
                frame = hurwitz(frame, i, True)
            else:
                e = meridian(frame[i])[1]
                key = e, counts[e]
                counts[e] += 1
                cuts[key], anchors[key] = records(frame)[e], path
                self.record(frame, h, path)
        return cuts, anchors, frame

    def follow(self, path):
        h = self.root
        for g in path:
            h = exchange(h, g, self.ports)
            assert h is not None
        return h

    def search(self, source, target, can_finish=transport):
        start, end = tuple(source.items()), tuple(target.items())
        queue, seen = deque([start]), {start: None}
        while queue:
            w = queue.popleft()
            if w == end:
                out = []
                while seen[w] is not None:
                    w, step = seen[w]
                    out.append(step)
                return out[::-1]
            for i, (m, c) in enumerate(w):
                for d, (path, g) in self.gains[c].items():
                    if not can_finish(d, target[m]):
                        continue
                    q = w[:i]+((m, d),)+w[i+1:]
                    if q not in seen:
                        seen[q] = w, ('gain', i, path, g)
                        queue.append(q)
                if i+1 < len(w) and (c, w[i+1][1]) in self.meet:
                    q = w[:i]+(w[i+1], w[i])+w[i+2:]
                    if q not in seen:
                        seen[q] = w, ('commute', i, self.meet[c, w[i+1][1]])
                        queue.append(q)
        return None

    def verify(self, a, b, steps):
        order, latest = list(a), a.copy()
        passive = 0
        def align(m, path):
            nonlocal passive
            current = latest[m]
            h, k = self.follow(current), self.follow(path)
            # The Artin names are positions at the chosen root.
            e = self.root[m[0]-1][1]
            i = next(j for j, (_, f) in enumerate(h) if f == e)
            word = realize(h, k, inv(current)+path, self.ports)
            assert word is not None and all(abs(g) not in (i, i+1) for g in word)
            passive += len(word)
            latest[m] = path
        for op, i, path, *args in steps:
            m = order[i]
            align(m, path)
            if op == 'gain':
                g, = args
                h = self.follow(path)
                assert h[abs(g)-1][1] == self.root[m[0]-1][1]
                self.follow(path+(g,))
                latest[m] = path+(g,)
            else:
                align(order[i+1], path)
                order[i:i+2] = order[i+1], m
        assert order == list(b)
        for m in b:
            align(m, b[m])
        return passive


def solve(data, radius=None, moduli=()):
    if radius is not None and radius < 0:
        raise ValueError('expected nonnegative radius')
    preliminary = winding(data)
    if preliminary['obstruction']:
        return preliminary
    structure = Group(data['history'], data['marks'], len(data['initial']))
    group = structure.graph
    simple_root = grouped_chart(group)
    root = structure.root if simple_root is None else simple_root
    chart = PrefixChart(root, structure.ports)
    rebase = inv(group.tree_paths[root])
    a, old, left = chart.read(rebase, data['source'])
    b, new, right = chart.read(rebase, data['target'])
    if left != right or any(not transport(c, b[m]) for m, c in a.items()):
        return dict(surface_filler=False, obstruction='ambient braid or mark transport')
    for modulus in moduli:
        from semistrict_surface_private_framing import finite_obstruction
        if finite_obstruction(data, modulus):
            return dict(surface_filler=False, obstruction='positioned reflection quotient', modulus=modulus)
    n, m = len(root), len(old)
    swaps = (m*max(0, n-1)+1)*m*(m-1)//2
    # The branch equations include a fixed chart path per gain and meeting.
    height = max(map(len, group.tree_paths.values()), default=0)
    size = len(data['source'])+len(data['target'])+(2*height+n+2)**2*(swaps+m*n+2)
    info = dict(grouped=simple_root is not None, histories=len(group.tree_paths), root_path=group.tree_paths[root])
    r = 0
    while True:
        proof = chart.search(a, b)
        if proof is not None:
            passive = chart.verify(old, new, proof)
            return dict(info, surface_filler=True, steps=proof, passive_steps=passive, radius=r)
        if not chart.layer or exhausted(r, n, m, size):
            return dict(info, surface_filler=False)
        if radius == r:
            return dict(info, surface_filler=None, radius=r)
        chart.grow()
        r += 1


def checks():
    from semistrict_surface_private_heap_order import solve as raw
    from semistrict_surface_signed_private_model import Ball
    base = dict(edges={'f': [0, 0]}, initial=[], start_vertex=0, scalar_at={'s': 0},
                marks={'s': [[], []], 'u': [[], ['f']], 'd': [['f'], []]}, higher=[{'p': ['s', 's']}])
    total = passive = 0
    for names in ('ssu', 'ssud'):
        h = tuple((0, label) for label in names)
        graph = Ball(h, base['marks'], 3)
        ports = {i: base['marks'][label] for i, (_, label) in enumerate(h)}
        cuts = [records(braid_image(len(h), p)) for p in graph.paths]
        for j, a in enumerate(graph.paths):
            for k, b in enumerate(graph.paths):
                step = realize(graph.histories[j], graph.histories[k], inv(a)+b, ports)
                assert step is not None
                for e in range(len(h)):
                    i = next(i for i, (_, f) in enumerate(graph.histories[j]) if f == e)
                    yes = all(abs(g) not in (i, i+1) for g in step)
                    assert (cuts[j][e+1] == cuts[k][e+1]) == yes
                    total += 1
                    passive += yes
    def crossing(p):
        return [('X', g-1) for g in p]
    d = dict(base, history=[(0, 's')]*3+[(0, 'u')],
             source=[('p', 0)]+crossing((2, 1, 2, 3, 1, 1)),
             target=crossing((1, 2, 1, 3))+[('p', 3)]+crossing((1, 1)))
    out = solve(d, 3)
    assert out['grouped'] and out['surface_filler'] and out['passive_steps'] > 0
    assert not raw(d)['raw_filler']
    # The four scalars alternate between the two new gaps at the input. A
    # signed tree connector carries them to one common block before the birth.
    separate = dict(base, history=[(0, 'u'), (0, 's'), (1, 's'), (0, 's'), (1, 's')],
                    source=[('p', 2)]+crossing((3, 4)), target=crossing((3, 4))+[('p', 4)])
    out = solve(separate, 5)
    assert out['grouped'] and out['root_path'] and out['surface_filler']
    # A nontrivial floating connected component can braid with both scalars.
    floating = dict(base, history=[(0, 's')]*2+[(0, 'u'), (0, 'd')], source=[], target=[])
    assert not solve(floating, 0)['grouped']
    print(f'{total} passive comparisons of legal endpoints agree with orthogonal fractions '
          f'({passive} transports); grouped nonabelian charts with 90 and 744 histories '
          'and the floating bubble boundary checked.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces', type=Path)
    parser.add_argument('--radius', type=int)
    parser.add_argument('--modulus', type=int, action='append', default=[])
    args = parser.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()), args.radius, args.modulus)))
    else:
        checks()
