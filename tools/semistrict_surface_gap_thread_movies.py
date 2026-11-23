"""Decide private degree-four movies of positive rewrites and scalar events.

--faces FILE uses the positioned private format. --radius R bounds the search
for meetings. Output at a small radius can be unknown.
"""
from argparse import ArgumentParser
from collections import defaultdict
from dataclasses import dataclass
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_history_group import exchange
from semistrict_surface_meridian_transport import Cut, meridian, prod, quasi, transport
from semistrict_surface_private_winding import solve as winding
from semistrict_surface_scalar_meetings import exhausted, hurwitz, meeting_path
from semistrict_surface_shared_edge import inverse


@dataclass(frozen=True)
class SiteCut:
    left: tuple
    site: int
    atom: tuple


def advances(source, target):
    c = source.site
    return (c == target.site and transport(Cut(source.left[c], source.atom), Cut(target.left[c], target.atom))
            and all(quasi(prod(inverse(a), b)) for j, (a, b) in enumerate(zip(source.left, target.left)) if j != c))


def share_frame(s, t):
    def first(x, y):
        return all(quasi(prod(inverse(prod(a, x.atom) if c == x.site else a), b))
                   for c, (a, b) in enumerate(zip(x.left, y.left)))
    return meridian(s.atom)[1] != meridian(t.atom)[1] and (first(s, t) or first(t, s))


class Diagram:
    def __init__(self, data):
        history = data['history']
        wires = [0]*len(data['initial'])
        gaps = list(range(len(wires)+1))
        owner = [0]*len(gaps)
        readers = defaultdict(list)
        groups = {}
        self.sites, self.predecessors = {}, {}
        self.history = tuple((p, e) for e, (p, _) in enumerate(history, 1))
        self.ports = {e: data['marks'][label] for e, (_, label) in enumerate(history, 1)}
        for e, (p, _) in enumerate(history, 1):
            k, l = map(len, self.ports[e])
            if not k and not l:
                gap = gaps[p]
                group = 'gap', gap
                deps = {owner[gap]}
                readers[gap].append(e)
            elif k and l:
                group = 'box', e
                inside = gaps[p+1:p+k]
                deps = set(wires[p:p+k]) | {v for gap in inside for v in readers[gap]}
                deps.update(owner[gap] for gap in inside)
                wires[p:p+k] = [e]*l
                gaps[p+1:p+k] = range(len(owner), len(owner)+l-1)
                owner.extend([e]*(l-1))
            else:
                raise ValueError('one-sided rewrite in the selected history')
            self.sites[e] = groups.setdefault(group, len(groups))
            self.predecessors[e] = deps-{0}
        self.size = len(groups)
        self.root = tuple((e,) for e in self.sites)

    def records(self, frame):
        left = [()]*self.size
        marks = {}
        for atom in frame:
            _, e = meridian(atom)
            c = self.sites[e]
            marks[e] = SiteCut(tuple(left), c, atom)
            left[c] = prod(left[c], atom)
        return marks

    def legal_frame(self, frame):
        seen = set()
        for atom in frame:
            _, e = meridian(atom)
            if e in seen or not self.predecessors[e] <= seen:
                return False
            if any(self.sites[abs(x)] != self.sites[e] for x in atom):
                return False
            seen.add(e)
        return (seen == self.sites.keys() and
                all(prod(*(a for a in frame if self.sites[meridian(a)[1]] == c))
                    == tuple(e for e in self.sites if self.sites[e] == c) for c in range(self.size)))

    def move(self, frame, history, g):
        nxt = exchange(history, g, self.ports)
        if nxt is None:
            return None
        i = abs(g)-1
        e, f = history[i][1], history[i+1][1]
        if self.sites[e] == self.sites[f]:
            frame = hurwitz(frame, i, g > 0)
        else:
            frame = (*frame[:i], frame[i+1], frame[i], *frame[i+2:])
        return frame, nxt

    def read(self, movie):
        f, h = self.root, self.history
        occurrences, anchors, counts = {}, set(), defaultdict(int)
        for op, i in movie:
            if op == 'X':
                f, h = self.move(f, h, i+1)
            else:
                e = h[i][1]
                occurrences[e, counts[e]] = self.records(f)[e]
                counts[e] += 1
                anchors.add(f)
        return occurrences, anchors, f


def decide(diagram, data, radius):
    source, left, a = diagram.read(data['source'])
    target, right, b = diagram.read(data['target'])
    if a != b:
        return dict(surface_filler=False, obstruction='total frame')
    if any(not advances(c, target[m]) for m, c in source.items()):
        return dict(surface_filler=False, obstruction='individual site cuts')
    ranks = {m: j for j, m in enumerate(target)}
    inversions = [(e, f) for e, f in combinations(source, 2) if ranks[e] > ranks[f]]
    if any(all(share_frame(c[e], c[f]) for e, f in inversions) for c in (source, target)):
        return dict(surface_filler=True)
    if all(c == target[m] for m, c in source.items()):
        return dict(surface_filler=False, obstruction='stationary meeting')
    at = defaultdict(dict)
    def record(frame):
        for (e, s), (f, t) in combinations(diagram.records(frame).items(), 2):
            at[e, f][s, t] = at[f, e][t, s] = frame
    for frame in left | right | {diagram.root}:
        record(frame)
    seen, layer, r = {diagram.root}, {diagram.root: diagram.history}, 0
    n = len(diagram.root)
    while True:
        witness = meeting_path(at, source, target, advances)
        if witness is not None:
            order, latest = list(source), dict(source)
            for i, frame in witness:
                assert diagram.legal_frame(frame)
                records = diagram.records(frame)
                e, f = order[i:i+2]
                assert e[0] != f[0]
                for m in (e, f):
                    assert advances(latest[m], records[m[0]])
                    latest[m] = records[m[0]]
                order[i:i+2] = f, e
            assert order == list(target) and all(advances(v, target[m]) for m, v in latest.items())
            return dict(surface_filler=True, meetings=witness, radius=r)
        if not layer or exhausted(r, n, len(source), len(data['source'])+len(data['target'])):
            return dict(surface_filler=False, obstruction='exhausted meeting frames')
        if r == radius:
            return dict(surface_filler=None, radius=r)
        new = {}
        for frame, h in layer.items():
            for i in range(1, n):
                for g in (i, -i):
                    step = diagram.move(frame, h, g)
                    if step is not None and step[0] not in seen:
                        f, k = step
                        seen.add(f)
                        record(f)
                        new[f] = k
        layer = new
        r += 1


def solve(data, radius=None):
    if radius is not None and radius < 0:
        raise ValueError('expected nonnegative radius')
    first = winding(data)
    if first['obstruction']:
        return first
    return decide(Diagram(data), data, radius)


def checks():
    from semistrict_surface_private_abelian_cover import Cover, add, point
    from semistrict_surface_signed_private_model import Ball
    from semistrict_surface_private_heap_order import solve as raw
    base = dict(edges={'f': [0, 0]}, initial=['f', 'f'], start_vertex=0, scalar_at={'s': 0},
                marks={'s': [[], []], 'up': [['f'], ['f', 'f']], 'down': [['f', 'f'], ['f']]},
                higher=[{'p': ['s', 's']}])
    small = dict(base, history=[(0, 'up'), (1, 's'), (1, 's'), (2, 's')])
    diagram = Diagram(small)
    cover = Cover(small['history'], small['marks'])
    assert cover.abelian and cover.rank == 1
    ball = Ball(tuple(small['history']), small['marks'], 4)
    samples = defaultdict(set)
    for path in ball.paths:
        frame, h = diagram.root, diagram.history
        v, k = cover.zero, 0
        for g in path:
            frame, h = diagram.move(frame, h, g)
            k, delta = cover.edges[k][g]
            v = add(v, delta)
        assert diagram.legal_frame(frame)
        for e, c in diagram.records(frame).items():
            samples[e].add((c, (k, *v)))
    pairs = yes = 0
    for e, records in samples.items():
        relation = cover.transports(e-1)
        for c, p in records:
            reached = point(p).apply(relation)
            for d, q in records:
                allowed = advances(c, d)
                assert allowed == (not reached.is_disjoint(point(q)))
                pairs += 1
                yes += allowed

    mixed = dict(base, history=[(1, 's'), (0, 'up')]+[(1, 's')]*4+[(0, 'down'), (1, 's')])
    diagram = Diagram(mixed)
    assert diagram.sites[1] == diagram.sites[8] != diagram.sites[3]
    assert len({diagram.sites[e] for e in (3, 4, 5, 6)}) == 1
    assert diagram.predecessors[7] >= {3, 4, 5, 6}
    ball = Ball(tuple(mixed['history']), mixed['marks'], 3)
    frames = []
    for path in ball.paths:
        f, h = diagram.root, diagram.history
        for g in path:
            f, h = diagram.move(f, h, g)
        assert diagram.legal_frame(f)
        frames.append(f)
    assert len(set(frames)) == len(ball.paths)
    edges = 0
    for i, outgoing in enumerate(ball.edges):
        h = tuple((p, e+1) for p, e in ball.histories[i])
        for g, k in outgoing:
            assert diagram.move(frames[i], h, g)[0] == frames[k]
            edges += 1
    def movie(tokens):
        # Extend a genuine intermediate meeting at four internal scalars by an
        # external gap, a split, a merge, and four more local crossings.
        return [('X', x+1) if x > 0 else ('p', 2-x) for x in tokens]+[('X', 2)]*4
    data = dict(mixed, source=movie((0, 2, 1, 0, 3, 2, 1, -3, 3)),
                target=movie((2, 3, -3, 1, 2, 3, 0, -3, 1)))
    assert solve(data, 0)['surface_filler'] is None
    proof = solve(data, 3)
    assert proof['surface_filler'] and proof['radius'] == 3

    # Three gains: two inside the new gap and one across its left boundary.
    def crossing(w):
        return [('X', i-1) for i in w]
    both = dict(base, history=[(0, 'up')]+[(1, 's')]*3+[(0, 's'), (0, 'down')])
    d = dict(both, source=[('p', 1)]+crossing((3, 2, 3, 4, 2, 2)),
             target=crossing((2, 3, 2, 4))+[('p', 4)]+crossing((2, 2)))
    assert solve(d)['surface_filler'] and not raw(d)['raw_filler']
    print(f'{pairs} one-update tests agree with integral-cover reachability ({yes} inhabited); '
          f'{len(frames)} distinct ambient braids and {edges} signed edges match gap frames. '
          'Interior meetings at four scalars and a three-gain nonreflecting boundary checked.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces', type=Path)
    parser.add_argument('--radius', type=int)
    args = parser.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()), args.radius)))
    else:
        checks()
