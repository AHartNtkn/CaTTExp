"""Compile a positioned private meeting/gain schedule into free-group equations.

--faces FILE --schedule FILE uses primitive steps from the prefix-chart solver.
The schedule JSON contains its steps and the reported root_path. Only the vertices visited by the primitive actions constrain the equations.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import chain
import json
from pathlib import Path

from semistrict_surface_component_braids import Group
from semistrict_surface_history_group import exchange, inv
from semistrict_surface_meridian_transport import content, meridian, prod
from semistrict_surface_private_winding import solve as winding
from semistrict_surface_scalar_meetings import FiniteFrameGraph


def positioned_quotient(data, modulus):
    if modulus < 1:
        raise ValueError('expected positive reflection modulus')
    # The charged frame and the actual positioned history must agree at a meeting.
    h = tuple((p, e) for e, (p, _) in enumerate(data['history']))
    ports = {e: data['marks'][a] for e, (_, a) in enumerate(data['history'])}
    start = h, tuple(e % modulus for _, e in h)
    states, index = [start], {start: 0}
    # Reuse the signed directed move and finite reachability algorithm, with
    # positions supplied by the actual history in each product vertex.
    model = FiniteFrameGraph()
    model.histories, model.edges, model.neighbors = [], [], []
    for h, colours in states:
        model.histories.append(h)
        edges = {}
        for i, (a, b) in enumerate(zip(colours, colours[1:])):
            for g, pair in ((i+1, ((2*a-b) % modulus, a)), (-i-1, (b, (2*b-a) % modulus))):
                k = exchange(h, g, ports)
                if k is None:
                    continue
                nxt = k, colours[:i]+pair+colours[i+2:]
                if nxt not in index:
                    index[nxt] = len(states)
                    states.append(nxt)
                edges[g] = index[nxt]
        model.edges.append(tuple(edges.items()))
        model.neighbors.append(edges)
    return model


def finite_obstruction(data, modulus):
    return not positioned_quotient(data, modulus).accepts(data['source'], data['target'])


class Equations:
    def __init__(self, n, sample=True):
        self.sample = sample
        self.rank, self.count = n, n
        self.rows, self.values = [], {}

    def fresh(self, nominal=()):
        self.count += 1
        if self.sample:
            self.values[self.count] = nominal
        return (self.count,)

    def evaluate(self, word):
        def value(x):
            if abs(x) <= self.rank:
                return (x,)
            w = self.values[abs(x)]
            return w if x > 0 else inv(w)
        return prod(*(value(x) for x in word))

    def assign(self, word):
        x = self.fresh(self.evaluate(word) if self.sample else ())
        self.rows.append((x, word))
        return x

    def step(self, frame, g):
        i = abs(g)-1
        a, b = frame[i:i+2]
        pair = (self.assign(a+b+inv(a)), a) if g > 0 else (b, self.assign(inv(b)+a+b))
        return (*frame[:i], *pair, *frame[i+2:])

    def follow(self, frame, word):
        for g in word:
            frame = self.step(frame, g)
        return frame

    def framed(self, group, witnesses):
        enclosing = [[] for _ in range(self.rank)]
        for face in group.packets:
            lhs, rhs = [], []
            for c, i, j in face:
                u = self.fresh(witnesses.get(c, ()))
                packet = tuple(range(i+1, j+1))
                lhs.extend(u+packet+inv(u))
                rhs.extend(packet)
                for v in range(i, j):
                    enclosing[v].append((len(packet), u))
            self.rows.append((tuple(lhs), tuple(rhs)))
        frame = []
        for i, wraps in enumerate(enclosing):
            factors = tuple(chain.from_iterable(u for _, u in sorted(wraps, reverse=True)))
            frame.append(self.assign(factors+(i+1,)+inv(factors)))
        return tuple(frame)


def conjugators(group, word):
    s = group.split(word)
    if not s['framed']:
        raise ValueError('proposed loop outside the framed group')
    out = {}
    from semistrict_surface_shared_edge import braid_image
    for face, shadow in zip(group.packets, s['factors']):
        packets = [tuple(range(i+1, j+1)) for _, i, j in face]
        for atom in braid_image(len(face), shadow):
            v, e = meridian(atom)
            c = face[e-1][0]
            # The unframed braid moves the block without mutual linking of
            # its strands. A central rotation changes exactly this exponent.
            k = s['frame_turns'].get(c, 0)-content(v).get(e, 0)
            v = prod(v, ((e if k >= 0 else -e),)*abs(k))
            out[c] = prod(*(packets[x-1] if x > 0 else inv(packets[-x-1]) for x in v))
    return out


def passive_components(group, e):
    classes = {}
    for h in group.graph.tree_paths:
        if h in classes:
            continue
        classes[h] = h
        todo = [h]
        while todo:
            k = todo.pop()
            i = next(j for j, (_, f) in enumerate(k) if f == e)
            for j in range(1, len(k)):
                if j in (i, i+1):
                    continue
                for g in (j, -j):
                    q = exchange(k, g, group.ports)
                    if q is not None and q not in classes:
                        classes[q] = h
                        todo.append(q)
    return classes


def compile_branch(data, steps, root_path=None):
    first = winding(data)
    if first['obstruction']:
        return dict(admissible=False, reason=first['obstruction'])
    group = Group(data['history'], data['marks'], len(data['initial']))
    sys = Equations(group.n)
    root = tuple((i+1,) for i in range(group.n))
    oldroot = inv(group.path)
    # Supplied paths select actual vertices and give optional sample values.
    prefix = () if root_path is None else oldroot+tuple(root_path)
    tree = group.graph
    def vertex(path):
        here = group.root
        for g in path:
            here = exchange(here, g, group.ports)
            if here is None:
                raise ValueError('schedule path fails at its actual ports')
        return here
    def locate(path):
        actual = prefix+tuple(path)
        h = vertex(actual)
        ref = oldroot+tree.tree_paths[h]
        values = conjugators(group, actual+inv(ref))
        return h, sys.follow(sys.framed(group, values), ref)
    classes = {}
    def passive(h, e):
        if e not in classes:
            classes[e] = passive_components(group, e)
        return classes[e][h]
    return action_system(data, steps, sys, vertex(oldroot), sys.follow(root, oldroot),
                         group.ports, locate, passive)


def action_system(data, steps, sys, start_history, start_frame, ports, locate, passive):
    def cut(h, f, e):
        i = next(i for i, (_, x) in enumerate(h) if x == e)
        return h, tuple(chain.from_iterable(f[:i])), f[i]
    def old(movie):
        h, f = start_history, start_frame
        counts, marks = defaultdict(int), {}
        for name, i in movie:
            if name == 'X':
                f, h = sys.step(f, i+1), exchange(h, i+1, ports)
            else:
                e = h[i][1]
                marks[e, counts[e]] = cut(h, f, e)
                counts[e] += 1
        return marks, f
    start, left = old(data['source'])
    end, right = old(data['target'])
    if sys.sample and any(sys.evaluate(a) != sys.evaluate(b) for a, b in zip(left, right)):
        return dict(admissible=False, reason='different total braids')
    order, latest = list(start), start.copy()
    if not sys.sample:
        sys.rows.extend(zip(left, right))
    def align(m, value):
        x, s, a = latest[m]
        y, t, b = value
        if passive(x, m[0]) != passive(y, m[0]):
            return False
        sys.rows.extend(((s, t), (a, b)))
        latest[m] = value
        return True
    for op, i, path, *args in steps:
        if op not in ('gain', 'commute') or not 0 <= i < len(order):
            raise ValueError('expected a gain or meeting at an update index')
        h, f = locate(path)
        m = order[i]
        if not align(m, cut(h, f, m[0])):
            return dict(admissible=False, reason='passive component')
        if op == 'gain':
            g, = args
            if not 0 < abs(g) < len(h) or h[abs(g)-1][1] != m[0]:
                return dict(admissible=False, reason='gain at wrong occurrence')
            k = exchange(h, g, ports)
            if k is None:
                return dict(admissible=False, reason='unavailable gain')
            latest[m] = cut(k, sys.step(f, g), m[0])
        else:
            if i+1 >= len(order) or order[i+1][0] == m[0]:
                return dict(admissible=False, reason='dependent updates')
            other = order[i+1]
            if not align(other, cut(h, f, other[0])):
                return dict(admissible=False, reason='passive component')
            order[i:i+2] = other, m
    if order != list(end) or not all(align(m, end[m]) for m in end):
        return dict(admissible=False, reason='final order or passive component')
    satisfied = all(sys.evaluate(a) == sys.evaluate(b) for a, b in sys.rows) if sys.sample else None
    return dict(admissible=True, rank=sys.rank, variable_count=sys.count-sys.rank,
                equations=sys.rows, sample_satisfies=satisfied)


def checks():
    from itertools import product
    from semistrict_surface_component_braids import cabling, twist
    from semistrict_surface_private_heap_order import solve as raw
    from semistrict_surface_private_prefix_charts import records, solve
    from semistrict_surface_shared_edge import braid_image

    marks = {'s': ([], []), 'u': ([], ['x']), 'd': (['x'], []),
             'U': ([], ['x', 'x']), 'D': (['x', 'x'], [])}
    h = [(0, 's'), (0, 'U'), (1, 's'), (1, 'u'), (1, 'd'), (0, 'D')]
    group = Group(h, marks, 0)
    loops = [cabling(f, (1, 1)) for f in group.packets]
    center = (twist(1, 6), twist(3, 5))
    pure = loops+list(center)
    algebra = passive = corrected = projected = 0
    for choices in product((-1, 0, 1), repeat=4):
        word = tuple(chain.from_iterable(w if k == 1 else inv(w) if k == -1 else ()
                                         for w, k in zip(pure, choices)))
        sys = Equations(6)
        f = sys.framed(group, conjugators(group, word))
        assert all(sys.evaluate(a) == sys.evaluate(b) for a, b in sys.rows)
        assert tuple(map(sys.evaluate, f)) == braid_image(6, word)
        algebra += 1
        if sum(map(abs, choices)) > 2:
            continue
        actual = group.split(word)['unframed_word']
        zero = records(braid_image(6, ()))
        for p in group.graph.tree_paths.values():
            ref = inv(group.path)+p
            old = records(braid_image(6, inv(ref)+word+ref))
            new = records(braid_image(6, inv(ref)+actual+ref))
            for e in zero:
                projected += 1
                if old[e] == zero[e]:
                    assert new[e] == zero[e]
                    passive += 1
                    corrected += bool(any(choices[2:]))
    assert corrected
    d = dict(edges={'x': [0, 0]}, initial=[], start_vertex=0, scalar_at={'s': 0},
             marks={k: marks[k] for k in ('s', 'u', 'd')}, higher=[{'p': ['s', 's']}],
             history=[(0, 's')]*2+[(0, 'u'), (0, 'd')])
    face, = Group(d['history'], d['marks'], 0).packets
    def crossings(word):
        return [('X', i-1) for i in word]
    d.update(source=[('p', 0)]+crossings(cabling(face, (2, 1, 2))+(3, 3)),
             target=crossings(cabling(face, (1, 2, 1)))+[('p', 3)]+crossings((3, 3)))
    out = solve(d, 3, [1, 3])
    assert out['surface_filler'] and not out['grouped'] and not raw(d)['raw_filler']
    formula = compile_branch(d, out['steps'], out['root_path'])
    assert formula['sample_satisfies'] and len(out['steps']) == 3
    print(f'{algebra} nested framed factorizations and {projected} marked projections '
          f'({passive} passive, {corrected} with a nonzero twist) checked. '
          f'Floating-cube comparison: {len(out["steps"])} gains, {out["passive_steps"]} '
          f'passive crossings, {len(formula["equations"])} equations, '
          f'{formula["variable_count"]} variables; raw comparison excluded.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces', type=Path)
    parser.add_argument('--schedule', type=Path)
    args = parser.parse_args()
    if (args.faces is None) != (args.schedule is None):
        parser.error('--faces and --schedule must be supplied together')
    if args.faces:
        schedule = json.loads(args.schedule.read_text())
        print(json.dumps(compile_branch(json.loads(args.faces.read_text()), schedule['steps'],
                                        schedule['root_path'])))
    else:
        checks()
