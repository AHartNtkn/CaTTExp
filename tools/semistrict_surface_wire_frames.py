"""Compile the framed prefixes of a named positioned diagram from its wires.

Meridians are in temporal order. Each wire reads the horizontal cuts it crosses.
With --faces FILE --path WORD check a signed prefix; --loop WORD precomposes
an ambient pure braid at the input drawing before testing its graph action.
--schedule FILE takes a prefix solver certificate or an object with steps in
which each path is replaced by its list of (position, named event) pairs.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import chain
import json
from pathlib import Path

from semistrict_surface_history_group import exchange, inv
from semistrict_surface_meridian_transport import content, meridian, prod
from semistrict_surface_private_framing import Equations
from semistrict_surface_shared_edge import braid_image


def wires(h, ports, width):
    # (-1,j) and (-2,j) specify the j-th fixed top and bottom ends.
    live = [((-1, j), []) for j in range(width)]
    edges = {}
    for i, (p, e) in enumerate(h):
        k, l = map(len, ports[e])
        if not 0 <= p <= len(live)-k:
            raise ValueError('event outside its spatial slice')
        for _, word in live[:p]:
            word.append(i+1)
        for j, (start, word) in enumerate(live[p:p+k]):
            edges[start, (e, j)] = tuple(word)
        live[p:p+k] = [((e, j), []) for j in range(l)]
    for j, (start, word) in enumerate(live):
        edges[start, (-2, j)] = tuple(word)
    return edges


def substitute(word, frame):
    return tuple(chain.from_iterable(frame[x-1] for x in word))


def chart_equations(sys, start, h, ports, width, lifts=None):
    """Return symbolic Artin frame; sys acquires exactly its wire constraints."""
    a, b = wires(start, ports, width), wires(h, ports, width)
    if a.keys() != b.keys():
        raise ValueError('different named wire incidence')
    origins = {e: i+1 for i, (_, e) in enumerate(start)}
    lifts = lifts or {}
    tails = {e: sys.fresh(lifts.get(e, ())) for _, e in h}
    frame = tuple(sys.assign(tails[e]+(origins[e],)+inv(tails[e])) for _, e in h)
    sys.rows.append((tuple(chain.from_iterable(frame)), tuple(range(1, len(h)+1))))
    for edge, old in a.items():
        (e, _), (f, _) = edge
        sys.rows.append((substitute(b[edge], frame), tails.get(e, ())+old+inv(tails.get(f, ()))))
    return frame


def point_lifts(start, h, ports, width, frame):
    """Recover all incident vertex lifts for a specified ambient frame."""
    a, b = wires(start, ports, width), wires(h, ports, width)
    if a.keys() != b.keys():
        return None
    origins = {e: i+1 for i, (_, e) in enumerate(start)}
    tails = {}
    for (_, e), atom in zip(h, frame):
        tail, index = meridian(atom)
        if index != origins[e]:
            return None
        tails[e] = tail
    turns = {}
    for edge, source in a.items():
        (e, _), (f, _) = edge
        test = prod(inv(tails.get(e, ())), substitute(b[edge], frame), tails.get(f, ()))
        delta = content(prod(test, inv(source)))
        for v, sign in ((e, 1), (f, -1)):
            if v >= 0:
                turn = sign*delta.get(origins[v], 0)
                if turns.setdefault(v, turn) != turn:
                    return None
    lifts = {}
    for e, u in tails.items():
        k = turns.get(e, 0)
        lifts[e] = prod(u, ((origins[e] if k >= 0 else -origins[e]),)*abs(k))
    sys = Equations(len(h))
    chart_equations(sys, start, h, ports, width, lifts)
    if all(sys.evaluate(left) == sys.evaluate(right) for left, right in sys.rows):
        return lifts
    return None


def follow(start, path, ports):
    h = start
    for g in path:
        h = exchange(h, g, ports)
        if h is None:
            raise ValueError('path crosses overlapping spatial sites')
    return h


def diagram_key(h, ports, width):
    """Named incidence, with a partition of all corners by complementary face."""
    from semistrict_surface_component_braids import Partition
    width0 = width
    spots = Partition()
    corners = {(0, j): (0, j) for j in range(width+1)}
    for i, (p, e) in enumerate(h):
        k, l = map(len, ports[e])
        for j in range(k+1):
            corners[2, e, 0, j] = i, p+j
        for j in range(l+1):
            corners[2, e, 1, j] = i+1, p+j
        for j in range(p+1):
            spots.unite((i, j), (i+1, j))
        for j in range(p+k, width+1):
            spots.unite((i, j), (i+1, j+l-k))
        width += l-k
    for j in range(width+1):
        corners[1, j] = len(h), j
    faces = defaultdict(set)
    for name, loc in corners.items():
        faces[spots.at(loc)].add(name)
    return frozenset(wires(h, ports, width0)), frozenset(map(frozenset, faces.values()))


def passive_key(h, ports, width, mark):
    i = next(j for j, (_, e) in enumerate(h) if e == mark)
    def delta(e):
        k, l = map(len, ports[e])
        return l-k
    after = width+sum(delta(e) for _, e in h[:i+1])
    return h[i][0], diagram_key(h[:i], ports, width), diagram_key(h[i+1:], ports, after)


def setup(data):
    h = tuple((p, e) for e, (p, _) in enumerate(data['history']))
    ports = {e: data['marks'][label] for e, (_, label) in enumerate(data['history'])}
    return h, ports, len(data['initial'])


def compile_schedule(data, schedule):
    from semistrict_surface_private_framing import action_system
    from semistrict_surface_private_winding import solve as winding
    failure = winding(data)['obstruction']
    if failure:
        return dict(admissible=False, reason=failure)
    start, ports, width = setup(data)
    key = diagram_key(start, ports, width)
    # A located branch has compact vertices. A certified chart proof also
    # supplies paths, allowing all equations to be checked on its witness.
    sampled = 'root_path' in schedule
    sys = Equations(len(start), sample=sampled)
    root = tuple((i+1,) for i in range(len(start)))
    def locate(checkpoint):
        lifts = None
        if sampled:
            path = tuple(schedule['root_path'])+tuple(checkpoint)
            h = follow(start, path, ports)
            lifts = point_lifts(start, h, ports, width, braid_image(len(h), path))
            assert lifts is not None
        else:
            h = tuple(map(tuple, checkpoint))
            if sorted(e for _, e in h) != list(range(len(start))) or diagram_key(h, ports, width) != key:
                raise ValueError('checkpoint outside the named diagram class')
        return h, chart_equations(sys, start, h, ports, width, lifts)
    return action_system(data, schedule['steps'], sys, start, root, ports, locate,
                         lambda h, e: passive_key(h, ports, width, e))


def has_zero_turns(h, ports, lifts):
    return lifts is not None and all(not any(ports[e]) or content(lifts[e]).get(i+1, 0) == 0
                                     for i, (_, e) in enumerate(h))


def checks():
    from random import Random
    from semistrict_surface_component_braids import Group, cabling, twist
    from semistrict_surface_history_group import realize
    from semistrict_surface_private_framing import passive_components
    from semistrict_surface_private_prefix_charts import solve
    rng = Random(166)
    ports = {str((k, l)): (['x']*k, ['x']*l) for k in range(3) for l in range(3)}
    key_tests = tests = accepted = framed_only = passive_tests = fractions = 0
    for _ in range(80):
        width = rng.randrange(3)
        live = width
        history = []
        for _ in range(rng.randrange(3, 6)):
            k, l = rng.randrange(min(2, live)+1), rng.randrange(3)
            label = str((k,l))
            history.append((rng.randrange(live-k+1), label))
            live += l-k
        group = Group(history, ports, width)
        start = tuple((p, e) for e, (p, _) in enumerate(history))
        vertices = list(group.graph.tree_paths)
        key = diagram_key(start, group.ports, width)
        for e in range(group.n):
            classes = passive_components(group, e)
            buckets, reverse = {}, {}
            for h in vertices:
                v = passive_key(h, group.ports, width, e)
                assert buckets.setdefault(v, classes[h]) == classes[h]
                assert reverse.setdefault(classes[h], v) == v
                passive_tests += 1
        for _ in range(20):
            names = rng.sample(range(group.n), group.n)
            live, candidate = width, []
            for e in names:
                k, l = map(len, group.ports[e])
                if k > live:
                    break
                candidate.append((rng.randrange(live-k+1), e))
                live += l-k
            else:
                h = tuple(candidate)
                assert (diagram_key(h, group.ports, width) == key) == (h in group.graph.tree_paths)
                key_tests += 1
            h = rng.choice(vertices)
            path = group.graph.tree_paths[h]
            i, j = sorted(rng.sample(range(group.n), 2))
            loop = rng.choice(((), twist(i, j+1), inv(twist(i, j+1))))
            word = loop+path
            lifts = point_lifts(start, h, group.ports, width, braid_image(group.n, word))
            split = group.split(inv(group.path)+loop+group.path)
            expected, actual = split['framed'], split['actual']
            if len(word) <= 6:
                assert actual == (realize(start, h, word, group.ports) is not None)
                fractions += 1
            assert (lifts is not None) == expected and has_zero_turns(start, group.ports, lifts) == actual
            tests += 1
            accepted += actual
            framed_only += expected and not actual
    assert framed_only
    marks = {'s': ([], []), 'u': ([], ['x']), 'd': (['x'], []),
             'U': ([], ['x','x']), 'D': (['x','x'], [])}
    nested = [(0,'s'), (0,'U'), (1,'s'), (1,'u'), (1,'d'), (0,'D')]
    group = Group(nested, marks, 0)
    q = twist(1,6)+inv(twist(3,5))
    for h, path in group.graph.tree_paths.items():
        lifts = point_lifts(group.root, h, group.ports, 0, braid_image(6, q+inv(group.path)+path))
        assert lifts is not None and not has_zero_turns(group.root, group.ports, lifts)
    d = dict(edges={'x':[0,0]}, initial=[], start_vertex=0, scalar_at={'s':0},
             marks={k: marks[k] for k in ('s','u','d')}, higher=[{'p':['s','s']}],
             history=[(0,'s')]*2+[(0,'u'),(0,'d')])
    simple = Group(d['history'], d['marks'], 0)
    face, = simple.packets
    def x(w):
        return [('X',g-1) for g in w]
    d.update(source=[('p',0)]+x(cabling(face,(2,1,2))+(3,3)),
             target=x(cabling(face,(1,2,1)))+[('p',3)]+x((3,3)))
    proof = solve(d,3)
    formula = compile_schedule(d,proof)
    assert formula['sample_satisfies']
    steps = [(op,i,follow(simple.root, path, simple.ports),g) for op,i,path,g in proof['steps']]
    compact = compile_schedule(d,dict(steps=steps))
    assert all(row in compact['equations'] for row in formula['equations'])
    print(f'{key_tests} named diagram tests and {passive_tests} passive class entries agree '
          f'with the positioned graph. {tests} framed/actual prefix tests: {accepted} '
          f'executable and {framed_only} framed only; {fractions} orthogonal cross-checks. Nested twists checked at '
          f'{len(group.graph.tree_paths)} vertices; chart-free floating-cube branch '
          f'has {len(compact["equations"])} equations on {compact["variable_count"]} variables.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces', type=Path)
    parser.add_argument('--schedule', type=Path)
    parser.add_argument('--path', default='')
    parser.add_argument('--loop', default='')
    args = parser.parse_args()
    if args.faces:
        data = json.loads(args.faces.read_text())
        if args.schedule:
            result = compile_schedule(data, json.loads(args.schedule.read_text()))
        else:
            def word(s):
                return tuple(map(int, s.split(','))) if s else ()
            h, ports, width = setup(data)
            path = word(args.path)
            k = follow(h, path, ports)
            lifts = point_lifts(h, k, ports, width, braid_image(len(h), word(args.loop)+path))
            result = dict(framed=lifts is not None, executable=has_zero_turns(h, ports, lifts), lifts=lifts)
        print(json.dumps(result))
    else:
        checks()
