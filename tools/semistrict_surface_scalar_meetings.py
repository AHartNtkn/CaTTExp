"""Decide degree-four private scalar movies of any width at one spatial gap.

--radius R gives a bounded search for meeting frames. The default continues
through the free-equation small-solution bound. That bound is theoretical.
Finite quotients and direct mark transports can settle a query much earlier.
"""
from argparse import ArgumentParser
from collections import defaultdict, deque
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_meridian_transport import Cut, cuts, meridian, prod, solve as individual, transport
from semistrict_surface_planar_tiers import artin_step
from semistrict_surface_shared_edge import inverse
from semistrict_surface_signed_private_model import Ball


def hurwitz(frame, i, positive):
    if positive:
        return artin_step(frame, i)
    a, b = frame[i:i+2]
    return (*frame[:i], b, prod(inverse(b), a, b), *frame[i+2:])


def old_frames(n, steps):
    frame = tuple((e+1,) for e in range(n))
    for op, i in steps:
        if op == 'X':
            frame = artin_step(frame, i)
        else:
            yield frame


class Meetings:
    def __init__(self, n, anchors):
        root = tuple((e+1,) for e in range(n))
        self.frontier, self.seen = {root}, {root}
        self.at = defaultdict(dict)
        for f in {*anchors, root}:
            self.record(f)

    def record(self, frame):
        before = ()
        marked = []
        for a in frame:
            marked.append((meridian(a)[1], Cut(before, a)))
            before = prod(before, a)
        for (e, s), (f, t) in combinations(marked, 2):
            self.at[e, f][s, t] = frame
            self.at[f, e][t, s] = frame

    def grow(self):
        layer = set()
        for f in self.frontier:
            for i in range(len(f)-1):
                for direction in (False, True):
                    h = hurwitz(f, i, direction)
                    if h not in self.seen:
                        self.seen.add(h)
                        layer.add(h)
                        self.record(h)
        self.frontier = layer


def meeting_path(frames, source, target, move):
    possible = lru_cache(None)(move)
    @lru_cache(None)
    def candidates(e, f):
        return tuple((s, t) for s, t in frames[e[0], f[0]]
                     if possible(source[e], s) and possible(s, target[e]) and
                     possible(source[f], t) and possible(t, target[f]))
    start = tuple(source.items())
    goal = tuple(target)
    parents, queue = {start: None}, deque([start])
    while queue:
        state = queue.popleft()
        if tuple(m for m, _ in state) == goal:
            # Each stored cut can reach its own prescribed target.
            witness = []
            while parents[state] is not None:
                state, i, frame = parents[state]
                witness.append((i, frame))
            return witness[::-1]
        for i in range(len(state)-1):
            (e, s), (f, t) = state[i:i+2]
            if e[0] == f[0]:
                continue
            for u, v in candidates(e, f):
                if possible(s, u) and possible(t, v):
                    nxt = state[:i]+((f, v), (e, u))+state[i+2:]
                    if nxt not in parents:
                        parents[nxt] = state, i, frames[e[0], f[0]][u, v]
                        queue.append(nxt)
    return None


class ReflectionQuotient:
    """Full finite Hurwitz orbit of labelled dihedral reflections."""
    steps = Ball.steps

    def __init__(self, colours, modulus):
        # The second entry is always the original occurrence, as in Ball.steps.
        root = tuple((c % modulus, e) for e, c in enumerate(colours))
        self.histories, self.edges, self.neighbors = [root], [], []
        index = {root: 0}
        for frame in self.histories:
            edge = {}
            for i, ((a, e), (b, f)) in enumerate(zip(frame, frame[1:])):
                for sign, pair in ((1, (((2*a-b) % modulus, f), (a, e))),
                                   (-1, ((b, f), ((2*b-a) % modulus, e)))):
                    nxt = frame[:i]+pair+frame[i+2:]
                    if nxt not in index:
                        index[nxt] = len(self.histories)
                        self.histories.append(nxt)
                    edge[sign*(i+1)] = index[nxt]
            self.edges.append(tuple(edge.items()))
            self.neighbors.append(edge)

    def word(self, movie):
        h, counts, w = 0, defaultdict(int), []
        for op, i in movie:
            if op == 'X':
                h = self.neighbors[h][i+1]
            else:
                e = self.histories[h][i][1]
                w.append((e, counts[e], h))
                counts[e] += 1
        return tuple(w)

    def accepts(self, left, right):
        a, b = self.word(left), self.word(right)
        # Restrict transport to stages between the two old predecessor sets.
        def before(e, h):
            order = [x for _, x in self.histories[h]]
            return frozenset(order[:order.index(e)])
        limits = {(e, j): before(e, h) for e, j, h in b}
        queue, seen = deque([a]), {a}
        while queue:
            w = queue.popleft()
            if w == b:
                return True
            for op, v in self.steps(w):
                if op[0] == 'transport':
                    e, j, h = v[op[1]]
                    if not before(e, h) <= limits[e, j]:
                        continue
                if v not in seen:
                    seen.add(v)
                    queue.append(v)
        return False


def verify(source, target, witness, n):
    order, latest = list(source), source.copy()
    for i, frame in witness:
        assert prod(*frame) == tuple(range(1, n+1))
        assert sorted(meridian(a)[1] for a in frame) == list(range(1, n+1))
        records = {meridian(a)[1]: Cut(prod(*frame[:j]), a) for j, a in enumerate(frame)}
        e, f = order[i:i+2]
        assert e[0] != f[0]
        for m in (e, f):
            assert transport(latest[m], records[m[0]])
            latest[m] = records[m[0]]
        order[i:i+2] = f, e
    assert order == list(target)
    assert all(transport(v, target[m]) for m, v in latest.items())


def exhausted(radius, width, marks, old_length):
    """Compare against the double-exponential bound without constructing it."""
    gains = marks*max(0, width-1)
    swaps = (gains+1)*marks*(marks-1)//2
    alphabet_bound = 10**8 * (2+width+marks+swaps+old_length)**4
    if radius < 2:
        return False
    return (radius.bit_length()-1).bit_length()-1 >= alphabet_bound**4


def solve(data, radius=None, moduli=()):
    if radius is not None and radius < 0:
        raise ValueError('expected nonnegative search radius')
    first = individual(data)
    if first['surface_filler'] is not None:
        return first
    n = len(data['history'])
    a, b = data['source'], data['target']
    source, target = cuts(n, a)[0], cuts(n, b)[0]
    for p in moduli:
        if p < 1:
            raise ValueError('expected positive reflection modulus')
        model = ReflectionQuotient(range(n), p)
        if not model.accepts(a, b):
            return dict(surface_filler=False, obstruction='finite reflection orbit',
                        modulus=p, frames=len(model.histories))
    model = Meetings(n, (*old_frames(n, a), *old_frames(n, b)))
    r = 0
    while True:
        witness = meeting_path(model.at, source, target, transport)
        if witness is not None:
            verify(source, target, witness, n)
            return dict(surface_filler=True, meeting_radius=r, frames=len(model.seen), meetings=witness)
        if exhausted(r, n, len(source), len(a)+len(b)) or not model.frontier:
            return dict(surface_filler=False, obstruction='exhausted meeting frames')
        if radius == r:
            return dict(surface_filler=None, meeting_radius=r, frames=len(model.seen))
        model.grow()
        r += 1


def checks():
    from semistrict_surface_private_three_windings import solve as three
    from semistrict_surface_single_power import spellings
    from semistrict_surface_private_winding import solve as winding
    n = 3
    base = dict(edges={}, initial=[], start_vertex=0, scalar_at={'s': 0},
                marks={'s': [[], []]}, higher=[{'p': ['s', 's']}], history=[(0, 's')]*n)
    movies = {}
    for pure in spellings((1, 2, 1)*2):
        for a in (0, 2, 4, 6):
            for b in {a, 6}:
                for i in range(n):
                    for j in range(n):
                        w = [('X', g-1) for g in pure]
                        w.insert(b, ('p', j))
                        w.insert(a, ('p', i))
                        records = cuts(n, w)[0]
                        movies[tuple(records.items())] = w
    all_frames = {f for w in movies.values() for f in old_frames(n, w)}
    chart = Meetings(n, all_frames)
    quotient = ReflectionQuotient(range(n), 3)
    pairs = inhabited = excluded = 0
    for s, a in movies.items():
        for t, b in movies.items():
            if {k for k, _ in s} != {k for k, _ in t}:
                continue
            data = dict(base, source=a, target=b)
            if winding(data)['obstruction']:
                continue
            expected = three(data)['surface_filler']
            possible = all(transport(c, dict(t)[m]) for m, c in s)
            proof = meeting_path(chart.at, dict(s), dict(t), transport) if possible else None
            good = proof is not None
            if good:
                verify(dict(s), dict(t), proof, n)
            assert good == expected
            allowed = quotient.accepts(a, b)
            assert allowed or not expected
            pairs += 1
            inhabited += expected
            excluded += not allowed
    four = dict(base, history=[(0, 's')]*4)
    def movie(tokens):
        return [('X', x-1) if x > 0 else ('p', -x) for x in tokens]+[('X', 0)]*4
    data = dict(four, source=movie((0, 2, 1, 0, 3, 2, 1, -3, 3)),
                target=movie((2, 3, -3, 1, 2, 3, 0, -3, 1)))
    assert solve(data, 0)['surface_filler'] is None
    proof = solve(data, 3)
    assert proof['surface_filler'] and proof['meeting_radius'] == 3
    print(f'{pairs} full-twist comparisons passing the winding test: {inhabited} actual '
          f'comparisons, {excluded} finite-quotient exclusions; all meeting answers '
          'agree with the complete three-event solver.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces', type=Path)
    parser.add_argument('--radius', type=int)
    parser.add_argument('--modulus', type=int, action='append')
    args = parser.parse_args()
    if args.faces:
        data = json.loads(args.faces.read_text())
        # Keep the optional finite model modest on unfiltered large inputs.
        moduli = args.modulus
        if moduli is None:
            n = len(data['history'])
            marks = sum(op != 'X' for op, _ in data['source'])
            moduli = (1, 3) if n <= 3 and marks <= 2 else ((1,) if n <= 4 and marks <= 3 else ())
        print(json.dumps(solve(data, args.radius, moduli)))
    else:
        checks()
