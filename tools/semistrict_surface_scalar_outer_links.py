"""Compare simultaneous named rows of changing planar diagrams with their signed links."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import cache
from itertools import combinations, product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from relative_coherence_local_links import Circuits
from semistrict_surface_spatial_frames import flag_check

# Each face is a word of ordinary gates at local offsets, read on actual ports.
ARITY = {'s': (1, 2), 'r': (2, 1), 'a': (1, 1), 'b': (1, 1),
         'R': (2, 2), 'T': (1, 1), 'V': (1, 2)}
FACES = {'R': ((), (('r', 0), ('s', 0))),
         'T': ((('a', 0),), (('s', 0), ('r', 0))),
         'V': ((('s', 0),), (('a', 0), ('s', 0)))}


@dataclass(frozen=True)
class Rod:
    name: str
    offset: int
    used: frozenset
    outputs: tuple


def advance_faces(gaps, gate, ports, offset):
    inputs, outputs = ARITY[gate]
    born = tuple((gate, ports, i) for i in range(1, outputs))
    return gaps[:offset+1] + born + gaps[offset+inputs:]


class Diagram:
    def __init__(self, width, serial):
        self.circuits = Circuits(width, {}, ARITY)
        self.order = []
        front = self.circuits.inputs
        for g, i in serial:
            ports = front[i:i+ARITY[g][0]]
            self.order.append((g, ports))
            front = self.circuits.apply(g, i, front)
        self.end = front
        self.nodes = frozenset(self.order)

    def cuts(self):
        start = self.circuits.inputs
        todo = [(frozenset(), start, tuple(('bottom', i) for i in range(len(start)+1)))]
        seen = {}
        while todo:
            used, front, gaps = todo.pop()
            if used in seen:
                assert seen[used] == (front, gaps)
                continue
            seen[used] = front, gaps
            yield used, front, gaps
            for g, ports in self.nodes - used:
                if ports[0] not in front:
                    continue
                i = front.index(ports[0])
                if front[i:i+len(ports)] == ports:
                    todo.append((used | {(g, ports)}, self.circuits.apply(g, i, front),
                                 advance_faces(gaps, g, ports, i)))

    def rods(self, front, name, sign):
        width = ARITY[name][0]
        for i in range(len(front)+1-width):
            local = front[i:i+width]
            used = set()
            for g, j in FACES[name][sign]:
                ports = local[j:j+ARITY[g][0]]
                if (g, ports) not in self.nodes:
                    break
                used.add((g, ports))
                local = self.circuits.apply(g, j, local)
            else:
                yield Rod(name, i, frozenset(used), local)

    @cache
    def chart(self, before, front, rods):
        # Build the marked circuit itself. Contract each chosen expansion and
        # replay every remaining ordinary gate on the corresponding named ports.
        used = set(before)
        images = {p: p for p in front}
        for rod in rods:
            n = ARITY[rod.name][0]
            ports = front[rod.offset:rod.offset+n]
            marked = self.circuits.apply(rod.name, 0, ports)
            images.update(zip(rod.outputs, marked, strict=True))
            used.update(rod.used)
        for g, ports in self.order:
            if (g, ports) not in used:
                marked = self.circuits.apply(g, 0, tuple(images[p] for p in ports))
                images.update(zip(self.circuits.outputs[g, ports], marked, strict=True))
        return tuple(images[p] for p in self.end)


def row_sets(d, signs):
    actual = defaultdict(set)
    for before, front, gaps in d.cuts():
        options = [[None, *d.rods(front, name, sign)] for name, sign in zip(FACES, signs)]
        for selection in product(*options):
            rods = tuple(r for r in selection if r is not None)
            blocks = [(r.offset, r.offset+ARITY[r.name][0]) for r in rods]
            if any(a < e and c < b for (a, b), (c, e) in combinations(blocks, 2)):
                continue
            positive = frozenset((r.name, d.chart(before, front, (r,))) for r in rods)
            chart = d.chart(before, front, rods)
            open_faces = [face for k, face in enumerate(gaps)
                          if all(not a < k < b for a, b in blocks)]
            for left, right in product([None, *open_faces], repeat=2):
                scalars = tuple((name, face) for name, face in zip('xy', (left, right))
                                if face is not None)
                germs = positive.union(scalars)
                actual[germs].add((chart, scalars))
    return actual


def typed_changes(destination):
    ctx = (STAR, arr(STAR, v(0), v(0)))
    edge = v(1)
    pair = comp2(ctx, 0, edge, edge)

    def change(source, target):
        assert infer(ctx, source) == infer(ctx, target)
        return arr(infer(ctx, source), source, target)

    ctx += (change(edge, pair), change(pair, edge), change(edge, edge), change(edge, edge))
    split, merge, unary = v(2), v(3), v(4)
    scalar_pole = identity(ctx, identity(ctx, v(0)))
    ctx += (change(identity(ctx, pair), comp2(ctx, 1, merge, split)),
            change(unary, comp2(ctx, 1, split, merge)),
            change(split, comp2(ctx, 1, unary, split)),
            change(scalar_pole, scalar_pole), change(scalar_pole, scalar_pole))
    check_ctx(ctx)
    middle = comp2(ctx, 0, comp2(ctx, 0, edge, comp2(ctx, 2, v(9), v(10))), edge)
    ty = infer(ctx, middle)
    if destination:
        e = Emitter()
        for i, name in enumerate(('rodR', 'rodT', 'rodV', 'scalarX', 'scalarY'), start=6):
            e.check_type(name, ctx, v(i), ctx[i])
        e.check_type('twoAtMiddleVertex', ctx, middle, ty)
        g = e.ctx(ctx)
        e.checks.append(f'typed : {g} ⊢ctx\ntyped = from-just (checkCtx {g})\n')
        (destination / 'ScalarOuterLinks.agda').write_text(e.module('ScalarOuterLinks', __doc__))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    typed_changes(args.agda_dir)
    cases = [
        (0, ()),
        (3, (('r', 0), ('s', 0), ('a', 2))),
        (3, (('s', 1), ('a', 0), ('r', 1), ('s', 1), ('b', 3), ('r', 1))),
        (4, (('a', 0), ('s', 0), ('r', 2), ('s', 2), ('a', 4))),
    ]
    totals = Counter()
    checks = Counter()
    for width, serial in cases:
        d = Diagram(width, serial)
        for signs in product((0, 1), repeat=len(FACES)):
            actual = row_sets(d, signs)
            totals.update(dict(flag_check({0: {gs: len(frames) for gs, frames in actual.items()}})))
            for germs in actual:
                by_name = dict(germs)
                if 'x' in by_name and by_name.get('y') == by_name['x']:
                    checks['same-face scalar pair'] += 1
                if len(germs) == 5:
                    checks['three rods and two scalars'] += 1
            if width == 3 and serial[0] == ('s', 1):
                # Two bounded faces are born by successive splits at the same
                # seam. No row contains a point inside each at the same time.
                births = [(g, ports, 1) for g, ports in d.order if g == 's']
                x, y = ('x', births[0]), ('y', births[1])
                assert frozenset([x]) in actual and frozenset([y]) in actual
                assert frozenset([x, y]) not in actual
                checks['incompatible scalar pair at successive lenses'] += 1
    assert all(checks[k] for k in ('same-face scalar pair', 'three rods and two scalars',
                                    'incompatible scalar pair at successive lenses'))
    print('unique signed corners by dimension:', sorted(totals.items()))
    print('all pairwise-compatible cliques filled;', dict(checks))


if __name__ == '__main__':
    main()
