"""Check outer cubes by actual common slices in circuits with empty outputs."""

from collections import Counter, defaultdict
from functools import cache
from itertools import product

from semistrict_surface_spatial_frames import flag_check


# Faces consist of a positioned ordinary gate, with idle wires on either side.
ARITY = {'d': (1, 0), 'e': (1, 0), 'k': (2, 0), 'r': (2, 1), 's': (1, 2),
         'D': (1, 0), 'K': (2, 0), 'R': (2, 1), 'M': (3, 2)}
FACES = {'D': (('d', 0), ('e', 0)), 'K': (('k', 0), ('k', 0)),
         'R': (('r', 0), ('r', 0)), 'M': (('d', 0), ('d', 2))}


class Circuits:
    def __init__(self, width):
        self.inputs = tuple(range(-width, 0))
        self.outputs = {}
        self.next_port = 0

    def step(self, frontier, gate, offset):
        n, m = ARITY[gate]
        inputs = frontier[offset:offset + n]
        assert len(inputs) == n
        node = gate, inputs
        if node not in self.outputs:
            self.outputs[node] = tuple(range(self.next_port, self.next_port + m))
            self.next_port += m
        return node, frontier[:offset] + self.outputs[node] + frontier[offset+n:]

    def charts(self, bound):
        # Keep one serialization per incidence diagram. Dead nodes are stored
        # explicitly since the last frontier does not determine dead branches.
        layer = {(self.inputs, frozenset()): ()}
        for size in range(bound + 1):
            next_layer = {}
            for (frontier, deaths), rows in layer.items():
                yield rows
                if size == bound:
                    continue
                for gate, (n, m) in ARITY.items():
                    for i in range(len(frontier) - n + 1):
                        node, end = self.step(frontier, gate, i)
                        key = end, deaths if m else deaths | {node}
                        next_layer.setdefault(key, rows + ((node, i),))
            layer = next_layer

    def common_slice(self, rows):
        marked = [node for node, _ in rows if node[0] in FACES]
        ordinary = frozenset(node for node, _ in rows if node[0] not in FACES)

        @cache
        def expose(live, unused):
            offsets = {}
            for node in (*marked, *unused):
                _, ports = node
                if ports[0] in live:
                    i = live.index(ports[0])
                    if live[i:i+len(ports)] == ports:
                        offsets[node] = i
            if all(node in offsets for node in marked):
                # Distinct diagram nodes consume disjoint concrete input ports.
                return True
            for node in unused.intersection(offsets):
                _, after = self.step(live, node[0], offsets[node])
                if expose(after, unused - {node}):
                    return True
            return False
        return expose(self.inputs, ordinary)

    def hull_slice(self, rows):
        # Width = paths arriving at this wire times paths continuing from it.
        prefix = dict.fromkeys(self.inputs, 1)
        suffix = {}
        for node, _ in rows:
            arriving = sum(prefix[p] for p in node[1])
            prefix.update(dict.fromkeys(self.outputs[node], arriving))
        for node, _ in reversed(rows):
            continuing = sum(suffix.get(p, 1) for p in self.outputs[node]) or 1
            suffix.update(dict.fromkeys(node[1], continuing))
        lanes = {}
        offset = 0
        for p in self.inputs:
            width = suffix.get(p, 1)
            lanes[p] = tuple(range(offset, offset + width))
            offset += width
        predecessors = []
        for node, _ in rows:
            occupied = tuple(i for p in node[1] for i in lanes[p])
            first, last = occupied[0], occupied[-1]
            follows_mark = any(lo <= last and first <= hi and marked
                               for lo, hi, marked in predecessors)
            marked = node[0] in FACES
            if follows_mark and marked:
                return False
            predecessors.append((first, last, follows_mark or marked))
            offset = 0
            for p in self.outputs[node]:
                width = prefix[p] * suffix.get(p, 1)
                lanes[p] = occupied[offset:offset+width]
                offset += width
            assert not self.outputs[node] or offset == len(occupied)
        return True

    def expand(self, rows, signs, keep=None):
        live, deaths = self.inputs, set()
        for node, offset in rows:
            gate = node[0]
            if gate in FACES and node != keep:
                gate, shift = FACES[gate][signs[node]]
                offset += shift
            actual, live = self.step(live, gate, offset)
            if not self.outputs[actual]:
                deaths.add(actual)
        return live, frozenset(deaths)


def check(width, bound):
    diagrams = Circuits(width)
    corners = defaultdict(Counter)
    denied = 0
    for rows in diagrams.charts(bound):
        common = diagrams.common_slice(rows)
        assert common == diagrams.hull_slice(rows)
        if not common:
            denied += 1
            continue
        marked = [n for n, _ in rows if n[0] in FACES]
        for bits in product(range(2), repeat=len(marked)):
            signs = dict(zip(marked, bits))
            germs = frozenset((signs[n], diagrams.expand(rows, signs, n)) for n in marked)
            assert len(germs) == len(marked)
            corners[diagrams.expand(rows, signs)][germs] += 1
    return flag_check(corners), denied


def gap_control():
    diagrams = Circuits(3)
    death, surviving = diagrams.step(diagrams.inputs, 'D', 1)
    merge, _ = diagrams.step(surviving, 'R', 0)
    assert set(death[1]).isdisjoint(merge[1])
    assert all(port < 0 for port in merge[1])
    assert not diagrams.common_slice(((death, 1), (merge, 0)))
    outside, surviving = diagrams.step(diagrams.inputs, 'D', 2)
    merge, _ = diagrams.step(surviving, 'R', 0)
    assert diagrams.common_slice(((outside, 2), (merge, 0)))


if __name__ == '__main__':
    gap_control()
    for width, bound in ((3, 4), (5, 3)):
        corners, denied = check(width, bound)
        print(f'{width} inputs through {bound} gates: signed common-slice corners {corners}, {denied} excluded frames')
