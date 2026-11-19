"""Exhaustive finite checks for Researcher Response 5 on relative coherence.

Every wire has the same generating type. An ordinary gate is identified by
its type and ordered incoming wire occurrences. Its outputs have distinct port
numbers. Since every gate has an input and an output, the final frontier then
determines the whole planar circuit up to interchange.
"""
from collections import Counter, defaultdict
from functools import cache
from itertools import product


ARITY = {
    "a": (1, 1), "b": (1, 1), "s": (1, 2), "r": (2, 1), "p": (3, 2),
    "U": (1, 1), "A": (3, 2), "B": (3, 2), "V": (3, 2), "W": (3, 2),
}
# Each replacement face is an ordinary gate applied at the indicated port.
FACES = {
    "U": (("a", 0), ("b", 0)),
    "A": (("r", 0), ("p", 0)),
    "B": (("r", 1), ("p", 0)),
    "V": (("r", 0), ("r", 0)),
    "W": (("r", 1), ("r", 1)),
}


class Circuits:
    def __init__(self, inputs, faces):
        self.inputs = tuple(range(-inputs, 0))
        self.faces = faces
        self.outputs = {}
        self.producers = {}
        self.markers = {wire: frozenset() for wire in self.inputs}

    def apply(self, gate, offset, frontier):
        n, m = ARITY[gate]
        ports = frontier[offset:offset + n]
        assert len(ports) == n
        key = gate, ports
        if key not in self.outputs:
            start = len(self.producers)
            outputs = tuple(range(start, start + m))
            self.outputs[key] = outputs
            markers = frozenset().union(*(self.markers[port] for port in ports))
            if gate in self.faces:
                markers = markers | {key}
            for i, wire in enumerate(outputs):
                self.producers[wire] = key, i
                self.markers[wire] = markers
        return frontier[:offset] + self.outputs[key] + frontier[offset + n:]

    def enumerate(self, bound):
        alphabet = ("a", "b", "s", "r", "p", *self.faces)
        layer = {self.inputs}
        for size in range(bound + 1):
            next_layer = set()
            for frontier in layer:
                markers = frozenset().union(*(self.markers[wire] for wire in frontier))
                yield frontier, sorted(markers)
                if size < bound:
                    for gate in alphabet:
                        for offset in range(len(frontier) + 1 - ARITY[gate][0]):
                            next_layer.add(self.apply(gate, offset, frontier))
            layer = next_layer

    def expand(self, frontier, choices, retain=None):
        @cache
        def wire_image(wire):
            if wire < 0:
                return wire
            key, i = self.producers[wire]
            return node_image(key)[i]

        @cache
        def node_image(key):
            gate, ports = key
            ports = tuple(wire_image(port) for port in ports)
            if gate in self.faces and key != retain:
                gate, offset = self.faces[gate][choices[key]]
                return self.apply(gate, offset, ports)
            return self.apply(gate, 0, ports)

        return tuple(wire_image(wire) for wire in frontier)


def audit_links(inputs, bound, rules):
    diagrams = Circuits(inputs, {gate: FACES[gate] for gate in rules})
    corners = defaultdict(Counter)
    for frontier, markers in diagrams.enumerate(bound):
        for signs in product(range(2), repeat=len(markers)):
            choices = dict(zip(markers, signs))
            vertex = diagrams.expand(frontier, choices)
            germs = frozenset((choices[key], diagrams.expand(frontier, choices, key))
                              for key in markers)
            assert len(germs) == len(markers)
            corners[vertex][germs] += 1

    multiple, missing, sizes = Counter(), Counter(), Counter()
    for counts in corners.values():
        germs = sorted(next(iter(face)) for face in counts if len(face) == 1)
        for face, n in counts.items():
            sizes[len(face)] += n
            if n > 1:
                multiple[len(face)] += 1
        # A minimal missing clique extends an actual face by its largest germ.
        for base in counts:
            for germ in germs:
                if base and germ <= max(base):
                    continue
                if all(frozenset([germ, other]) in counts for other in base):
                    if base | {germ} not in counts:
                        missing[len(base) + 1] += 1
    return sizes, multiple, missing


def two_event_components(inputs, bound, rules):
    faces = {gate: FACES[gate] for gate in rules}
    # Put the idle faces of A and B at the same intermediate serial state.
    faces["A"] = tuple(reversed(faces["A"]))
    diagrams = Circuits(inputs, faces)
    neighbors = defaultdict(list)
    for frontier, markers in diagrams.enumerate(bound):
        if len(markers) != 2:
            continue
        start = dict.fromkeys(markers, 0)
        end = dict.fromkeys(markers, 1)
        a, b = markers
        ab = diagrams.expand(frontier, start, a), diagrams.expand(frontier, end, b)
        ba = diagrams.expand(frontier, start, b), diagrams.expand(frontier, end, a)
        neighbors[ab].append(ba)
        neighbors[ba].append(ab)

    result = Counter()
    seen = set()
    for vertex in neighbors:
        if vertex in seen:
            continue
        stack, degrees = [vertex], []
        seen.add(vertex)
        while stack:
            current = stack.pop()
            degrees.append(len(neighbors[current]))
            for adjacent in neighbors[current]:
                if adjacent not in seen:
                    stack.append(adjacent)
                    seen.add(adjacent)
        result[tuple(sorted(degrees))] += 1
    return result


def main():
    for inputs, bound, rules in [(5, 3, "UA"), (5, 3, "UAB"), (4, 4, "UA")]:
        sizes, multiple, missing = audit_links(inputs, bound, rules)
        print(inputs, bound, rules, "corners", sorted(sizes.items()),
              "multiple", sorted(multiple.items()), "missing", sorted(missing.items()))
        assert not missing and sizes[bound] > 0
        if "B" in rules:
            assert multiple[2] == 33
        else:
            assert not multiple

    for rules in ["UA", "UAB", "UABVW"]:
        counts = two_event_components(5, 3, rules)
        print(rules, "two-event components incident to an exchange", sorted(counts.items()))
        assert counts[(1, 1)] and counts.keys() <= {(1, 1), (1, 1, 2), (2, 2)}
        assert bool(counts[(1, 1, 2)]) == ("B" in rules)
        assert bool(counts[(2, 2)]) == ("V" in rules)


if __name__ == "__main__":
    main()
