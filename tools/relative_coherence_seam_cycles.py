"""Compare the full typed history complex with its cubical visible-sign image."""
from collections import Counter
from itertools import combinations, product
from graphlib import CycleError, TopologicalSorter

from relative_coherence_coloured_faces import visible
from relative_coherence_strip_fibres import Complex


def two_bridges():
    # In order along the line: four signals alternating with three seams.
    signals = ("ZA", "BYC", "DZE", "FY")
    rules = {event: {} for event in "ABCDEFYZ"}
    initial, final, types = [], [], []
    for lane in range(7):
        if lane % 2:
            seam = lane // 2
            deletion, insertion = "ABCDEF"[2 * seam:2 * seam + 2]
            rules[deletion][lane] = ("d", "")
            rules[insertion][lane] = ("", "e")
            arrows = {letter: ("p", "p") for letter in ("d", "e", deletion, insertion)}
            entry = exit_edge = "p"
            first, last = "d", "e"
        else:
            steps = signals[lane // 2]
            states = "lmnr"[:len(steps) + 1]
            for event, before, after in zip(steps, states, states[1:]):
                rules[event][lane] = (before, after)
            entry, exit_edge = "u", "v"
            arrows = {letter: (entry, exit_edge) for letter in states + steps}
            first, last = states[0], states[-1]

        arrows["t"] = ("q", entry)
        arrows["w"] = (exit_edge, "r")
        for reader, gap, covered in (("Z", "q", range(5)), ("Y", "r", range(2, 7))):
            if lane in covered and lane not in rules[reader]:
                rules[reader][lane] = ("", "")
                arrows[reader] = (gap, gap)
        types.append(arrows)
        initial.append("t" + first + "w")
        final.append("t" + last + "w")

    def well_typed(tier):
        for word, arrows in zip(tier, types):
            edge = "q"
            for letter in word:
                source, target = arrows[letter]
                if source != edge:
                    return False
                edge = target
            if edge != "r":
                return False
        return True

    return tuple(initial), tuple(final), rules, well_typed


def compatible(hidden):
    graph = TopologicalSorter()
    for chain in ("ZA", "BYC", "DZE", "FY"):
        for before, after in zip(chain, chain[1:]):
            graph.add(after, before)
    for seam in hidden:
        deletion, insertion = "ABCDEF"[2 * seam:2 * seam + 2]
        graph.add(insertion, deletion)
    try:
        graph.prepare()
    except CycleError:
        return False
    return True


def main():
    obj = Complex(*two_bridges())
    assert len(obj.components) == 1
    signs = [visible(cell, 3) for cell in obj.cells]
    faces = {face for face in product((-1, 0, 1), repeat=3)
             if compatible(i for i in range(3) if face[i] == 0)}
    assert set(signs) == faces
    for i, facets in enumerate(obj.facets):
        for j in facets:
            assert all(y == 0 or x == y for x, y in zip(signs[i], signs[j]))

    # Lower ideals of the order-reversing map consist of histories in which
    # all free coordinates of the specified cubical face are hidden.
    for face in faces:
        ideal = {i for i, sign in enumerate(signs)
                 if all(s == 0 or s == f for s, f in zip(sign, face))}
        assert obj.betti(ideal) == (1,)

    nonfaces = [pair for pair in combinations(range(3), 2) if not compatible(pair)]
    assert nonfaces == [(0, 1), (1, 2)]
    cubical_counts = Counter(face.count(0) for face in faces)
    assert cubical_counts == {0: 8, 1: 12, 2: 2}
    assert obj.betti(obj.components[0]) == (1, 3)
    print("Typed history counts by degree:", sorted(Counter(obj.degrees).items()))
    print("Cubical image:", sorted(cubical_counts.items()), "Betti numbers: (1, 3)")
    print("Checked every facet and all", len(faces), "lower ideals.")


if __name__ == "__main__":
    main()
