"""Check the last-step complexes in homotopy-polygraphs-r3, Response 1."""

from collections import Counter, defaultdict
from itertools import combinations

from relative_coherence_spherical_fibres import ring
from relative_coherence_strip_fibres import Complex, events, substitute


def last_step_complex(histories, rules, component):
    """Group strings by their last chart and by the strict class of their prefix."""
    neighbors = defaultdict(set)
    for index in component:
        last = histories.cells[index][-1]
        for facet in histories.facets[index]:
            if histories.cells[facet][-1] == last:
                neighbors[index].add(facet)
                neighbors[facet].add(index)

    prefix_class = {}
    for index in sorted(component):
        if index in prefix_class:
            continue
        prefix_class[index] = index
        stack = [index]
        while stack:
            for neighbor in neighbors[stack.pop()]:
                if neighbor not in prefix_class:
                    prefix_class[neighbor] = index
                    stack.append(neighbor)

    def omit_slot(index, slot):
        *prefix, chart = histories.cells[index]
        others = events(chart) - {slot}
        first = substitute(chart, rules, {slot}, 0)
        final = substitute(chart, rules, others, 1)
        split = tuple(prefix) + (first, final)
        return prefix_class[histories.index[split]]

    # Compute every incidence on every representative, including multiplicity.
    faces = {}
    for index in component:
        slots = events(histories.cells[index][-1])
        boundary = tuple(omit_slot(index, slot) for slot in sorted(slots)) if len(slots) > 1 else ()
        key = prefix_class[index]
        if key in faces:
            assert faces[key] == boundary
        faces[key] = boundary
    return faces


def vertex_sets(faces):
    """Check that each simplex embeds and every abstract face has one incidence."""
    by_vertices = {}
    vertices = {}
    for cell, boundary in sorted(faces.items(), key=lambda pair: len(pair[1])):
        slots = frozenset().union(*(vertices[face] for face in boundary)) if boundary else frozenset({cell})
        if boundary:
            assert len(slots) == len(boundary)
            assert {vertices[face] for face in boundary} == {slots - {slot} for slot in slots}
        assert slots not in by_vertices
        by_vertices[slots] = cell
        vertices[cell] = slots
    return set(by_vertices)


def check_example(data, seams):
    initial, final, rules, well_typed = data
    histories = Complex(initial, final, rules, well_typed)
    component, = histories.components
    simplices = vertex_sets(last_step_complex(histories, rules, component))
    vertices = set().union(*simplices)
    opposite = {frozenset(pair) for pair in combinations(vertices, 2) if frozenset(pair) not in simplices}
    if seams:
        assert len(vertices) == 2 * seams
        assert Counter(v for pair in opposite for v in pair) == Counter({v: 1 for v in vertices})
        expected_betti = (1,) + (0,) * (seams - 2) + (1,)
    else:
        assert len(vertices) == 2 and not opposite
        expected_betti = (1,)
    expected_faces = {
        frozenset(face)
        for size in range(1, len(vertices) + 1)
        for face in combinations(vertices, size)
        if not any(pair.issubset(face) for pair in opposite)
    }
    assert simplices == expected_faces
    assert histories.betti(component) == expected_betti
    counts = sorted(Counter(len(face) - 1 for face in simplices).items())
    print(f"{len(component)} chart strings, last-step faces {counts}, full mod-two Betti numbers {expected_betti}")


def check_repeated_deletion():
    # A:a -> 1_f. The two final unary charts are literally the same word.
    def charts(word):
        for size in range(1, len(word) + 1):
            for marked in combinations(range(len(word)), size):
                yield "".join("h" if i in marked else gate for i, gate in enumerate(word))

    def histories(word):
        if not word:
            yield ()
        for chart in charts(word):
            for rest in histories(chart.replace("h", "")):
                yield (chart,) + rest

    strings = set(histories("aa"))
    assert strings == {("hh",), ("ha", "h"), ("ah", "h")}
    terminal_pairs = {(string[:-1], string[-1]) for string in strings if len(string) == 2}
    full = "hh"
    faces = set()
    for cut in range(len(full)):
        first = "".join("h" if i == cut else "a" for i in range(len(full)))
        last = full[:cut] + full[cut + 1:]
        faces.add(((first,), last))
    assert faces == terminal_pairs and len(faces) == 2
    assert {last for _, last in faces} == {"h"}
    print("Repeated deletion: one terminal unary chart, two strict prefixes, one joining edge")


if __name__ == "__main__":
    for seam_count in (2, 3):
        check_example(ring(seam_count), seam_count)
    # A has an identity source on the first wire. B is an endomorphism on the second.
    check_example((("", "b"), ("a", "b"), {"A": {0: ("", "a")}, "B": {1: ("b", "b")}}, None), 0)
    check_repeated_deletion()
