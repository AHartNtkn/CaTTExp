"""Check the passive-strip reduction by enumerating typed charts and their facets."""

from relative_coherence_spherical_fibres import ring
from relative_coherence_strip_fibres import Complex


def insert_strip(row, value):
    return row[:2] + (value,) + row[2:]


def erase_strip(row):
    return row[:2] + row[3:]


def tape_matches(gates, initial, final, accept):
    # The end brackets denote the two private ports. x -> ab changes wire count.
    rewrites = {
        "i": ("Q", "[xy]"),
        "x": ("x", "ab"),
        "y": ("y", "c"),
        "f": (accept, "U"),
        "Z": ("Q", "Q"),
        "B": ("U", "U"),
    }
    frontiers = {initial}
    for gate in gates:
        source, target = rewrites[gate]
        frontiers = {
            word[:cut] + target + word[cut + len(source):]
            for word in frontiers
            for cut in range(len(word) - len(source) + 1)
            if word.startswith(source, cut)
        }
    return final in frontiers


def enumerate_guarded(data, gates, initial, final, accept="[abc]"):
    start, end, rules, well_typed = data
    extended = {
        name: {(lane if lane < 2 else lane + 1): change for lane, change in columns.items()}
        for name, columns in rules.items()
    }
    for name in {"B", "Z"} & extended.keys():
        extended[name][2] = ("", "")

    def typed(row):
        return well_typed(erase_strip(row)) and tape_matches(row[2], initial, final, accept)

    return Complex(insert_strip(start, gates), insert_strip(end, gates), extended, typed)


def compare(guarded, original):
    def image(cell):
        return tuple(erase_strip(row) for row in cell)

    projection = [original.index[image(cell)] for cell in guarded.cells]
    assert sorted(projection) == list(range(len(original.cells)))
    for i, j in enumerate(projection):
        assert sorted(projection[face] for face in guarded.facets[i]) == sorted(original.facets[j])
    return sorted(guarded.betti(component) for component in guarded.components)


if __name__ == "__main__":
    data = ring(2)
    original = Complex(*data)
    assert len(original.cells) == 96
    # Two serializations of the same passive diagram by strict interchange.
    for gates in ("ixyf", "iyxf"):
        guarded = enumerate_guarded(data, gates, "Q", "U")
        assert compare(guarded, original) == [(1, 1)]
        print(f"{gates}: all 96 chart strings and every facet agree, Betti (1, 1)")

    # An incomplete computation has a Q cut but no U cut.
    incomplete = enumerate_guarded(data, "ix", "Q", "[aby]")
    assert not incomplete.cells
    print("Incomplete tape: no full five-event chart string")

    # x and y each rewrite at most once, so these are all complete tape orders.
    # Neither can close at the permuted target, even with arbitrary marker cuts.
    for gates in ("if", "ixf", "iyf", "ixyf", "iyxf"):
        unreachable = enumerate_guarded(data, gates, "Q", "U", accept="[acb]")
        assert not unreachable.cells
    print("Unreachable target acb: no full string in any tape order")

    # A proper history with B enabled and Z absent, including the ambiguity on a seam.
    start, end, rules, typed = data
    start = ("m",) + start[1:]
    end = end[:-1] + ("m",)
    proper = start, end, {name: columns for name, columns in rules.items() if name != "Z"}, typed
    original_proper = Complex(*proper)
    actual = enumerate_guarded(proper, "", "U", "U")
    assert compare(actual, original_proper) == [(1,)]
    print(f"U only: all {len(actual.cells)} proper chart strings and every facet agree, Betti (1,)")
