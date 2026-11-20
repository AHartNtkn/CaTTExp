"""Project the subdivided simplex boundary onto one relabelled five-cube."""
from collections import Counter
from itertools import combinations

from relative_coherence_simplex_carrier import facets, face_cubes, nonzero


def vertex_names(anchor, axes):
    """Minimum of each subset in the Boolean interval over its singleton."""
    return tuple(min([anchor] + [i for bit, i in enumerate(axes) if mask >> bit & 1])
                 for mask in range(1 << len(axes)))


def relabel(names, collapsed):
    return tuple(0 if x in collapsed else x for x in names)


def alternating(names, colours):
    terms = Counter()
    for size in range(len(colours) + 1):
        for subset in combinations(colours, size):
            terms[relabel(names, subset)] += (-1) ** size
    return nonzero(terms)


def face_names(names, axis, side):
    return tuple(x for mask, x in enumerate(names) if (mask >> axis & 1) == side)


def check(degree):
    ranks = tuple(range(degree + 1))
    colours = ranks[1:]
    surviving = []
    for face, face_sign in facets(ranks):
        for (anchor, _), piece_sign in face_cubes(face):
            axes = tuple(i for i in face if i != anchor)
            values = vertex_names(anchor, axes)
            projected = alternating(values, colours)
            if projected:
                surviving.append((face, anchor, face_sign * piece_sign, projected))
    (face, anchor, orientation, chain), = surviving
    assert (face, anchor) == (colours, degree)
    assert orientation == (-1) ** (degree - 1)
    assert len(chain) == 2 ** degree and set(chain.values()) == {-1, 1}

    # Keep the original facet index and side fixed during each cancellation.
    # Equality of labels on that facet gives equality on its entire bracket map.
    faces = 0
    for axis in range(degree - 1):
        for side in (0, 1):
            boundary = Counter()
            for names, sign in chain.items():
                boundary[face_names(names, axis, side)] += sign
            assert not nonzero(boundary)
            faces += 1
    # Check each collapse separately on the surviving chain, including its signs.
    for colour in colours:
        projected = Counter()
        for names, sign in chain.items():
            projected[relabel(names, (colour,))] += sign
        assert not nonzero(projected)
    print(f"{degree + 1} ranks: {degree * (degree + 1)} top cubes, "
          f"1 survivor, {len(chain)} distinct vertex labellings, "
          f"{faces} separate facet cancellations, coefficient {orientation:+d}.")


if __name__ == "__main__":
    for degree in range(2, 7):
        check(degree)
