"""Finite checks for the time-simplex and coefficient constructions in HPOL r5."""

from itertools import combinations, combinations_with_replacement, product


def last_face(history):
    """Interior vertex states are 0 (absent), 1 (inside a bead), or 2 (joint)."""
    start = max(i for i, state in enumerate(history) if state == 2 and i < len(history) - 1)
    return tuple(i for i in range(start, len(history)) if history[i])


def refines(source, target):
    return all(a == b or a == 1 for a, b in zip(source, target))


def least_face(history, face):
    start = face[0]
    return history[:start] + tuple(
        2 if i in (start, len(history) - 1) else int(i in face)
        for i in range(start, len(history))
    )


def check_comma(length):
    histories = [(2,) + inner + (2,) for inner in product(range(3), repeat=length - 1)]
    final_faces = {last_face(x) for x in histories}
    checked = 0
    for face in final_faces:
        exact = [x for x in histories if last_face(x) == face]
        # The exact fibre is freely obtained by appending the selected final bead.
        assert len(exact) == (3 ** (face[0] - 1) if face[0] else 1)
        for x in histories:
            if not set(face).issubset(last_face(x)):
                continue
            y = least_face(x, face)
            assert y in exact and refines(x, y)
            for z in exact:
                assert refines(y, z) == refines(x, z)
            checked += 1
    print(f'{length}-simplex: {len(histories)} strings, {len(final_faces)} final faces, '
          f'{checked} comma objects satisfy the adjunction')


def pullback(counts, vertices):
    return tuple(sum(counts[a:b]) for a, b in zip(vertices, vertices[1:]))


def check_scalar_colours():
    # In a free commutative scalar monoid there is only a multiplicity at each cut.
    # There are no slot names. Both constant faces in this example are the unit.
    checked = 0
    for counts in product(range(3), repeat=3):
        for vertices in combinations_with_replacement(range(4), 4):
            first = pullback(counts, vertices)
            for selected in combinations_with_replacement(range(4), 3):
                direct = pullback(counts, tuple(vertices[i] for i in selected))
                assert direct == pullback(first, selected)
                # Quotient of the vertex ordinal by its zero edges.
                projection = (0,) + tuple(sum(v > 0 for v in first[:i]) for i in range(1, 4))
                reduced = tuple(v for v in first if v)
                assert pullback(reduced, tuple(projection[i] for i in selected)) == direct
                checked += 1
    print(f'Scalar charts: {checked} composite restrictions commute with idle-edge quotients')


def order_complex_betti(elements, below):
    """Enumerate strict flags and row-reduce their boundary maps over F_2."""
    chains = [(e,) for e in elements]
    dimensions, ranks = [], [0]
    while chains:
        dimensions.append(len(chains))
        indices = {chain: i for i, chain in enumerate(chains)}
        longer = [c + (e,) for c in chains for e in elements if below(c[-1], e)]
        pivots = {}
        for chain in longer:
            column = sum(1 << indices[face] for face in combinations(chain, len(chain) - 1))
            while column:
                pivot = column.bit_length() - 1
                if pivot not in pivots:
                    pivots[pivot] = column
                    break
                column ^= pivots[pivot]
        ranks.append(len(pivots))
        chains = longer
    return tuple(d - ranks[i] - ranks[i + 1] for i, d in enumerate(dimensions))


def check_coefficients():
    # The two middle-wire tiles have two distinct common ends.
    circle = ('tile A', 'tile B', 'end A', 'end B')

    def face(x, y):
        return x.startswith('tile') and y.startswith('end')

    assert order_complex_betti(circle, face) == (1, 1)
    # A single last bead of weight one has only its identity incidence.
    # For a length-two bead use the two distinct D-faces, with point coefficients.
    # Each constant restriction makes one cone in the Grothendieck construction.
    cones = ('diagonal', 'suffix')
    def decorated(x, y):
        return face(x, y) or (x in circle and y in cones)

    assert order_complex_betti(circle + cones, decorated) == (1, 0, 1)
    assert order_complex_betti(('chart',) + cones, lambda x, y: x == 'chart' and y in cones) == (1, 0)
    print('Marked circle: Betti (1, 1); two constant face maps: (1, 0, 1); point control: (1, 0)')


if __name__ == '__main__':
    check_comma(5)
    check_scalar_colours()
    check_coefficients()
