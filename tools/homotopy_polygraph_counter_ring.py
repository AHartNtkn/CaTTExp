"""Check the circle after two head instructions, including a run starting inside the tape."""

from relative_coherence_spherical_fibres import ring
from relative_coherence_strip_fibres import Complex


def counter_ring():
    initial, final, rules, old_types = ring(2)
    rules['B'][2] = ('l', '[i]')
    rules['C'][2] = ('[h]', 'r')
    rules['I'] = {2: ('i', 'xj')}
    rules['J'] = {2: ('xj', 'h')}
    tape_types = {
        't': ('q', 'u'), 'l': ('u', 'v'), 'r': ('u', 'v'),
        '[': ('u', 'p'), ']': ('s', 'v'), 'x': ('p', 'p'),
        'i': ('p', 's'), 'j': ('p', 's'), 'h': ('p', 's'),
        'I': ('p', 's'), 'J': ('p', 's'),
        'B': ('u', 'v'), 'C': ('u', 'v'), 'Z': ('q', 'q'),
    }

    def well_typed(tier):
        # The old checker still validates the four unmodified lanes.
        if not old_types(tier[:2] + ('tl',) + tier[3:]):
            return False
        edge = 'q'
        for gate in tier[2]:
            source, target = tape_types[gate]
            if source != edge:
                return False
            edge = target
        return edge == 'v'

    return initial, final, rules, well_typed


def inspect(initial, final, rules, well_typed, expected):
    histories = Complex(initial, final, rules, well_typed)
    component, = histories.components
    assert histories.betti(component) == expected
    # Read the gate order directly from every marked circuit, including split tiers.
    for cell in histories.cells:
        order = [gate for tier in cell for gate in tier[2] if gate in 'BIJC']
        assert order == [gate for gate in 'BIJC' if gate in rules]
        assert all(sum(g in 'BIJC' for g in tier[2]) <= 1 for tier in cell)
    print(f'{len(rules)} changes, {len(component)} chart strings, Betti {expected}')


if __name__ == '__main__':
    initial, final, rules, well_typed = counter_ring()
    inspect(initial, final, rules, well_typed, (1, 1))
    # The same accepting computation already in progress, without the start marker.
    # Its insertion on seam 1 is now an ordinary gate in the incoming diagram.
    partial = (initial[0], 'ted', 't[i]', initial[3], initial[4])
    inspect(partial, final, {k: v for k, v in rules.items() if k != 'B'}, well_typed, (1,))
    # A full ring cannot skip either head instruction, even if the target is prescribed.
    for omitted in 'IJ':
        rest = {k: v for k, v in rules.items() if k != omitted}
        assert not Complex(initial, final, rest, well_typed).cells
    print('Neither instruction can be skipped between the two signal changes.')
