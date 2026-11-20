"""Compare strict labels, terminal chart complexes, and passive wire folds in HPOL r5."""

from collections import Counter

from homotopy_polygraph_last_steps import last_step_complex
from relative_coherence_strip_fibres import Complex


def count_components(initial, final, left_input):
    rules = {'A': {0: ('a', 'x'), 1: (left_input, '')},
             'B': {1: ('', ''), 2: ('b', 'y')}}
    histories = Complex(('a', initial, 'b'), ('x', final, 'y'), rules)
    signatures = Counter()
    for component in histories.components:
        faces = last_step_complex(histories, rules, component)
        vertices = {i for i, boundary in faces.items() if not boundary}
        edges = [boundary for boundary in faces.values() if boundary]
        assert all(len(edge) == 2 and set(edge) <= vertices for edge in edges)
        assert histories.betti(component) == ((1, 1) if len(edges) == len(vertices) else (1,))
        signatures[len(vertices), len(edges)] += 1
    return signatures


def check_passive_words():
    # In the read/read example, the two cuts in the passive word survive every swap.
    # Distinct gaps give exactly one exchange, a common gap gives both spatial orders.
    for size in range(13):
        word = 't' * size
        expected = Counter({(2, 2): size + 1})
        if size:
            expected[2, 1] = size * (size + 1)
        assert count_components(word, word, '') == expected

    # Removing d merges its incident wire segments. In a component at the merged
    # gap, the other event can read before or after d in the incoming state.
    # The two exchanges have a common serial endpoint in the outgoing state.
    folds = 0
    for left in range(7):
        for right in range(7):
            initial = 't' * left + 'd' + 't' * right
            expected = Counter({(3, 2): 1})
            if left + right:
                expected[2, 1] = left + right
            assert count_components(initial, initial.replace('d', ''), 'd') == expected
            folds += 1
    print(f'Checked 13 passive word lengths and {folds} folded-wire placements.')
    print('At length 12 the 169 read/read labels give 13 circles and 156 intervals.')


if __name__ == '__main__':
    check_passive_words()
