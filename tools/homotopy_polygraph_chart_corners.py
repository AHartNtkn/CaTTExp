"""Check spatial orders at signed corners against literal marked planar charts."""

from collections import Counter
from itertools import combinations, permutations, product

from relative_coherence_strip_fibres import lane_charts, substitute


def frames(state, names, rules, typed_lane=lambda lane, word: True):
    """Enumerate a tier by spatial serialization, independent of any corner tests."""
    found = set()
    for order in permutations(names):
        lanes = []
        for i, word in enumerate(state):
            local_order = [k for k in order if i in rules[k]]
            words = lane_charts(word, local_order, rules, i)
            lanes.append([w for w in words if typed_lane(i, w)])
        found.update(product(*lanes))
    return found


def verify_corner(state, rules, expected):
    names = tuple(sorted(rules))
    single = {}
    for k in names:
        germ, = frames(state, (k,), rules)
        single[k] = germ
    # Choose the signed unary germs first. The test inputs have one per name.
    pairs = tuple(combinations(names, 2))
    choices = [sorted(frames(state, pair, rules)) for pair in pairs]
    assert all(1 <= len(pair_choices) <= 2 for pair_choices in choices)
    for pair, options in zip(pairs, choices):
        assert all(substitute(tier, rules, {k}, 0) == single[k] for tier in options for k in pair)

    def bits(tier, indices):
        return tuple(choices[i].index(substitute(tier, rules, pairs[i], 0)) for i in indices)

    triples = []
    for triple in combinations(names, 3):
        indices = [i for i, pair in enumerate(pairs) if set(pair) <= set(triple)]
        assert sum(len(choices[i]) == 2 for i in indices) <= 2
        triples.append((indices, {bits(t, indices) for t in frames(state, triple, rules)}))
    predicted = {b for b in product(*(range(len(opt)) for opt in choices))
                 if all(tuple(b[i] for i in indices) in allowed for indices, allowed in triples)}
    actual = frames(state, names, rules)
    assert {bits(t, range(len(pairs))) for t in actual} == predicted
    assert len(actual) == len(predicted) == expected
    for a, b, c in combinations(predicted, 3):
        assert tuple(int(i + j + k >= 2) for i, j, k in zip(a, b, c)) in predicted
    for a in predicted:
        for b in predicted - {a}:
            assert any(a[:i] + (b[i],) + a[i + 1:] in predicted
                       for i in range(len(a)) if a[i] != b[i])
    return len(actual), [p for p, opt in zip(pairs, choices) if len(opt) == 2]


def examples():
    # C's left active port precedes A, while its right active port follows B.
    # A and B each insert on the middle wire, giving two distinct opposite states.
    state = ('ca', '', 'bd')
    rules = {'A': {0: ('a', 'f'), 1: ('', 'x')},
             'B': {1: ('', 'y'), 2: ('b', 'g')},
             'C': {0: ('c', 'h'), 1: ('', ''), 2: ('d', 'k')}}
    _, ambiguous = verify_corner(state, rules, 1)
    assert ambiguous == [('A', 'B')]
    assert {substitute(t, rules, set(), 1)[1]
            for t in frames(state, ('A', 'B'), rules)} == {'xy', 'yx'}
    # B and C both reach across A's idle right port. Their active ports share
    # the right lane and have a prescribed order. Exactly three of four sign
    # choices survive. Reversing the substitutions checks a mixed signed corner.
    state = ('a', '', 'bc')
    rules = {'A': {0: ('a', 'f'), 1: ('', '')},
             'B': {1: ('', ''), 2: ('b', 'g')},
             'C': {1: ('', ''), 2: ('c', 'h')}}
    assert verify_corner(state, rules, 3)[1] == [('A', 'B'), ('A', 'C')]
    rules['B'] = {i: (t, s) for i, (s, t) in rules['B'].items()}
    assert verify_corner(('a', '', 'gc'), rules, 3)[1] == [('A', 'B'), ('A', 'C')]
    # Five private active gates, four intervening shared idle wires.
    state = tuple('a' if i % 2 == 0 else '' for i in range(9))
    rules = {k: {j: (state[j], state[j]) for j in range(max(0, 2 * i - 1), min(9, 2 * i + 2))}
             for i, k in enumerate('ABCDE')}
    assert len(verify_corner(state, rules, 16)[1]) == 4
    print('Chart corners: one forced sign, a three-vertex median path in both orientations, '
          'and all sixteen vertices of a four-cube.')


def all_three_lane_germs():
    state = ('a', 'b', 'c')
    names = 'ABC'
    intervals = [[range(left, right + 1) for left in range(i + 1) for right in range(i, 3)]
                 for i in range(3)]
    families = feasible = multiple = 0
    for supports in product(*intervals):
        rules = {name: {j: (state[j], state[j]) if i == j else ('', '') for j in lanes}
                 for i, (name, lanes) in enumerate(zip(names, supports))}

        def germs(chart, members):
            return tuple(substitute(chart, rules, {k}, 0) for k in members)

        singles = [frames(state, (k,), rules) for k in names]
        pairs = {(i, j): {germs(chart, (names[i], names[j]))
                          for chart in frames(state, (names[i], names[j]), rules)}
                 for i, j in combinations(range(3), 2)}
        joints = Counter(germs(chart, names) for chart in frames(state, names, rules))
        for family in product(*singles):
            pairwise = all((family[i], family[j]) in corners for (i, j), corners in pairs.items())
            assert pairwise == bool(joints[family])
            families += 1
            feasible += pairwise
            multiple += joints[family] > 1
    print(f'Three lanes: {families} germ families, {feasible} pairwise joint, '
          f'{multiple} with several joint charts.')


if __name__ == '__main__':
    examples()
    all_three_lane_germs()
