"""Finite checks for the row bound, transformation normal form, and wide grid heads."""

from itertools import product

from interchange_cylinders import atom, compose, face
from interchange_double_variation import between


def check_bridge_operands():
    """Read pure operand terms in independently computed Steiner hemisphere chains."""
    checks = 0
    for moving, p, q in product((0, 1), range(3, 8), range(2, 10)):
        def ordered(x, z):
            return (x, z) if moving == 0 else (z, x)

        disks = [atom(ordered((p, i), (q, 2))) for i in (0, 1)]
        flanks = [[], []]
        for a in range(p, p + q + 1):
            reverse = moving == 1 and (a - p) % 2
            bridges = []
            for side in (0, 1):
                ends = []
                for disk, flank in zip(disks, flanks):
                    row = disk
                    while len(row) > a + 1:
                        row = face(row, side)
                    for cut, pad, at_left in flank:
                        row = compose(pad, row, cut) if at_left else compose(row, pad, cut)
                    ends.append(row)
                if reverse:
                    ends.reverse()
                fixed_side = side ^ (p % 2) if moving == 0 else side
                fixed = (a - p, 2 if a == p + q else fixed_side)
                bridges.append(between(*ends, ordered((p + 1, 2), fixed)))
                if a == p:
                    continue
                fixed_rank = min(a, q)
                for end in ends:
                    for slot, rank in ((moving, p + 1), (1 - moving, fixed_rank)):
                        for chain in end[rank]:
                            pure = [pair for pair in chain if pair[slot][0] == rank]
                            assert len(pure) == 1 and pure[0][1 - slot][0] == 0
                            expected_side = side if slot != moving and q > a else 2
                            assert pure[0][slot][1] == expected_side
                            checks += 1
            first = int(reverse)
            flanks[first].append((a, bridges[1], False))
            flanks[1 - first].append((a, bridges[0], True))
    return checks


def product_map(word, assignment):
    result = tuple(range(len(assignment[0])))
    for letter in word:
        result = tuple(assignment[letter][i] for i in result)
    return result


def check_transformations():
    # One vertex, two letters of charge one, cutoff one: N = 4 exactly.
    maps = list(product(range(4), repeat=4))
    counted = equal_before = equal_after = 0
    for assignment in product(maps, repeat=2):
        one, two = (product_map((i,), assignment) for i in (0, 1))
        mask = int(one == two)
        equal_before += one == two
        equal_after += tuple(mask * (1 + i) for i in one) == tuple(mask * (1 + i) for i in two)
        counted += 1
    assert equal_before == len(maps) < counted == equal_after

    # A direct charge-two head c and the paste ab. Use a nontrivial exterior
    # context on both sides, and keep the reverse order ba distinguishable.
    samples = ("aabcb", "accb", "acabb", "abacb", "cab", "cc", "cba")
    expected = [word.replace("c", "ab") for word in samples]
    states = sorted({word[:i] for word in expected for i in range(len(word) + 1)})
    index = {word: i for i, word in enumerate(states)}
    sink = len(states)
    transitions = [tuple(index.get(word + letter, sink) for word in states) + (sink,)
                   for letter in "ab"]
    transitions.append(product_map((0, 1), transitions))
    products = [product_map(tuple("abc".index(c) for c in w), transitions) for w in samples]
    for i, j in product(range(len(samples)), repeat=2):
        assert (products[i] == products[j]) == (expected[i] == expected[j])
    return counted


def check_grid_routes():
    # Entries in a rank-three history are actual named swaps of b_i a_i.
    def replay(history):
        shuffle = [(color, i) for i in sorted(history) for color in "ba"]
        for i in history:
            pos = shuffle.index(("b", i))
            assert shuffle[pos + 1] == ("a", i)
            shuffle[pos:pos + 2] = reversed(shuffle[pos:pos + 2])
        return shuffle

    def crossing(history, left, right):
        # A positive rank-four iota moves a later spatial block after an
        # earlier one. The factor in the current history is right then left.
        assert max(left) < min(right)
        start = history.index(right[0])
        stop = start + len(left) + len(right)
        assert history[start:stop] == right + left
        result = history[:start] + left + right + history[stop:]
        assert replay(history) == replay(result)
        return result

    def route(history, moves):
        states = [history]
        for left, right in moves:
            states.append(crossing(states[-1], left, right))
        return states

    x, y = ((1,), (2,)), ((3,), (4,))
    tests = [
        ((3, 2, 1), [((2, 1), (3,)), x], [x, ((1, 2), (3,))]),
        ((3, 2, 1), [((2,), (3,)), ((1,), (2, 3))],
         [((1,), (3, 2)), ((2,), (3,))]),
        ((4, 3, 2, 1), [y, ((2, 1), (3, 4)), x],
         [x, y, ((1, 2), (3, 4))]),
    ]
    for start, source, target in tests:
        first, second = route(start, source), route(start, target)
        assert first[-1] == second[-1] == tuple(sorted(start))
        assert first != second
        charge = lambda moves: sum(len(l) * len(r) for l, r in moves)
        assert charge(source) == charge(target)
    return len(tests)


if __name__ == "__main__":
    print(f"{check_bridge_operands()} pure-operand hemisphere checks")
    print(f"{check_transformations()} transformation arrays checked")
    print(f"{check_grid_routes()} wide-grid generator boundaries checked")
