"""Finite checks for the degree-four trace and Diophantine multiplication gate.

Enumerate all binary operand histories of length at most 3, all their block
splits, and all witness words of length at most 10 for left inputs 0..5.
Replay forward sorting certificates separately for all input pairs in 0..6.
The histories here model event colors. The proof identifies the applicable
globular equations and establishes the weight conservation used by the trace.
"""

from itertools import product


def words_through(limit):
    for size in range(limit + 1):
        for letters in product("LR", repeat=size):
            yield "".join(letters)


def product_weights(left, right):
    # The full contextual inner edge counts event pairs with multiplicity.
    pairs = tuple(product(left, right))
    return len(pairs), pairs.count(("L", "L")), pairs.count(("R", "R"))


def color_trace(weights):
    total, left, right = weights
    assert total == left + right
    assert not (left and right)
    return "L" * left + "R" * right


def check_blocks():
    blocks = splits = 0
    histories = tuple(words_through(3))
    for first, second in product(histories, repeat=2):
        weight = product_weights(first, second)
        total, left, right = weight
        mixed = sum(a != b for a in first for b in second)
        assert total - left - right == mixed
        blocks += 1
        for i in range(len(first) + 1):
            for j in range(len(second) + 1):
                pieces = [
                    product_weights(x, y)
                    for x in (first[:i], first[i:])
                    for y in (second[:j], second[j:])
                ]
                assert tuple(map(sum, zip(*pieces))) == weight
                if mixed == 0:
                    assert "".join(map(color_trace, pieces)) == color_trace(weight)
                splits += 1
    return blocks, splits


def successors(word):
    for position in range(len(word) - 1):
        if word[position : position + 2] == "RL":
            yield position, word[:position] + "LR" + word[position + 2 :]


def reachable_words(start):
    seen = {start}
    todo = [start]
    while todo:
        for _, target in successors(todo.pop()):
            if target not in seen:
                seen.add(target)
                todo.append(target)
    return seen


def check_converse():
    # Compute the observed gates directly from commutation and directed
    # reachability to every sorted endpoint of the same length.
    observed = set()
    tested = 0
    for candidate in words_through(10):
        reachable = None
        for m in range(6):
            probe = "L" * m + "R"
            tested += 1
            if candidate + probe != probe + candidate:
                continue
            if reachable is None:
                reachable = reachable_words(candidate)
            for n in range(len(candidate) + 1):
                r = len(candidate) - n
                if "L" * r + "R" * n in reachable:
                    observed.add((m, n, r, candidate))
    expected = {
        (m, n, m * n, ("L" * m + "R") * n)
        for m in range(6)
        for n in range(11)
        if (m + 1) * n <= 10
    }
    assert observed == expected
    return tested, len(observed)


def check_construction():
    certificates = steps = 0
    for m, n in product(range(7), repeat=2):
        probe = "L" * m + "R"
        witness = probe * n
        assert witness + probe == probe + witness
        certificate = []
        current = witness
        while "RL" in current:
            position, current = next(successors(current))
            certificate.append(position)

        # Replay the swap positions without consulting the search procedure.
        replay = list(witness)
        for position in certificate:
            assert replay[position : position + 2] == ["R", "L"]
            replay[position], replay[position + 1] = replay[position + 1], replay[position]
        assert "".join(replay) == "L" * (m * n) + "R" * n
        assert len(certificate) == m * n * (n - 1) // 2
        certificates += 1
        steps += len(certificate)
    return certificates, steps


if __name__ == "__main__":
    blocks, splits = check_blocks()
    tested, gates = check_converse()
    certificates, steps = check_construction()
    print(f"{blocks} event products and {splits} contextual subdivisions")
    print(f"{tested} witness/input pairs, {gates} accepted gates, exact agreement")
    print(f"{certificates} sorting certificates, {steps} directed swaps replayed")
