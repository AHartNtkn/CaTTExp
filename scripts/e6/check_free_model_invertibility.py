"""Finite checks of Researcher Response 1 in free-model-invertibility.md."""

from itertools import product

from grid_loop_words import classes, marked_edge, states, swap


def doubled_block(high):
    start, end = (high, high), (high - 2, high - 2)
    quotient = classes(start, end)
    word, = (w for w in quotient if marked_edge(start, end, w, 1))
    assert quotient[word] == quotient[swap(word, 1)]
    return word


def evaluate_block(word, a, b):
    events = [a[i] * b[j - 1] for i, j in word]
    # The middle events are exchanged, with the first and last as fixed pads.
    return sum(events), events[1] * events[2]


# (d, u) acts on natural numbers by n |-> max(n - d, 0) + u.
ID, UP, DOWN = (0, 0), (0, 1), (1, 0)


def then(first, second):
    d, u = first
    e, v = second
    return d + max(e - u, 0), v + max(u - e, 0)


def square(exception, exponent, early, late):
    x, u = early
    y, v = late
    # Chronological powers keep the supporting three-cell x fixed.
    front = exponent * u
    source, target = (x + y, v + front), (x + y, front + v)
    label = ID
    if v and (front == v or (exception is not None and front == exception * v)):
        label = UP
    elif v and front == 2 * v:
        label = DOWN
    return source, target, label


def main():
    early_word, late_word = doubled_block(4), doubled_block(2)
    full_word = early_word + late_word
    route = states((4, 4), full_word)
    assert route[4] == (2, 2) and route[-1] == (0, 0)
    quotient = classes((4, 4), (0, 0))
    assert len({quotient[w] for w in (
        full_word, swap(full_word, 1), swap(full_word, 5),
        swap(swap(full_word, 1), 5))}) == 1

    assert then(UP, DOWN) == ID and then(DOWN, UP) != ID
    indices = range(3, 8)
    right_lengths = [b for b in product(range(5), repeat=4) if sum(b) <= 4]
    count = 0
    for a in product(range(-2, 3), repeat=2):
        for b in right_lengths:
            early = evaluate_block(early_word, a, b)
            late = evaluate_block(late_word, a, b)
            active = bool(early[1] and late[1])
            if active:
                assert early[1] == late[1] and b == (1, 1, 1, 1)
            for r in (*indices, None):
                s1, t1, first = square(r, 1, early, late)
                s2, t2, second = square(r, 2, early, late)
                # The first move has suffix X^2, the second prefix X.
                u = early[1]
                assert t1[0] == s2[0] and t1[1] + 2 * u == u + s2[1]
                assert (s1[0], s1[1] + 2 * u) == (t2[0], u + t2[1])
                assert (first, second) == ((UP, DOWN) if active else (ID, ID))
                assert then(first, second) == ID
                for p in indices:
                    source, target, label = square(r, p, early, late)
                    assert source == target
                    assert label == (UP if active and p == r else ID)
                    count += 1
    print(f"Typed the two blocks and checked {count:,} indexed queries on signed assignments.")
    print("Both padded moves compose to the identity on every tested assignment.")


if __name__ == "__main__":
    main()
