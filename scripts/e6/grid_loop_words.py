"""Check the support-free 5-comparisons on the doubled H in the 2-by-4 grid."""

from functools import cache
from itertools import permutations, product


@cache
def schedules(start, end):
    if start == end:
        return ((),)
    result = []
    for a, h in enumerate(start):
        if h <= end[a] or (a == 1 and h == start[0]):
            continue
        after = list(start)
        after[a] -= 1
        result.extend(((a, h),) + rest for rest in schedules(tuple(after), end))
    return tuple(result)


@cache
def block(lo, hi):
    """All binary rectangular expansions of the crossing of the two a's."""
    left = tuple((0, b) for b in range(hi, lo, -1))
    right = tuple((1, b) for b in range(hi, lo, -1))
    words = {left + right}
    for split in range(lo + 1, hi):
        words.update(p + q for p in block(split, hi) for q in block(lo, split))
    return words


def states(start, word):
    result = [start]
    for a, b in word:
        next_state = list(result[-1])
        assert next_state[a] == b and (a == 0 or next_state[0] < b)
        next_state[a] -= 1
        result.append(tuple(next_state))
    return result


@cache
def classes(start, end):
    """Impose K15 on contiguous rectangles, including inside every word context."""
    unseen = set(schedules(start, end))
    result = {}
    while unseen:
        seed = unseen.pop()
        component = {seed}
        pending = [seed]
        while pending:
            w = pending.pop()
            for i, (x, y) in enumerate(states(start, w)):
                if x != y:
                    continue
                for lo in range(x - 1):
                    j = i + 2 * (x - lo)
                    expansions = block(lo, x)
                    if w[i:j] in expansions:
                        for part in expansions:
                            other = w[:i] + part + w[j:]
                            if other in unseen:
                                unseen.remove(other)
                                component.add(other)
                                pending.append(other)
        rep = min(component)
        result.update((w, rep) for w in component)
    return result


def marked_edge(start, end, w, i):
    first, second = w[i:i + 2]
    if not (first[0] == 1 and second[0] == 0 and first[1] == second[1] + 1
            and first[1] in (2, 4)):
        return None
    corners = states(start, w)
    p = classes(start, corners[i])[w[:i]]
    q = classes(corners[i + 2], end)[w[i + 2:]]
    return p, (second[1], first[1]), q


def swap(w, i):
    return w[:i] + (w[i + 1], w[i]) + w[i + 2:]


def reach(start, rules):
    seen = {start}
    pending = [start]
    while pending:
        w = pending.pop()
        for i in range(len(w) - 1):
            for old, new in rules:
                if w[i:i + 2] == old:
                    nxt = w[:i] + new + w[i + 2:]
                    if nxt not in seen:
                        seen.add(nxt)
                        pending.append(nxt)
    return seen


def check_grid():
    start, end = (4, 4), (0, 0)
    paths = classes(start, end)
    edges, squares = {}, set()
    for w in paths:
        for i in range(len(w) - 1):
            left = marked_edge(start, end, w, i)
            if left is None:
                continue
            changed = swap(w, i)
            boundary = paths[w], paths[changed]
            assert edges.setdefault(left, boundary) == boundary
            for j in range(i + 2, len(w) - 1):
                right = marked_edge(start, end, w, j)
                if right is None:
                    continue
                after_right = marked_edge(start, end, swap(w, j), i)
                after_left = marked_edge(start, end, changed, j)
                assert after_right and after_left
                squares.add(((right, after_right), (left, after_left)))
    # Construct the actual whiskerings on two consecutive full 2-by-2 blocks.
    def right_first(k):
        return ((0, k), (1, k), (0, k - 1), (1, k - 1))
    w = right_first(4) + right_first(2)
    earlier = marked_edge(start, end, w, 1)
    later = marked_edge(start, end, w, 5)
    assert len({*edges[earlier], *edges[later]}) == 1
    for source, target in squares:
        for a, b in (source, target):
            assert edges[a][1] == edges[b][0]
        assert edges[source[0]][0] == edges[target[0]][0]
        assert edges[source[1]][1] == edges[target[1]][1]

    # D is the step (later, earlier) -> (earlier, later). Place one
    # copy on each half of a four-letter word and evaluate both 5-paths.
    old, new = (later, earlier), (earlier, later)
    assert (old, new) in squares
    begin, finish = old + old, new + new
    middle_right, middle_left = old + new, new + old
    assert middle_right != middle_left and begin != finish
    assert middle_right in reach(begin, squares) and finish in reach(middle_right, squares)
    assert middle_left in reach(begin, squares) and finish in reach(middle_left, squares)
    print("The two D,D boundary paths have different middle words and the same endpoints.")

    count = 0
    for length in range(7):
        words = set(product((earlier, later), repeat=length))
        for word in words:
            actual = reach(word, squares) & words
            predicted = reach(word, {((later, earlier), (earlier, later))})
            assert actual == predicted
            count += 1
    print(f"{len(paths)} schedules, {len(edges)} marked contextual edges, {len(squares)} marked delta rules.")
    print(f"Directed reachability agrees on all {count} doubled-loop words of length at most six.")


def check_rectangles(n):
    counts = [0, 0]
    for i, j in product(range(n + 1), repeat=2):
        for r in range(1, i + 1):
            for s in range(1, j - i + 1):
                labels = set(product(range(i - r + 1, i + 1), range(j - s + 1, j + 1)))
                marks = [(a, b) for a, b in labels if b == a + 1 and a % 2 == 1]
                assert len(marks) <= 1
                counts[0] += 1
                for c1 in range(n + 1):
                    for c2 in range(c1, n + 1):
                        early = {(a, b) for a, b in labels if a > c1 and b > c2}
                        late = {(a, b) for a, b in labels if a <= c1 and b <= c2}
                        if labels == early | late:
                            assert not (early and late)
                            counts[1] += 1
    print(f"Width two, height {n}: {counts[0]} rectangles, {counts[1]} monochromatic cut tests.")


# Four disjoint crossings b_i a_i on the 4-by-4 grid can occur in any
# order. Here the same pair labels can occur on either side of a cut.
@cache
def sorting_paths(word, lo, hi):
    paths = [(word, ())]
    for i in range(lo, hi - 1):
        if word[i] > word[i + 1]:
            edge = (frozenset(word[:i]), frozenset(word[i:i + 2]))
            for target, rest in sorting_paths(swap(word, i), lo, hi):
                paths.append((target, (edge,) + rest))
    return paths


def colors(route, cut, anchored):
    word = []
    for before, pair in route:
        if pair <= cut and (not anchored or before | pair <= cut):
            word.append("E")
        elif pair.isdisjoint(cut) and (not anchored or cut <= before):
            word.append("L")
        else:
            return None
    return word


def inversions(word):
    return sum(word[:i].count("L") for i, color in enumerate(word) if color == "E")


def check_four_independent_events():
    cuts = [frozenset(i for i in range(4) if mask & (1 << i)) for mask in range(16)]
    connected_checks = delta_checks = unanchored_increases = 0
    for word in permutations(range(4)):
        for lo, hi in ((0, 3), (1, 4), (0, 4)):
            routes = {}
            for target, route in sorting_paths(word, lo, hi):
                routes.setdefault(target, []).append(route)
            for alternatives in routes.values():
                if len(alternatives) < 2:
                    continue
                pairs = [pair for _, pair in alternatives[0]]
                component = {word[lo]}
                for _ in range(hi - lo):
                    for pair in pairs:
                        if component & pair:
                            component |= pair
                if len(component) != hi - lo:
                    continue
                for cut in cuts:
                    values = [colors(route, cut, anchored=True) for route in alternatives]
                    assert all(v == values[0] for v in values)
                    if values[0] is not None:
                        connected_checks += 1
        if word[0] < word[1] or word[2] < word[3]:
            continue
        target = swap(swap(word, 0), 2)
        routes = [path for end, path in sorting_paths(word, 0, 4) if end == target]
        assert len(routes) == 2
        # Right spatial substring first is the source of the delta comparison.
        source, dest = sorted(routes, key=lambda path: -len(path[0][0]))
        for cut in cuts:
            a, b = colors(source, cut, True), colors(dest, cut, True)
            assert (a is None) == (b is None)
            if a is not None:
                assert inversions(b) <= inversions(a)
                delta_checks += 1
            a, b = colors(source, cut, False), colors(dest, cut, False)
            if a is not None and inversions(b) > inversions(a):
                unanchored_increases += 1
    assert connected_checks and delta_checks and unanchored_increases
    print(f"Four independent events: {connected_checks} connected route tests, {delta_checks} "
          f"separated delta tests, {unanchored_increases} increases if locations are ignored.")


if __name__ == "__main__":
    check_grid()
    check_rectangles(12)
    check_four_independent_events()
