"""Check subdivision of a Gray (2,2)-cell and repeated comparison schedules."""

from collections import Counter
from itertools import combinations, permutations, product
from math import comb


def face(name, index):
    return (name, index)


def differential(generator):
    kind, index = generator
    if kind == "vertex":
        return {}
    if kind == "arrow":
        return {face("vertex", 1): 1, face("vertex", 0): -1}
    return {face("arrow", index + 1): 1, face("arrow", index): -1}


def boundary(chain):
    degrees = {"vertex": 0, "arrow": 1, "advance": 2}
    result = Counter()
    for (left, right), count in chain.items():
        for g, c in differential(left).items():
            result[g, right] += c * count
        sign = (-1) ** degrees[left[0]]
        for g, c in differential(right).items():
            result[left, g] += sign * c * count
    return {g: c for g, c in result.items() if c}


def disk_rows(start, end, side):
    return (
        [face("vertex", side)],
        [face("arrow", (start, end)[side])],
        [face("advance", i) for i in range(start, end)],
    )


def tensor_rows(left, right):
    result = {}
    for degree in range(5):
        for side in range(2):
            row = Counter()
            for i in range(3):
                j = degree - i
                if 0 <= j <= 2:
                    row.update(product(disk_rows(*left, side)[i],
                                       disk_rows(*right, side ^ (i % 2))[j]))
            result[degree, side] = row
    return result


def check_table(rows):
    for side in range(2):
        assert sum(rows[0, side].values()) == 1
        for degree in range(1, 5):
            assert all(v > 0 for v in rows[degree, side].values())
            difference = rows[degree - 1, 1].copy()
            difference.subtract(rows[degree - 1, 0])
            assert boundary(rows[degree, side]) == {g: c for g, c in difference.items() if c}
    assert rows[4, 0] == rows[4, 1]


def partitions(width):
    for cuts in product((False, True), repeat=width - 1):
        endpoints = [0, *(i for i, cut in enumerate(cuts, 1) if cut), width]
        yield tuple(zip(endpoints, endpoints[1:]))


def check_subdivisions(width, height):
    whole = tensor_rows((0, width), (0, height))
    check_table(whole)
    tags = set()
    for strips in product(partitions(width), repeat=height):
        current = whole[3, 0].copy()
        chain = Counter()
        tiles = []
        for j, strip in enumerate(strips):
            for lo, hi in strip:
                tile = tensor_rows((lo, hi), (j, j + 1))
                assert tile[3, 0] <= current
                after = current - tile[3, 0] + tile[3, 1]
                step = dict(whole)
                step[3, 0], step[3, 1] = current, after
                step[4, 0] = step[4, 1] = tile[4, 0]
                check_table(step)
                chain.update(step[4, 0])
                tiles.append((lo, hi, j, j + 1))
                current = after
        assert current == whole[3, 1] and chain == whole[4, 0]
        signature = frozenset(tiles)
        assert signature not in tags
        tags.add(signature)
    assert len(tags) == 2 ** ((width - 1) * height)
    return len(tags)


def check_schedule_chain(size):
    # A state is a list of moves in disjoint temporal slots. Each move
    # changes its component from its source face to its target face.
    def endpoints(schedule):
        state = [0] * size
        for slot in schedule:
            assert state[slot] == 0
            state[slot] = 1
        return tuple(state)

    def inversions(schedule):
        return sum(a > b for i, a in enumerate(schedule) for b in schedule[i + 1:])

    schedule = tuple(reversed(range(size)))
    common_target = endpoints(schedule)
    schedules = {schedule}
    for cut in reversed(range(1, size)):
        earlier_active = (cut - 1,)
        earlier_inactive = tuple(reversed(range(cut - 1)))
        later_active = tuple(range(cut, size))
        assert max(earlier_active + earlier_inactive) < min(later_active)
        assert schedule == later_active + earlier_active + earlier_inactive
        target = earlier_active + later_active + earlier_inactive
        assert endpoints(target) == common_target
        assert inversions(schedule) - inversions(target) == len(later_active)
        assert target not in schedules
        schedules.add(target)
        schedule = target
    assert schedule == tuple(range(size)) and len(schedules) == size
    return len(schedules) - 1


def check_pair_projections(size):
    """Compare paths of elementary swaps with every two-block contraction."""
    words = list(permutations(range(size)))
    pairs = list(combinations(range(size), 2))
    masks = {
        word: sum(1 << i for i, (a, b) in enumerate(pairs) if word.index(b) < word.index(a))
        for word in words
    }
    successors = {
        word: [word[:i] + (b, a) + word[i + 2:]
               for i, (a, b) in enumerate(zip(word, word[1:])) if a > b]
        for word in words
    }
    for source in words:
        reached = {source}
        todo = [source]
        while todo:
            for target in successors[todo.pop()]:
                if target not in reached:
                    reached.add(target)
                    todo.append(target)
        allowed = {target for target in words if masks[target] & ~masks[source] == 0}
        assert reached == allowed
    return len(words) ** 2


if __name__ == "__main__":
    count = sum(check_subdivisions(m, n) for m in range(1, 5) for n in range(1, 4))
    rectangles = sum(check_schedule_chain(r) for r in range(2, 33))
    assert rectangles == comb(32, 2)
    print(f"Validated {count} distinct tagged subdivisions on 12 signed tensor tables.")
    print(f"Validated {rectangles} consecutive proper rectangles on schedules of 2–32 moves.")
    schedules = sum(check_pair_projections(size) for size in range(2, 7))
    print(f"Compared swap reachability with all pair projections for {schedules} schedule pairs.")
