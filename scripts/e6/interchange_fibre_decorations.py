"""Check the cut count on strips and the two distinguishable loops on the 3 x 4 grid."""

from collections import deque
from itertools import permutations, product

from interchange_comparison_fibres import check_strip
from interchange_normal_form_check import complete
from t_endomorphisms import expansions, run


def projected_rectangle(rows, columns, row_first=False):
    if row_first:
        return tuple((i, c) for i in rows for c in columns)
    return tuple((i, c) for c in columns for i in rows)


def projected_rules():
    full = "qxyp", "qyxp"
    rules = [(projected_rectangle(rows, full[0]), projected_rectangle(rows, full[1]))
             for rows in ((1,), (2,), (1, 2))]
    for columns in ("qx", "qy", "xp", "yp", *full):
        rules.append((projected_rectangle((1, 2), columns),
                      projected_rectangle((1, 2), columns, row_first=True)))
    return rules


def equivalence_class(word, rules):
    seen = {word}
    pending = deque([word])
    while pending:
        current = pending.popleft()
        for left, right in rules:
            for old, new in ((left, right), (right, left)):
                for pos in range(len(current) - len(old) + 1):
                    if current[pos:pos + len(old)] != old:
                        continue
                    changed = current[:pos] + new + current[pos + len(old):]
                    if changed not in seen:
                        seen.add(changed)
                        pending.append(changed)
    return seen


def check_actual_exchanges(projected, rows, corners, first, last):
    start = tuple(("b", j) for j in range(1, 5)) + tuple(("a", i) for i in range(1, 4))
    moving = tuple(rows.values())
    stationary = tuple(corners[name] for name in "pyxq")
    history = first + stationary + moving + last
    target = first + moving + stationary + last
    full = expansions((1, 2, 3), (1, 2, 3, 4))
    assert history in full and target in full
    for row, column in projected:
        left, right = rows[row], corners[column]
        pos = history.index(right)
        assert history[pos + 1] == left
        spatial = run(start, history[:pos])
        assert spatial is not None
        left_slot = max(spatial.index(("a", left[0])), spatial.index(("b", left[1])))
        right_slot = min(spatial.index(("a", right[0])), spatial.index(("b", right[1])))
        assert left_slot < right_slot
        history = history[:pos] + (left, right) + history[pos + 2:]
        assert run(start, history) == run(start, target)
    assert history == target


def check_threshold_grid():
    rows = {1: (1, 2), 2: (1, 1)}
    corners = dict(p=(2, 4), y=(3, 4), x=(2, 3), q=(3, 3))
    first = ((1, 4), (1, 3))
    last = ((2, 2), (3, 2), (2, 1), (3, 1))
    straight = projected_rectangle((1, 2), "qxyp")
    mixed = (projected_rectangle((1, 2), "q")
             + projected_rectangle((1, 2), "xy", row_first=True)
             + projected_rectangle((1, 2), "p"))
    for word in (straight, mixed):
        check_actual_exchanges(word, rows, corners, first, last)
    rules = projected_rules()
    straight_class = equivalence_class(straight, rules)
    assert equivalence_class(mixed, rules) == {mixed} and mixed not in straight_class
    delimiter = ((2, "p"), (1, "q"))
    for pair in rules:
        for side in pair:
            assert not any(side[i:i + 2] == delimiter for i in range(len(side) - 1))
            assert delimiter[0] not in side[:-1] and delimiter[1] not in side[1:]
    words = list(product((straight, mixed), repeat=3))
    for blocks in words:
        assert len(equivalence_class(sum(blocks, ()), rules)) == len(straight_class)**blocks.count(straight)
    print(f"3 x 4: both positional loops, {len(rules)} relations, classes of sizes "
          f"{len(straight_class)} and 1, and {len(words)} three-block products checked.")


def check_cut_counts():
    for width in range(1, 10):
        # Every cut of the complete strip is determined by its prefix length.
        # The adjacency relation allows any nonempty consecutive interval.
        paths = [1]
        for stop in range(1, width + 1):
            paths.append(sum(paths[:stop]))
        assert paths[-1] == check_strip(width)
    print("Strip cut-path counts agree with independent marked evaluations through width nine.")


def check_forbidden_patterns():
    # Fix one use of each named pair. Cuts in this test DAG are the used subsets.
    labels = projected_rectangle((1, 2), "qxyp")
    equations = projected_rules()
    rules, _ = complete(dict.fromkeys(labels, 1), equations, len(labels))
    prefixes = {lhs[:i] for lhs in rules for i in range(len(lhs))}
    states = {(frozenset(), ()): 1}
    for _ in labels:
        following = {}
        for (used, suffix), count in states.items():
            for event in labels:
                if event in used:
                    continue
                word = suffix + (event,)
                suffixes = [word[i:] for i in range(len(word) + 1)]
                if any(part in rules for part in suffixes):
                    continue
                longest = next(part for part in suffixes if part in prefixes)
                key = (used | {event}, longest)
                following[key] = following.get(key, 0) + count
        states = following

    remaining = set(permutations(labels))
    components = 0
    while remaining:
        component = equivalence_class(remaining.pop(), equations)
        remaining.difference_update(component)
        components += 1
    assert sum(states.values()) == components
    print(f"Forbidden-pattern cut counts agree with all {components} permutation components.")


if __name__ == "__main__":
    check_cut_counts()
    check_threshold_grid()
    check_forbidden_patterns()
