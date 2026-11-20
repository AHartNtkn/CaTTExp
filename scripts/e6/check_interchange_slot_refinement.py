"""Verify the degree-three slot refinement and a failure of greedy sorting."""

from collections import defaultdict, deque
from functools import cache
from itertools import combinations

from interchange_sorting_fiber import moves, raw_histories
from t_endomorphisms import UF, expansions


@cache
def rectangles(state, factors):
    """All positive block re-spellings enabled in this spatial state."""
    rules = defaultdict(set)
    for lo, mid, hi in combinations(range(len(state) + 1), 3):
        right, left = state[lo:mid], state[mid:hi]
        if max(factors[ord(a)-97] for a in left) >= min(factors[ord(b)-97] for b in right):
            continue
        variants = {tuple(a + b for a, b in word)
                    for word in expansions(tuple(left), tuple(right))}
        for source in variants:
            rules[source].update(variants - {source})
    return rules


def steps(start, path, factors):
    state = start
    for pos, event in enumerate(path):
        for factor, alternatives in rectangles(state, factors).items():
            if path[pos:pos+len(factor)] == factor:
                yield from (path[:pos] + alt + path[pos+len(factor):] for alt in alternatives)
        if len(event) == 2:
            assert event[::-1] in state
            state = state.replace(event[::-1], event)


@cache
def classes_on(start, end):
    paths = raw_histories(start, end)
    union = UF()
    for path in paths:
        for move in moves(start, path):
            if move.family == 'K15':
                union.union(path, move.target)
    return {path: union.find(path) for path in paths}


@cache
def gap_name(start, path):
    state = start
    for event in path:
        state = state.replace(event[::-1], event)
    return start, state, classes_on(start, state)[path]



def check_advance(start, factors, slot):
    end = ''.join(sorted(start))
    coarse = UF()
    refined = {}
    for word in raw_histories(start, end):
        state = start
        for pos in range(len(word)+1):
            # An independent slot-vertex advance changes no position. Its
            # contextual input-globe name and its entire 2-state are retained.
            path = word[:pos] + (slot,) + word[pos:]
            for other in steps(start, path, factors):
                coarse.union(path, other)
            refined[path] = (gap_name(start, word[:pos]), slot, state,
                             gap_name(state, word[pos:]))
            if pos < len(word):
                event = word[pos]
                state = state.replace(event[::-1], event)
    partition = {(coarse.find(p), key) for p, key in refined.items()}
    assert len(partition) == len(set(refined.values())) == len({a for a, _ in partition})
    print(f"{start}, factors {factors}: {len(refined)} marked histories, "
          f"{len(partition)} classes in both presentations")


def check_sorting():
    start, end = 'edcba', 'abcde'
    group = classes_on(start, end)
    assert len(group) == 768 and len(set(group.values())) == 422
    p = tuple('de ce be ae cd bd bc ad ac ab'.split())
    q = tuple('de ce cd be bd bc ae ad ac ab'.split())
    assert group[p] == group[q]
    factors = tuple(range(5))
    for path in group:
        actual = {move.target for move in moves(start, path) if move.family == 'K15'}
        assert actual == set(steps(start, path, factors))
    position = {e: i for i, e in enumerate(q)}

    def distance(path):
        return sum(position[a] > position[b] for i, a in enumerate(path) for b in path[i+1:])

    adjacent = set(steps(start, p, factors))
    assert distance(p) == 4 and [distance(w) for w in adjacent] == [5]
    after_first = tuple('de ce be ae cd bd ad bc ac ab'.split())
    after_second = tuple('de ce cd be ae bd ad bc ac ab'.split())
    route = (p, after_first, after_second, q)
    assert all(b in steps(start, a, factors) for a, b in zip(route, route[1:]))
    seen, todo = {p}, deque([(p, 0)])
    while todo:
        path, depth = todo.popleft()
        if path == q:
            break
        for other in steps(start, path, factors):
            if other not in seen:
                seen.add(other)
                todo.append((other, depth + 1))
    else:
        raise AssertionError("missing derivation")
    assert depth == len(route) - 1
    print(f"Five spans: 768 histories, 422 classes, shortest witness {depth} rewrites; "
          "the only first rewrite increases the distance from 4 to 5")


def check_packing():
    # Two disjoint four-slot queries whose source and target have the same
    # order across blocks. Check all reachable re-spellings after concatenation.
    start = 'cdabghef'
    left = {tuple(a+b for a,b in p) for p in expansions(tuple('ab'), tuple('cd'))}
    right = {tuple(a+b for a,b in p) for p in expansions(tuple('ef'), tuple('gh'))}
    root = min(left) + min(right)
    todo, seen = [root], {root}
    while todo:
        for other in steps(start, todo.pop(), tuple(range(8))):
            if other not in seen:
                seen.add(other)
                todo.append(other)
    assert seen == {p + q for p in left for q in right}
    print("Packed eight-span instance: the full equality class is the product of the two gap classes")


if __name__ == '__main__':
    check_sorting()
    check_advance('cdab', (0, 0, 1, 1), 'a')
    check_advance('decab', (0, 0, 1, 2, 2), 'd')
    check_advance('debca', (0, 1, 1, 2, 2), 'c')
    check_packing()
