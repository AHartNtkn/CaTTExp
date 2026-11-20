"""When can one late crossing change the order test for an early inner pair?

Keep the quartet and the late crossing. Each late triangle on six strands
meets the quartet. Response 29 pins it before positive early quartet weight
on a cycle through CDAB. Thus a positive inner product cannot have a late
event in its left operand (Response 27). A K15 ambiguity in its right operand
requires the entire four-strand block opposite a single early event f.

Project this product in all six ways to five strands. Its source and target
must be on a cut-compatible route of total excess zero, with no more late
triangle after the product. At most ten triangles can occur on five strands;
Response 24 bounds the total negative excess by 20. Both signs of every
partial excess are therefore bounded by 20 on an admissible complete route.
"""

from collections import defaultdict
from functools import cache
from itertools import combinations, permutations

from interchange_inner_triangle_blocks import ambiguous
from interchange_inner_triangle_windows import increasing, matchings, normalize
from interchange_quartet_cut import excess, triangles
from interchange_sorting_fiber import moves, raw_histories
from interchange_triangle_carriers import PACKETS, START, trajectory
from marked_swap_schedules import expansions


def charges(seeds, adjacency):
    seen = defaultdict(set)
    pending = [(p, 0) for p in seeds]
    for p in seeds:
        seen[p].add(0)
    while pending:
        p, at = pending.pop()
        for target, cost in adjacency[p]:
            value = at + cost
            if -20 <= value <= 20 and value not in seen[target]:
                seen[target].add(value)
                pending.append((target, value))
    return seen


@cache
def cut_routes(cut):
    early = increasing(cut)
    histories = raw_histories(START)
    seeds = {p for p in histories if cut in trajectory(p)}
    forward, backward = defaultdict(set), defaultdict(set)
    for p in histories:
        for edge in moves(START, p):
            support = triangles(edge)
            if any(not (PACKETS[t] <= early or PACKETS[t].isdisjoint(early)) for t in support):
                continue
            if any(PACKETS[t] <= early for t in support) and not set(p[edge.lo:edge.hi]) <= early:
                continue
            cost = excess(edge, early)
            forward[p].add((edge.target, cost))
            if all(PACKETS[t] <= early for t in support):
                # Any late-left, early-right pair requires a later late
                # triangle. It cannot occur in the suffix under test.
                if edge.family == 'i' and set(edge.left_events) - early and set(edge.right_events) & early:
                    continue
                assert cost >= 0
                backward[edge.target].add((p, cost))
    return charges(seeds, forward), charges(seeds, backward)


@cache
def projected_product(cut, start, left, right):
    before, after = cut_routes(cut)
    early = increasing(cut)
    cost = sum((f in early) != (e in early) for f in left for e in right)
    source, target = right + left, left + right
    for p, totals in before.items():
        states = trajectory(p)
        if start not in states:
            continue
        i = states.index(start)
        if p[i:i+len(source)] != source:
            continue
        end = p[:i] + target + p[i+len(source):]
        if any(-v-cost in after.get(end, ()) for v in totals):
            return True
    return False


def possible_ambiguity(cut, m, f, e):
    if not ambiguous(cut, m, f, e, False):
        return False
    slots = sorted(m+e)
    for high in permutations(slots[2:]):
        for low in permutations(slots[:2]):
            words = {tuple(a+b for a, b in path) for path in expansions(low, high)}
            if len({w.index(m) < w.index(e) for w in words}) == 1:
                continue
            start = f[::-1] + ''.join(high + low)
            for omit in start:
                keep = ''.join(sorted(set(start) - {omit}))
                left = () if omit in f else (normalize(f, keep),)
                rights = {tuple(normalize(a, keep) for a in w if omit not in a) for w in words}
                if not all(projected_product(normalize(cut, keep), normalize(start, keep), left, right)
                           for right in rights):
                    break
            else:
                return True
    return False


@cache
def unprotected():
    rows = []
    count = 0
    for order in permutations('abcdef'):
        cut = ''.join(order)
        early = increasing(cut)
        for m in map(''.join, combinations('abcdef', 2)):
            if m in early:
                continue
            quartet = ''.join(x for x in 'abcdef' if x not in m)
            for a, b in matchings(quartet, early):
                for f, e in ((a, b), (b, a)):
                    count += 1
                    if possible_ambiguity(cut, m, f, e):
                        rows.append((cut, m, f, e))
    assert count == 8100 and len(rows) == len({q for q, _, _, _ in rows}) == 72
    return tuple(rows)


if __name__ == '__main__':
    print(f'{len(unprotected())} ordered cases out of 8100 retain a possible right-operand ambiguity.')
