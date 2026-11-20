"""Extend the right-join crossing test to disjoint inner and triangle witnesses.

The designated cut places the quartet before the descending triangle. Fix
one late crossing m of the triangle. For the crossing score of Response 29
the only new ambiguity is a K15 redescription interchanging m and a counted
right event e in an inner product with an early left event f. On f,e,m's six
strands the ambiguity requires a two-by-two crossing block in the right
operand, with f alone on the left. The quartet table and five-strand edge
scores exclude candidate blocks. Failure to find a score retains the block.
"""

import argparse
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, permutations

from interchange_five_cut_ranks import cut_graph
from interchange_inner_triangle_windows import cases, increasing, matchings, normalize
from interchange_quartet_cut import EXPECTED
from interchange_regular_rectangles import feasible
from interchange_sorting_fiber import raw_histories
from interchange_triangle_carriers import START, trajectory
from marked_swap_schedules import expansions


def possible_pair(cut, f, z):
    slots = ''.join(sorted(f + z))
    rename = str.maketrans(slots, 'abcd')
    local_cut = ''.join(x for x in cut if x in slots).translate(rename)
    pair = tuple(sorted((f.translate(rename), z.translate(rename))))
    return any(opposite == pair for (opposite, _, _), _ in EXPECTED.get(local_cut, ()))


@cache
def five_scores(cut):
    histories = set(raw_histories(START))
    early = increasing(cut)
    seeds = {p for p in histories if cut in trajectory(p)}
    _, _, graph, labels = cut_graph(histories, seeds, early)
    zero = {n for e, n in labels.items() if e.source in seeds and
            (e.hi <= len(early) or e.lo >= len(early))}
    constraints = [({n: 1}, '=' if n in zero else '>=') for n in graph.edges]
    for rule in graph.rules.values():
        diff = Counter(rule.target.edges)
        diff.subtract(rule.source.edges)
        constraints.append(({k: v for k, v in diff.items() if v}, '=' if rule.equation else '>='))
    products = defaultdict(set)
    for e, n in labels.items():
        if e.family == 'i' and len(e.left_events) == 1 and len(e.right_events) == 2:
            products[e.left + e.right, e.left_events[0], e.right_events].add(n)
    return constraints, products


@cache
def forbidden_product(cut, start, f, packet):
    constraints, products = five_scores(cut)
    candidates = products.get((start, f, packet), ())
    if not candidates:
        return True
    rows = constraints + [({n: 1}, '>') for n in sorted(candidates)]
    score = feasible(rows)
    if score is None:
        return False
    for row, relation in rows:
        value = sum(v * score.get(n, 0) for n, v in row.items())
        assert value == 0 if relation == '=' else value >= int(relation == '>')
    return True


@cache
def ambiguous(cut, m, f, e, project):
    slots = ''.join(sorted(m + e))
    small, large = slots[:2], slots[2:]
    packet = {a+b for a in small for b in large}
    if not {m, e} <= packet:
        return False
    if any(not possible_pair(cut, f, z) for z in packet - increasing(cut)):
        return False
    if not project:
        return True
    for left in permutations(large):
        for right in permutations(small):
            # As in the local face grounder, the outer-small moving word
            # crosses the outer-large stationary word on its left.
            paths = [tuple(a+b for a, b in p) for p in expansions(right, left)]
            if len({p.index(m) < p.index(e) for p in paths}) == 1:
                continue
            start = f[::-1] + ''.join(left + right)
            for omit in slots:
                keep = ''.join(sorted(set(start) - {omit}))
                surviving, = {tuple(normalize(z, keep) for z in p if omit not in z) for p in paths}
                if forbidden_product(normalize(cut, keep), normalize(start, keep), normalize(f, keep),
                                     surviving):
                    break
            else:
                return True
    return False


def protected(cut, triangle, quartet, project):
    # The score counts all positive early pairs on the quartet. Either
    # spatial order of every early matching can appear on an intervening path.
    pairs = list(matchings(quartet, increasing(cut)))
    return any(all(not ambiguous(cut, m, f, e, project) and not ambiguous(cut, m, e, f, project)
                   for f, e in pairs)
               for m in map(''.join, combinations(triangle, 2)))


def check(list_open=False):
    counts = Counter()
    remaining = defaultdict(list)
    for cut, triangle, quartet, _, surviving in cases():
        if not surviving:
            continue
        assert cut.endswith(triangle[::-1])
        counts['input'] += 1
        if protected(cut, triangle, quartet, False):
            counts['quartet'] += 1
        elif protected(cut, triangle, quartet, True):
            counts['five'] += 1
        else:
            counts['open'] += 1
            remaining[triangle].append(cut)
    assert counts == {'input': 168, 'quartet': 126, 'five': 6, 'open': 36}
    print('Of 168 placements, the quartet test protects 126 and five-strand scores protect 6 more.')
    print('36 cut/triangle placements survive both tests.')
    if list_open:
        for triangle, cuts in sorted(remaining.items()):
            print(f'{triangle}: {" ".join(sorted(cuts))}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--list-open', action='store_true', help='print the remaining cuts by late triangle')
    check(parser.parse_args().list_open)
