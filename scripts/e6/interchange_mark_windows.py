"""Compare the marked-event separation test with complete four-slot reachability."""
from collections import Counter
from dataclasses import dataclass
from functools import cache
from itertools import combinations, product

from interchange_four_slot_ground import CROSSES, primitive_moves, raw_histories, slots, walk
from interchange_four_slot_rectangles import window_paths
from interchange_path_grading import History, cross, word
from interchange_reachability import solve, verify
from interchange_response12_rectangles import ground_completion


@cache
def names(raw):
    counts = Counter()
    result = []
    for event in raw:
        counts[event] += 1
        result.append(f'{event}{counts[event]}' if event in 'XY' else event)
    return tuple(result)


@dataclass(frozen=True)
class Mark:
    kind: str
    anchors: tuple


@cache
def read_edge(raw, move):
    events = names(raw)
    first = events[move.lo:move.mid]
    second = events[move.mid:move.hi]
    if move.kind == 'i':
        return frozenset(), tuple(Mark('inner', (x,y)) for x in first for y in second)
    atoms = frozenset((advance, partner) for advance in second
                      for partner in slots(raw[move.lo:move.mid]) & {'z','w'})
    marks = set()
    for advance, partner in atoms:
        crossing = next(e for e, pair in CROSSES.items() if pair == partner + advance[0].lower())
        marks.update((Mark('mixed', (advance,)), Mark('mixed', (crossing,))))
    return atoms, tuple(marks)


def read_path(raw, moves):
    atoms, marks = set(), set()
    for move in moves:
        edge_atoms, edge_marks = read_edge(raw, move)
        atoms.update(edge_atoms)
        marks.update(edge_marks)
        raw = move.target(raw)
    return frozenset(atoms), marks


@cache
def prohibited(m, n, allowed):
    """Joining two events here means some admissible wide mixed window contains both."""
    pairs = set()
    for raw in raw_histories(m,n):
        for move in primitive_moves(raw):
            if move.kind == 'r' and read_edge(raw, move)[0] <= allowed:
                window = names(raw)[move.lo:move.hi]
                pairs.update(frozenset(pair) for pair in combinations(window, 2))
    return pairs


def separated(a, d, inseparable):
    anchors = a.anchors + d.anchors
    return all(frozenset(pair) not in inseparable for pair in combinations(anchors, 2))


def check(m,n):
    model = ground_completion(m,n)
    checked = set()
    counts = Counter()
    for raw in raw_histories(m,n):
        for cut in range(1,len(raw)):
            if not (set(raw[:cut]) & CROSSES.keys() and set(raw[cut:]) & CROSSES.keys()):
                continue
            for early, late in product(window_paths(raw,0,cut), window_paths(raw,cut,len(raw))):
                allowed = read_path(raw, early)[0] | read_path(raw, late)[0]
                conflicts = prohibited(m,n,allowed)
                for i in range(1,len(early)+1):
                    a,b = early[:i],early[i:]
                    left = read_path(raw,a)[1]
                    for j in range(len(late)):
                        c,d = late[:j],late[j:]
                        mid = raw
                        for move in c:
                            mid = move.target(mid)
                        right = read_path(mid,d)[1]
                        witnesses = {(x.kind,y.kind) for x,y in product(left,right)
                                     if separated(x,y,conflicts)}
                        counts['placements'] += 1
                        if not witnesses:
                            continue
                        counts['separated'] += 1
                        for first,second in witnesses:
                            counts[f'{first}/{second}'] += 1
                        src,dst = walk(raw,c+d+a+b),walk(raw,c+a+d+b)
                        if (src,dst) in checked:
                            continue
                        checked.add((src,dst))
                        certificate = solve(model,dst,src)
                        assert not certificate.reachable and verify(model,dst,src,certificate)
                        counts['reverse cuts'] += 1
                        counts['cut vertices'] += len(certificate.visited)
    return counts


def check_seven_slots():
    # Execute a common 3-by-4 crossing, both triangle schedules, both
    # orders of the two kernel events, and the final 2-by-2 crossing.
    start = word('gfedcba')
    early_block = cross(word('cba'), word('gfed'))
    final_block = cross(word('de'), word('fg'))
    assert early_block.start == start
    triangle = (('c','b'), ('c','a'), ('b','a'))
    pair = (('e','d'), ('g','f'))
    for a in (triangle, triangle[::-1]):
        for b in (pair, pair[::-1]):
            events = early_block.events + a + b + final_block.events
            assert len(set(events)) == len(events) == 21
            assert History(start, events).end == word('abcdefg')
    # For the sole permitted mixed atom abc, every crossing of a mixed
    # window uses at least one of a,b,c, even with spatial spectators.
    assert all(set(event).isdisjoint('abc') for event in pair)
    print('All four seven-slot histories traverse the 21 named crossings.')


if __name__ == '__main__':
    check_seven_slots()
    total = Counter()
    for arity in ((2,0),(1,1),(0,2)):
        result = check(*arity)
        print(arity, dict(sorted(result.items())))
        total.update(result)
    assert total['placements'] == 896
    for pair in product(('mixed','inner'), repeat=2):
        assert total['/'.join(pair)] > 0
