"""Check the color-filtered 4-weight and the order at a specified input update."""
from collections import Counter
from itertools import product

from interchange_double_disk_paths import build, moves
from interchange_four_slot_ground import CROSSES, laws, primitive_moves, raw_histories, slots
from interchange_mark_windows import names, read_edge
from interchange_response12_rectangles import shifted_joins


def route_weight(raw, path, selected):
    total = 0
    compatible = True
    for edge in path:
        events = names(raw)
        left = events[edge.lo:edge.mid]
        right = events[edge.mid:edge.hi]
        if edge.kind == 'i':
            total += len(selected.intersection(left)) * len(selected.intersection(right))
        else:
            moving = ''.join(sorted(slots(raw[edge.lo:edge.mid]) & {'x','y'}))
            for advance, partner in read_edge(raw, edge)[0]:
                slot = advance[0].lower()
                crossing = next(e for e, pair in CROSSES.items() if pair == partner+slot)
                compatible &= (advance in selected) == (crossing in selected)
                if advance not in selected:
                    continue
                total += 11
                for spectator in moving:
                    if spectator != slot:
                        pair = next(e for e, s in CROSSES.items() if s == partner+spectator)
                        if pair in selected:
                            total += 1 if moving.index(spectator) > moving.index(slot) else -1
        raw = edge.target(raw)
    return total, compatible


def check_weights():
    counts = Counter()
    for arity in ((2,0),(1,1),(0,2)):
        for raw in raw_histories(*arity):
            rules = list(laws(raw))
            rules.extend(('shifted', lhs, rhs) for lhs,rhs in shifted_joins(raw,primitive_moves))
            for mask in product((False,True), repeat=len(raw)):
                selected = {e for e, enabled in zip(names(raw),mask) if enabled}
                for name,lhs,rhs in rules:
                    a,ok = route_weight(raw,lhs,selected)
                    b,also_ok = route_weight(raw,rhs,selected)
                    assert ok == also_ok
                    if ok:
                        assert a == b and a >= 0, (raw,mask,name,lhs,rhs)
                        counts[name] += 1
    return counts


def disk_path(start, path, flag, selected):
    state = start
    weight = 0
    point = None
    compatible = True
    for op in path:
        word = state[0]
        if op == flag:
            event = {'x':'A','y':'B'}[flag]
            point = frozenset(word[:word.index(event)]), weight
        if op in ('r','h','t'):
            moving = 'B' if op == 't' else 'A'
            compatible &= (moving in selected) == ('C' in selected)
            if moving in selected:
                weight += 11 - int(op == 'h' and 'B' in selected)
        elif op == 'i':
            weight += int({'A','B'} <= selected)
        else:
            weight += int({'x':'A','y':'B'}[op] in selected)
        state = dict(moves(state))[op]
    return point, weight, compatible, state[0]


def check_flags():
    paths, graph, _, _ = build()
    counts = Counter()
    for src, successors in enumerate(graph):
        start, path = paths[src]
        for flag in set(path) & {'x','y'}:
            event = {'x':'A','y':'B'}[flag]
            for dst in successors:
                other_start, other = paths[dst]
                assert start == other_start
                for cut in (1,2):
                    early = set(start[0][:cut])
                    is_early = event in early
                    selected = set('ABC')-early if is_early else early
                    old, total, ok, end = disk_path(start,path,flag,selected)
                    new, new_total, also_ok, end2 = disk_path(start,other,flag,selected)
                    assert end == end2 and ok == also_ok and old[0] <= new[0]
                    counts['set inclusions'] += 1
                    if ok:
                        assert total == new_total
                    if not ok or set(end[:cut]) != early or old[0] != new[0]:
                        continue
                    if (is_early and old[0] & selected) or (not is_early and not selected <= old[0]):
                        continue
                    assert (new[1] <= old[1]) if is_early else (new[1] >= old[1])
                    counts['prefix inequalities'] += 1
                    counts['strict'] += old[1] != new[1]
    return counts


if __name__ == '__main__':
    print('Four-slot compatible weight checks', dict(sorted(check_weights().items())))
    print('Two-flag disk comparisons', dict(sorted(check_flags().items())))
