"""Exclude the remaining inverted temporal comparisons on six strands.

In a 4-path a specified flipped triangle occurs on a unique edge. A ground
rewrite either preserves that edge in its context or transports it to the
unique edge bearing the same triangle on its other side. Thus the carrier
edges on a directed 5-cycle are all in one strongly connected component.

Project by deleting one strand, retaining one full active triangle. Compare
every carrier compatible with the designated 2-cut to every carrier at the
inverted cut on the wrong side. In the last two placements, fix the outside
orientation of every triple. Shared-slot late-before-early pins then also
constrain which 3-vertices can occur between the two boundary histories.
"""
from collections import defaultdict
from functools import cache
from itertools import combinations, product

from interchange_path_grading import History, r_faces, word
from interchange_sorting_fiber import raw_histories, states
from interchange_triangle_join_interval import closure, gray, ground_interval, restrict_interval


START = 'edcba'


def events(group):
    return frozenset(a + b for a, b in combinations(sorted(group), 2))


TRIPLES = tuple(''.join(p) for p in combinations(START[::-1], 3))
BIT = {t: 1 << i for i, t in enumerate(TRIPLES)}
PACKETS = {t: events(t) for t in TRIPLES}


@cache
def trajectory(raw):
    return tuple(states(START, raw))


@cache
def orientation(raw):
    return sum(BIT[t] for t in TRIPLES if raw.index(t[:2]) < raw.index(t[1:]))


def components(graph, labels, mark):
    marked = {label for e, label in labels.items() if mark in gray(e)}
    forward, backward = defaultdict(set), defaultdict(set)
    for rule in graph.rules.values():
        lhs = [e for e in rule.source.edges if e in marked]
        rhs = [e for e in rule.target.edges if e in marked]
        assert len(lhs) == len(rhs) <= 1
        if not lhs:
            continue
        a, b = lhs[0], rhs[0]
        forward[a].add(b)
        backward[b].add(a)
        if rule.equation:
            forward[b].add(a)
            backward[a].add(b)
    by_node = {}
    for node in marked:
        if node not in by_node:
            component = closure(node, forward.__getitem__) & closure(node, backward.__getitem__)
            by_node.update((v, min(component)) for v in component)
    return by_node


@cache
def carrier_test(early, early_left, start_mask=None, end_mask=None):
    late = ''.join(x for x in START[::-1] if x not in early)
    cut = early + late[::-1] if early_left else late[::-1] + early
    inv = early[::-1] + late if early_left else late + early[::-1]
    mark = early if len(early) == 3 else late
    wide_early = mark == early
    early_events = frozenset(a + b for a, b in combinations(cut, 2) if a < b)
    mono = {t for t, packet in PACKETS.items()
            if packet <= early_events or packet.isdisjoint(early_events)}
    assert (start_mask is None) == (end_mask is None)
    raws = raw_histories(START)
    outside = [p for p in raws if cut in trajectory(p)]
    sources = [p for p in outside if not orientation(p) & BIT[mark]
               and (start_mask is None or orientation(p) == start_mask)]
    targets = [p for p in outside if orientation(p) & BIT[mark]
               and (end_mask is None or orientation(p) == end_mask)]
    allowed = set(raws)
    if start_mask is not None and end_mask is not None:
        changed = start_mask ^ end_mask
        pins = [(BIT[g], BIT[h]) for g in mono if changed & BIT[g] and PACKETS[g] <= early_events
                for h in mono if changed & BIT[h] and PACKETS[h].isdisjoint(early_events)
                and set(g) & set(h)]
        allowed = {p for p in allowed if all(not (orientation(p) & g) or orientation(p) & h
                                             for g, h in pins)}
    classes, at = restrict_interval(START, sources, targets, allowed,
                                    lambda e: e.family == 'K15' or set(gray(e)) <= mono)
    graph, labels = ground_interval(classes, at)
    cc = components(graph, labels, mark)
    designated, inverted = set(), set()
    for e, name in labels.items():
        if name not in cc:
            continue
        v = trajectory(e.source)
        if cut in v and (e.hi <= v.index(cut) if wide_early else e.lo >= v.index(cut)):
            designated.add(cc[name])
        if inv in v and (e.lo >= v.index(inv) if wide_early else e.hi <= v.index(inv)):
            inverted.add(cc[name])
    return not (designated & inverted)


def normalize(early, erased):
    remaining = 'abcdef'.replace(erased, '')
    return early.replace(erased, '').translate(str.maketrans(remaining, 'abcde'))


def half_boundaries(start, finish, mark):
    """One representative per possible orientation at either end of this half.

    We allow every nested pair of orientation sets with a flip of the
    designated mark. Such pairs need not be connected by a 4-path.
    """
    endpoint_order = {s: i for i, s in enumerate(finish)}

    @cache
    def tails(state):
        if state == finish:
            return ((),)
        found = []
        for i, (a, b) in enumerate(zip(state, state[1:])):
            if endpoint_order[a] > endpoint_order[b]:
                assert a > b
                after = state[:i] + b + a + state[i + 2:]
                found.extend((b + a, *rest) for rest in tails(after))
        return tuple(found)

    histories = tails(start)
    triples = map(''.join, combinations(sorted(start), 3))
    present = set(histories[0])
    complete = [t for t in triples if events(t) <= present]
    by_orientation = {frozenset(t for t in complete if h.index(t[:2]) < h.index(t[1:])): h
                      for h in histories}
    return [(s, t) for before, s in by_orientation.items()
            for after, t in by_orientation.items() if before < after and mark in after - before]


@cache
def projected_mask(raw, omit):
    remaining = 'abcdef'.replace(omit, '')
    rename = str.maketrans(remaining, 'abcde')
    return orientation(tuple(e.translate(rename) for e in raw if omit not in e))


def check_mixed_rectangle():
    """Execute CDAB and CADB with four proper r's on the cut cdefba."""
    initial = tuple('ef df cf de ce cd bf af be ae ab ad ac bd bc'.split())
    # Temporal offset, varying 2-word, its crossing, stationary strand.
    inputs = {'A': (3, 'dc', 'cd', 'e'), 'B': (0, 'edc', 'cd', 'f'),
              'C': (8, 'ba', 'ab', 'e'), 'D': (6, 'ba', 'ab', 'f')}

    def perform(schedule):
        raw = initial
        for name in schedule:
            lo, varying, event, stationary = inputs[name]
            state = tuple(states('fedcba', raw[:lo]))[-1]
            assert stationary + varying in state
            moving = History(word(varying), (tuple(event[::-1]),))
            source, target = r_faces(moving, word(stationary))
            before, after = (tuple(b + a for a, b in face.events) for face in (source, target))
            hi = lo + len(before)
            assert raw[lo:hi] == before
            raw = raw[:lo] + after + raw[hi:]
            trajectory = tuple(states('fedcba', raw))
            assert trajectory[6] == 'cdefba' and trajectory[-1] == 'abcdef'
        return raw

    finish = tuple('cd ef cf df ce de ab af bf ae be ad ac bd bc'.split())
    assert perform('CDAB') == perform('CADB') == finish
    print('Executed the four mixed inputs cde, cdf, abe, abf on both temporal schedules.')


def check():
    check_mixed_rectangle()
    groups = tuple(''.join(p) for p in combinations('abcdef', 3))
    # The five-slot prefix/suffix test handles all twenty cuts with E on
    # the right. Run the component test independently on all twenty others.
    unresolved = [g for g in groups if not any(carrier_test(normalize(g, x), True)
                                               for x in 'abcdef')]
    assert unresolved == ['cde', 'cdf']
    print('Unrestricted carrier components exclude 18 of 20 left-block cuts.')
    for early in unresolved:
        late = ''.join(x for x in 'abcdef' if x not in early)
        cut = early + late[::-1]
        count = 0
        for (a, b), (c, d) in product(half_boundaries('fedcba', cut, early),
                                      half_boundaries(cut, 'abcdef', late)):
            start, finish = a + c, b + d
            assert any(carrier_test(normalize(early, x), True, projected_mask(start, x),
                                    projected_mask(finish, x)) for x in 'abcdef')
            count += 1
        assert count == {'cde': 28, 'cdf': 38}[early]
        print(f'{cut}: a five-slot carrier obstruction for all {count} outside orientation pairs.')


if __name__ == '__main__':
    check()
