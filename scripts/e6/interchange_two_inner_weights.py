"""Check the two-inner inversion count with a mixed inactive path on each side.

A word lists groups in 4-path order. Each group carries a nonnegative early
and late weight. The cross terms in the inversion count are bilinear. Binary
unit choices therefore test the coefficient of each potential lost pair,
including for composite variations. A loss in N or the shifted join forces
a left-late/right-early product at or after positive early work.
"""

from dataclasses import replace
from itertools import product

from interchange_quartet_cut import EXPECTED
from interchange_sorting_fiber import moves, states
from interchange_triangle_join_interval import weight


def inversions(route, early, late):
    return sum(early[a] * late[b] for i, a in enumerate(route) for b in route[i+1:])


def check_lost_pairs():
    # X is the left variation, Y the right. I is the product. Before
    # and after transport it carries identical weights. Internal terms
    # in a composite occurrence cancel, leaving only the terms below.
    for source, target in [('IX', 'XI'), ('YI', 'IY'), ('YIX', 'XYI')]:
        for early_group, late_group in product(source, repeat=2):
            early = {a: int(a == early_group) for a in source}
            late = {a: int(a == late_group) for a in source}
            if inversions(source, early, late) <= inversions(target, early, late):
                continue
            left_has_late = late_group in 'XI'
            right_has_early = early_group in 'YI'
            assert left_has_late and right_has_early
            assert source.index(early_group) <= source.index('I')

    witnessed = 0
    for cut, cases in EXPECTED.items():
        for (pair, before, left), all_triangles in cases:
            right, = set(pair) - {left}
            if cut.index(left[0]) < cut.index(left[1]):
                continue
            assert cut.index(right[0]) < cut.index(right[1])
            forced = ''.join(sorted(left + min(right)))
            assert forced in all_triangles and forced not in before
            assert all(cut.index(x) > cut.index(y) for x, y in
                       ((forced[0], forced[1]), (forced[1], forced[2])))
            witnessed += 1
    assert witnessed == 4


def check_example():
    start = 'fedcba'
    raw = tuple('ef bc bd bf ac be ad af ae ab df de cf ce cd'.split())
    specs = {
        'A': ('i', 4, 'ac be', 'be ac'),
        'B': ('t', 0, 'ef bc bd bf be', 'bc bd be bf ef'),
        'C': ('r', 10, 'df de cf ce cd', 'cd cf df ce de'),
        'D': ('i', 12, 'df ce', 'ce df'),
    }
    supports, occurrences = {}, {}
    def replay(schedule):
        history = raw
        for letter in schedule:
            kind, lo, old, new = specs[letter]
            src, dst = tuple(old.split()), tuple(new.split())
            assert history[lo:lo+len(src)] == src
            end = history[:lo] + dst + history[lo+len(src):]
            hits = [e for e in moves(start, history)
                    if e.family == kind and e.target == end and (e.lo, e.hi) == (lo, lo + len(src))]
            assert hits and list(states(start, end))[10] == 'abefdc'
            occurrences[letter] = hits[0]
            if kind == 'i':
                for edge in hits:
                    assert len(edge.left_events) == len(edge.right_events) == 1
                    pair = (edge.left_events[0], edge.right_events[0])
                    assert supports.setdefault(letter, pair) == pair
            history = end
        return history

    assert replay('CDAB') == replay('CADB') and supports == {
        'A': ('be', 'ac'), 'D': ('ce', 'df')}
    g, s = (set(''.join(supports[k])) for k in 'AD')
    assert len(g | s) == 6 and len(g & s) == 2
    def projected(edge, keep):
        letters = lambda w: ''.join(x for x in w if x in keep)
        events = lambda seq: tuple(ev for ev in seq if set(ev) <= keep)
        return weight(replace(edge, left=letters(edge.left), right=letters(edge.right),
                              left_events=events(edge.left_events), right_events=events(edge.right_events)))

    # The active windows are each monochromatic. Filter by temporal
    # side and compute the native weights after retaining each quartet.
    early = {k: projected(v, g) if k in 'AB' else 0 for k, v in occurrences.items()}
    late = {k: projected(v, s) if k in 'CD' else 0 for k, v in occurrences.items()}
    assert inversions('CDAB', early, late) == 0 and inversions('CADB', early, late) == 1
    print('Replayed both six-strand schedules at abefdc with mixed C and B and joint witness cost six.')


if __name__ == '__main__':
    check_lost_pairs()
    check_example()
    print('Every possible loss in the two naturalities or shifted join requires a later late triangle.')
