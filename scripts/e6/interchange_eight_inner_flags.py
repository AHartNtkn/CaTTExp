"""Check the marked crossing order in a late inner product.

For each earlier positive early pair and later positive late pair, test
whether an event of the early pair precedes the selected late occurrence.
Inside the late product only its spatial left operand can contain the early
event. Changing this order by K15 would force a second late pair using an
early witness strand. The intersecting-quartet score of Response 32 forbids that
pair after the earlier positive contribution.
"""

from itertools import combinations, permutations, product

from interchange_sorting_fiber import moves, raw_histories, states
from marked_swap_schedules import expansions


def check_block():
    count = 0
    for f in map(''.join, combinations('abcdef', 2)):
        rest = ''.join(x for x in 'abcdef' if x not in f)
        for m in map(''.join, combinations(rest, 2)):
            n = ''.join(x for x in rest if x not in m)
            slots = sorted(f + m)
            packet = {a+b for a, b in product(slots[:2], slots[2:])}
            if not {f, m} <= packet:
                continue
            for hi, lo in product(permutations(slots[2:]), permutations(slots[:2])):
                orders = {tuple(a+b for a, b in path) for path in expansions(lo, hi)}
                if len({w.index(f) < w.index(m) for w in orders}) == 1:
                    continue
                # The last crossing shares one strand with each of f and m.
                # Since m is late, incidence forces this crossing to be late.
                last, = {w[-1] for w in orders}
                assert all(w.index(m) < w.index(last) for w in orders)
                assert len(set(last) & set(m)) == len(set(last) & set(f)) == 1
                assert len(set(last+n)) == 4
                count += 1
    assert count == 120
    print(f'All {count} order-changing rectangular block presentations have a late bridge meeting the early pair.')


def point(f, prefix, left, m):
    return int(f in prefix or f in left[:left.index(m)])


def check_left_history():
    # Splitting a product's left history at any position must give the
    # same score on the piece carrying m. Each right history contains n.
    checked = 0
    losses = {}
    for word in permutations('abcd'):
        start = ''.join(word)
        for h in raw_histories(start):
            for m, f in permutations(h, 2):
                if set(f) & set(m):
                    continue
                before = point(f, (), h, m)
                for k in range(1, len(h)):
                    prefix, piece = ((), h[:k]) if m in h[:k] else (h[:k], h[k:])
                    assert point(f, prefix, piece, m) == before
                    checked += 1
                for edge in moves(start, h):
                    if point(f, (), edge.target, m) >= before:
                        continue
                    assert {f, m} <= set(h[edge.lo:edge.hi])
                    if edge.family == 'i':
                        assert m in edge.left_events and f in edge.right_events
                    elif edge.family == 'K15':
                        z = h[edge.hi-1]
                        assert z == edge.target[edge.hi-1]
                        assert len(set(z) & set(m)) == len(set(z) & set(f)) == 1
                    else:
                        assert edge.family in {'r', 't', 'h'}
                    losses[edge.family] = losses.get(edge.family, 0) + 1
    assert {'K15', 'i', 'r', 't', 'h'} == set(losses)
    print(f'Checked {checked} subdivision tests and all local decreases {losses}.')


def check_example(cut, cut_at, pattern, raw, steps):
    start = 'hgfedcba'
    raw = tuple(raw.split())

    def replay(schedule):
        h = raw
        early_pair = ()
        score = 0
        for name in schedule:
            lo, width = steps[name]
            window = h[lo:lo+width]
            slots = ''.join(x for x in start if x in ''.join(window))
            tr = tuple(states(start, h))
            assert tr[cut_at] == cut and tr[-1] == 'abcdefgh'
            if width == 2:
                right, left = (tr[lo].index(z[::-1]) for z in window)
                assert left + 2 <= right
            else:
                assert slots in tr[lo]
            sub = tuple(z for z in h if set(z) <= set(slots))
            i = sum(set(z) <= set(slots) for z in h[:lo])
            end = sub[:i] + window[::-1] + sub[i+width:]
            families = {'i'} if width == 2 else {'r', 't'}
            assert any(g.family in families and g.target == end
                       and (g.lo, g.hi) == (i, i+width) for g in moves(slots, sub))
            if name == 'A':
                early_pair = window
                assert all((x in ''.join(window)) == (letter == 'G')
                           for x, letter in zip(cut, pattern))
            if name == 'D':
                assert all((x in ''.join(window)) == (letter == 'S')
                           for x, letter in zip(cut, pattern))
                score += sum(point(f, h[:lo], window[1:], window[1]) for f in early_pair)
            h = h[:lo] + window[::-1] + h[lo+width:]
        assert tuple(states(start, h))[cut_at] == cut
        return h, score

    source, first = replay('CDAB')
    target, second = replay('CADB')
    assert source == target and (first, second) == (0, 2)
    print(f'{cut} ({pattern}): both schedules replay with mixed B and C; score {first} to {second}.')


def check():
    check_block()
    check_left_history()
    check_example('abhefcgd', 18, 'GGGGSSSS',
                  'fg eg ef bc ac bd ad ab cd ag bg af cg bf ae be ah bh '
                  'dg cf eh ch ce fh dh df de gh',
                  {'A': (15, 2), 'B': (0, 3), 'C': (20, 3), 'D': (18, 2)})
    check_example('dhfabgec', 12, 'GGSSGGSS',
                  'fg bc ac de be ae ab dg ag df bg dh '
                  'eg cg ce af ah fh bh bf ch eh gh ad cf bd cd ef',
                  {'A': (10, 2), 'B': (4, 3), 'C': (17, 3), 'D': (14, 2)})


if __name__ == '__main__':
    check()
