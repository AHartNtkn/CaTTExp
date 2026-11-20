"""Test the bridge constraints for temporally inverted disjoint inner quartets.

Cross-quartet comparisons stay fixed between the two atomic windows.
Enumerate the spatial states at either window independently. Matching the
entire matrix of comparisons allows arbitrary changes inside either quartet.
The second check executes an eight-strand rectangle with mixed inactive inputs.
"""

from collections import defaultdict
from itertools import combinations, permutations

from interchange_sorting_fiber import moves, raw_histories, states
from interchange_triangle_join_interval import gray

EARLY = 'abcd'
LATE = 'efgh'
STRANDS = EARLY + LATE


def pattern(word, early):
    return ''.join('G' if x in early else 'S' for x in word)


def bridge_orders(word):
    return tuple(word.index(a) < word.index(b) for a in EARLY for b in LATE)


def enabled_pairs(word, group):
    """All ways of covering the group by two disjoint adjacent pairs."""
    adjacent = [word[i:i+2] for i in range(7) if set(word[i:i+2]) <= set(group)]
    return {tuple(sorted((''.join(sorted(a)), ''.join(sorted(b)))))
            for a, b in combinations(adjacent, 2) if set(a + b) == set(group)}


def check_patterns():
    at_early, at_late = defaultdict(set), defaultdict(set)
    patterns = {}
    for letters in permutations(STRANDS):
        word = ''.join(letters)
        matrix = bridge_orders(word)
        cut = pattern(word, EARLY)
        assert patterns.setdefault(matrix, cut) == cut
        at_early[matrix].update(enabled_pairs(word, EARLY))
        at_late[matrix].update(enabled_pairs(word, LATE))
    all_patterns = set(patterns.values())
    possible = {cut for matrix, cut in patterns.items() if at_early[matrix] and at_late[matrix]}
    assert len(all_patterns) == 70
    assert possible == {'GGGGSSSS', 'GGSSGGSS', 'GGSSSSGG',
                        'SSGGGGSS', 'SSGGSSGG', 'SSSSGGGG'}
    remaining = {c for c in possible if not c.startswith('SS') and not c.endswith('GG')}
    assert remaining == {'GGGGSSSS', 'GGSSGGSS'}
    print('Checked 40,320 spatial states and all 70 patterns; six admit both windows, '
          'and two survive the leading and trailing pair tests.')


def check_mixed_windows():
    # For every native five-slot mixed face, delete the union of its Gray
    # triangles. The entire window must contract, including join spectators.
    counts = {name: 0 for name in ('r', 't', 'h')}
    for raw in raw_histories('edcba'):
        for edge in moves('edcba', raw):
            used = set(''.join(gray(edge))) if edge.family != 'K15' else set()
            for x in set('abcde') - used:
                assert tuple(z for z in raw if x in z) == tuple(z for z in edge.target if x in z)
            if edge.family not in counts:
                continue
            assert used
            for layer in (raw, edge.target):
                assert all(set(event) & used for event in layer[edge.lo:edge.hi])
            counts[edge.family] += 1
    assert all(counts.values())
    print(f'Both faces contract on the complement of the triangle strands: {counts}.')


def check_seven():
    # Disjoint spatial intervals with either temporal ordering. Embed both
    # in a full reduced history; then execute the native inner and braid
    # faces. Only the early-before-late placement has the designated cut.
    middle = 'gbfaedc'
    def extend(start, finish):
        raw = []
        while start != finish:
            a, b = next((a, b) for a, b in zip(start, start[1:])
                        if finish.index(a) > finish.index(b))
            assert a > b
            raw.append(b+a)
            start = start.replace(a+b, b+a)
        return tuple(raw)

    left, right = ('af', 'bg'), ('de', 'ce', 'cd')
    prefix = extend('gfedcba', middle)
    suffix = extend('bgafcde', 'abcdefg')
    cut = 'bgafedc'
    early_g = {a+b for a, b in combinations(cut, 2)
               if a < b and a in 'abfg' and b in 'abfg'}
    for early_first in (False, True):
        local = left + right if early_first else right + left
        lo = len(prefix) + (len(left) if early_first else 0)
        raw = prefix + local + suffix
        assert list(states('gfedcba', raw))[-1] == 'abcdefg'
        passed = early_g <= set(raw[:lo])
        assert passed == early_first
        for order in ('PT', 'TP'):
            current = raw
            score = before = 0
            for name in order:
                window = left if name == 'P' else right
                pos = next(i for i in range(len(current)) if current[i:i+len(window)] == window)
                support = set(''.join(window))
                projection = tuple(z for z in current if set(z) <= support)
                k = sum(set(z) <= support for z in current[:pos])
                want = projection[:k] + window[::-1] + projection[k+len(window):]
                assert any(e.family in ({'i'} if name == 'P' else {'r', 't'})
                           and e.target == want and e.lo == k and e.hi == k + len(window)
                           for e in moves(''.join(sorted(support, reverse=True)), projection))
                if name == 'P':
                    before += 1
                else:
                    score = before * (early_g <= set(current[:pos]))
                current = current[:pos] + window[::-1] + current[pos+len(window):]
                assert list(states('gfedcba', current))[-1] == 'abcdefg'
            assert score == int(order == 'PT' and early_first)
    print('Replayed both 4-orders in both temporal placements of a disjoint seven-strand pair.')


def check_rectangle():
    history = tuple('gh cd bd ef cf ce bf df ch eh af cg '
                    'eg ad bh ah ab ag bg ae dh be fh dg de ac fg bc'.split())
    cut = 'cgehbdaf'
    steps = {'A': (10, 2), 'B': (3, 3), 'C': (14, 3), 'D': (20, 2)}
    f = 'af'
    def replay(schedule):
        raw = history
        prefix_weight = score = 0
        for name in schedule:
            lo, width = steps[name]
            local = raw[lo:lo+width]
            support = set(''.join(local))
            before = list(states('hgfedcba', raw))
            assert before[12] == cut and before[-1] == 'abcdefgh'
            world = ''.join(x for x in 'hgfedcba' if x in support)
            projected = tuple(ev for ev in raw if set(ev) <= support)
            offset = sum(set(ev) <= support for ev in raw[:lo])
            expected = projected[:offset] + local[::-1] + projected[offset+width:]
            assert any(e.family in ({'i'} if width == 2 else {'r', 't'}) and
                       e.target == expected and (e.lo, e.hi) == (offset, offset+width)
                       for e in moves(world, projected))
            if width == 3:
                places = sorted(before[lo].index(x) for x in support)
                assert places[-1] - places[0] == 2
            else:
                assert local[1][::-1] in before[lo] and local[0][::-1] in before[lo]
                assert before[lo].index(local[1][::-1]) < before[lo].index(local[0][::-1])
            if name == 'A':
                prefix_weight += 1
            if name == 'D':
                score += prefix_weight * (f in raw[:lo])
            raw = raw[:lo] + local[::-1] + raw[lo+width:]
        assert list(states('hgfedcba', raw))[12] == cut
        return raw, score

    early = set(''.join(history[10:12]))
    late = set(''.join(history[20:22]))
    assert not early & late and pattern(cut, early) == 'GGSSSSGG'
    assert cut[-2:] == f
    source, first = replay('CDAB')
    target, second = replay('CADB')
    assert source == target and (first, second) == (0, 1)
    print('Replayed both eight-strand schedules at cgehbdaf; the selected '
          'inner pair contributes zero and one to the filtered count.')


if __name__ == '__main__':
    check_mixed_windows()
    check_seven()
    check_patterns()
    check_rectangle()
