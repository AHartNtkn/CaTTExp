"""Find common four-event words for pairs of five-cell lifts in the six-cube."""
import argparse
import json
from collections import Counter, defaultdict
from functools import cache
from pathlib import Path

from catt import (arr, check_ctx, comp2, disc_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, tgt, tree_ctx, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_cube_facet_paths import packed_atom
from gray_cube_six_poles import boundary_equals
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head, string_tree


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, list) else value


def top_word(vertex, packets):
    events = vertex[-1][0]
    full = (1 << len(events))-1
    boundaries = [tuple(map(frozenset, packed_atom(6, f)[-2])) for f in events]
    predecessors = [sum(1 << j for j, (_, out) in enumerate(boundaries) if out & required)
                    for required, _ in boundaries]
    masks = [sum(1 << i for i, e in enumerate(events) if e in packet) for packet in packets]
    assert all(m.bit_count() == 5 for m in masks) and (masks[0] & masks[1]).bit_count() == 1

    @cache
    def extend(done):
        if done == full:
            return ()
        for i, event in enumerate(events):
            bit = 1 << i
            if done & bit or predecessors[i] & ~done:
                continue
            # An open packet must finish before a letter outside it is used.
            if any(done & m and m & ~done and not bit & m for m in masks):
                continue
            suffix = extend(done | bit)
            if suffix is not None:
                return (event,) + suffix
        return None

    return extend(0)


def replay(start, word):
    row = set(start)
    states = [start]
    for event in word:
        before, after = map(set, packed_atom(6, event)[-2])
        assert before <= row
        row -= before
        assert not row & after
        row |= after
        states.append(tuple(sorted(row)))
    return states


def split_core(edge, side, word, states):
    facet, = edge[-1][0]
    caps = packed_atom(6, facet)[-2]
    packet = set(caps[side])
    begin = next(i for i, e in enumerate(word) if e in packet)
    end = begin + len(packet)
    assert set(word[begin:end]) == packet
    core = edge[:3] + ((states[begin], states[end]), caps, ((facet,), (facet,)))
    assert all(boundary_equals(row, lower) for lower, pair in zip(core, core[1:]) for row in pair)
    # Recover the original five-cell on *both* sides, with the same exterior word.
    outside = word[:begin] + word[end:]
    assert tuple(tuple(sorted(row + outside)) for row in caps) == edge[-2]
    assert states[0] == edge[3][0] and states[-1] == edge[3][1]
    return begin, end


def packet_word(cell, side):
    facet, = cell[-1][0]
    # Deleting the facet's stationary axis gives the native sweep in its own cube.
    return tuple(sorted(packed_atom(6, facet)[-2][side],
                        key=lambda f: facet[0] ^ f[0], reverse=bool(side)))


def outside_word(start, events):
    unused = set(events)
    row = start
    result = []
    while unused:
        ready = [e for e in unused if set(packed_atom(6, e)[-2][0]) <= set(row)]
        assert ready
        event = min(ready)
        row = replay(row, (event,))[-1]
        result.append(event)
        unused.remove(event)
    return tuple(result)


def check_rectangles(vertex, pair):
    (first, s), (second, t) = sorted(pair, key=lambda a: -a[1])
    p, q = packet_word(first, s), packet_word(second, t)
    common, = set(p) & set(q)
    outside = set(vertex[-1][0]) - set(p) - set(q)
    start = vertex[-2][0]
    if s == t:
        if p[-1] != common:
            (first, second), (p, q) = (second, first), (q, p)
        assert p[-1] == q[0] == common
        middle = outside_word(replay(start, p[:-1])[-1], outside)
        word0 = p + middle + q[1:]
        word1 = p[:-1] + middle + q
        # Every intervening location of the distinguished event gives a
        # square leg, with a common actual three-state at either end of each path.
        for k in range(len(middle)+1):
            word = p[:-1] + middle[:k] + (common,) + middle[k:] + q[1:]
            assert replay(start, word)[-1] == vertex[-2][1]
        swaps = len(middle)
    else:
        i, j = ((63 ^ c[-1][0][0][0]).bit_length()-1 for c in (first, second))
        assert abs(i-j) == 1
        low, high = sorted((i, j))
        before = set()
        for event in outside:
            k, l = [x for x in range(6) if not event[0] & (1 << x)]
            if (k < low and high < l) == (i < j):
                before.add(event)
        prefix = outside_word(start, before)
        pi, qi = p.index(common), q.index(common)
        front = prefix + q[:qi] + p
        stop = replay(start, front+q[qi+1:])[-1]
        suffix = outside_word(stop, outside-before)
        word0 = front + q[qi+1:] + suffix
        word1 = prefix + p[:pi] + q + p[pi+1:] + suffix
        m = len(prefix) + pi + qi
        rows0, rows1 = replay(start, word0), replay(start, word1)
        assert rows0[m:m+2] == rows1[m:m+2]
        # Check all grid states obtained by interleaving the two chains on
        # each side of the shared letter, including the two degenerate grids.
        for base, left, right in ((rows0[len(prefix)], p[:pi], q[:qi]),
                                  (rows0[m+1], p[pi+1:], q[qi+1:])):
            for a in range(len(left)+1):
                for b in range(len(right)+1):
                    assert replay(base, left[:a]+right[:b])[-1] == replay(base, right[:b]+left[:a])[-1]
        swaps = pi*qi + (len(p)-pi-1)*(len(q)-qi-1)
    for word, c, sign in ((word0, first, s), (word1, second, t)):
        assert len(set(word)) == len(word) == len(vertex[-1][0])
        split_core(c, sign, word, replay(start, word))
    return swaps


def check_windows(requests):
    sectors = defaultdict(list)
    for cell in requests:
        sectors[cell[:4]].append(cell)
    counts, swaps = Counter(), Counter()
    solved = set()
    for key, edges in sectors.items():
        incident = defaultdict(list)
        for edge in edges:
            for side, row in enumerate(edge[-2]):
                incident[row].append((edge, side))
        for row, pair in incident.items():
            if len(pair) < 2:
                continue
            assert len(pair) == 2
            vertex = key + ((row, row),)
            packets = [set(packed_atom(6, c[-1][0][0])[-2][s]) for c, s in pair]
            moves = check_rectangles(vertex, pair)
            swaps[moves] += 1
            word = top_word(vertex, packets)
            assert (word is not None) == (moves == 0)
            counts[len(edges), word is not None] += 1
            if word is None:
                continue
            states = replay(key[-1][0], word)
            (i, j), (k, l) = [split_core(c, s, word, states) for c, s in pair]
            assert j-1 == k or l-1 == i
            if len(edges) == 2:
                solved.update(edges)
    assert counts == {(2, True): 48, (2, False): 164, (3, True): 12, (3, False): 44,
                      (4, True): 4, (4, False): 14, (12, True): 4, (12, False): 8}
    assert swaps == {0: 68, 6: 138, 8: 92}
    assert len(requests) == 544 and len(solved) == 96 and len(sectors) == 247
    print('Common two-block words at 48/212 two-edge path junctions, 12/56 three-edge, '
          '4/18 four-edge and 4/12 circuit junctions.')
    print(f'Checked the two factorizations and their intervening grids at all {sum(swaps.values())} junctions.')
    return [c for c in requests if c not in solved]


def check_raw(mirror, emitter):
    # The two blocks have one common four-letter; the other's neighboring
    # letter receives the compensating inverse loop. Mirror reverses cut three.
    ctx = tree_ctx(disc_tree(3))
    pole = ctx[-1]
    slot = len(ctx)-1
    ctx += (pole,)*3
    x, y, z, w = map(v, range(slot, slot+4))

    def variable(ty):
        nonlocal ctx
        var = v(len(ctx))
        ctx += (ty,)
        return var

    def arrow(a, b):
        return arr(infer(ctx, a), a, b)

    def four(a, b):
        return variable(arrow(b, a) if mirror else arrow(a, b))

    def mul(ambient, a, b):
        return comp2(ambient, 3, b, a) if mirror else comp2(ambient, 3, a, b)

    def times(a, b):
        return mul(ctx, a, b)

    def five(a, b):
        return variable(arrow(a, b))

    def generic(inputs, first, second):
        arity = tree_ctx(string_tree(3, [4]*len(inputs)))
        slots = maximal_vars(arity)
        params = list(map(v, slots))
        if mirror:
            params.reverse()
        def operation(a, b):
            return mul(arity, a, b)
        u, v_ = (expr(arity, operation, *params) for expr in (first, second))
        sigma = sub_from(arity, ctx, dict(zip(slots, reversed(inputs) if mirror else inputs)))
        return subst_tm(head(arity, u, v_), sigma)

    p, h, h_other, q = four(x, y), four(y, z), four(y, z), four(z, w)
    left, right, inverse = four(y, y), four(z, z), four(z, z)
    start, finish = four(x, z), four(y, w)
    first = five(start, times(p, h))
    second = five(times(h_other, q), finish)
    match = five(h, times(times(left, h_other), right))
    cancel = five(times(right, inverse), ident(ctx, z))
    adjusted = times(inverse, q)
    a = times(first, adjusted)
    junction = times(times(p, h), adjusted)
    open_junction = generic([p, h, adjusted],
                            lambda _, m, a, b, c: m(m(a, b), c),
                            lambda _, m, a, b, c: m(a, m(b, c)))
    replace = times(p, times(match, adjusted))
    prepare = generic([left, h_other, right, inverse, q],
                      lambda _, m, a, b, c, d, e: m(m(m(a, b), c), m(d, e)),
                      lambda _, m, a, b, c, d, e: m(a, m(b, m(m(c, d), e))))
    cancellation = times(left, times(h_other, times(cancel, q)))

    def with_unit(arity, m, a, b, c):
        middle = src(arity, c) if not mirror else tgt(arity, c)
        return m(a, m(b, m(ident(arity, middle), c)))
    unit = generic([left, h_other, q], with_unit, lambda _, m, a, b, c: m(a, m(b, c)))
    b = open_junction
    for step in (replace, times(p, prepare), times(p, cancellation), times(p, unit),
                 times(p, times(left, second))):
        b = comp2(ctx, 4, b, step)
    assert tgt(ctx, a) == src(ctx, b) == junction
    assert src(ctx, a) == times(start, adjusted) and tgt(ctx, b) == times(p, times(left, finish))
    assert top_counts(ctx, a) == Counter([first[1]])
    assert top_counts(ctx, b) == Counter(t[1] for t in (match, cancel, second))
    check_ctx(ctx)
    if emitter:
        suffix = 'Last' if mirror else 'First'
        for name, term, source, target in (('incoming', a, src(ctx, a), junction),
                                           ('outgoing', b, junction, tgt(ctx, b))):
            emitter.check_type(name+suffix, ctx, term, arrow(source, target))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('steps', type=Path, help='JSON produced by gray_cube_six_poles.py --requests')
    parser.add_argument('--agda', type=Path)
    parser.add_argument('--remaining', type=Path, help='write the remaining strict singleton tests')
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    for mirror in (False, True):
        check_raw(mirror, emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Two facet lifts with a common literal writing.'))
    remaining = check_windows([freeze(c) for c in json.loads(args.steps.read_text())])
    if args.remaining:
        args.remaining.write_text(json.dumps(sorted(remaining), separators=(',', ':'))+'\n')
    print(f'{len(remaining)} steps remain. Both orientations of the raw junction typecheck.')
