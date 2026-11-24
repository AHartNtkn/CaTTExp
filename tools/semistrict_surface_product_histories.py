"""Check shared ordinary 3-generators over products of path categories."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import permutations, product
from pathlib import Path

from catt import STAR, arr, comp2, glue_tree, infer, maximal_vars, src, sub_from, subst_tm, tgt, tree_ctx, v
from catt_unit_ordered_exchange import record_square, temporal_words
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import head


RULES = (
    (('a', ''), ('', 'c')),
    (('', 'c'), ('ba', '')),
    (('b', 'd'), ('a', 'c')),
    (('a', 'c'), ('', '')),
    (('', ''), ('b', 'd')),
    (('', ''), ('', '')),
)


def sites(words, rule):
    choices = []
    for word, source in zip(words, RULES[rule][0], strict=True):
        choices.append([i for i in range(len(word) + 1) if word.startswith(source, i)])
    return product(*choices)


def replace(words, event):
    rule, offsets = event
    after = []
    for word, old, new, i in zip(words, *RULES[rule], offsets, strict=True):
        assert 0 <= i <= len(word) and word.startswith(old, i)
        after.append(word[:i] + new + word[i + len(old):])
    return tuple(after)


def replay(words, history):
    for event in history:
        words = replace(words, event)
    return words


def occurrence_names(start, reading):
    wires = [[(k, i) for i in range(len(word))] for k, word in enumerate(start)]
    events = []
    for rule, a in reading:
        old, new = RULES[rule]
        ports = tuple(tuple(t[i:i + len(p)]) for t, i, p in zip(wires, a, old, strict=True))
        assert any(ports)
        name = rule, ports
        for k, (i, p, q) in enumerate(zip(a, old, new, strict=True)):
            wires[k][i:i + len(p)] = [(name, k, j) for j in range(len(q))]
        events.append(name)
    assert len(events) == len(set(events))
    return tuple(events)


def switch(history, k):
    (first, a), (second, b) = history[k:k + 2]
    source, target = RULES[second]
    if any(j + len(p) > i for i, j, p in zip(a, b, source, strict=True)):
        return None
    shifted = tuple(i + len(q) - len(p) for i, p, q in zip(a, source, target, strict=True))
    return history[:k] + ((second, b), (first, shifted)) + history[k + 2:]


def tier(start, blocks, order):
    """Read one cube from its marked input intervals and its ordered gaps."""
    positions = [list(a) for _, a in blocks]
    result = []
    words = start
    for k in order:
        rule, _ = blocks[k]
        event = rule, tuple(positions[k])
        result.append(event)
        words = replace(words, event)
        for j in range(k + 1, len(blocks)):
            for tape, (p, q) in enumerate(zip(*RULES[rule], strict=True)):
                positions[j][tape] += len(q) - len(p)
    return tuple(result)


def cubes(start, size, allowed):
    def extend(minimum, chosen):
        if len(chosen) == size:
            yield chosen
            return
        for rule in allowed:
            for a in sites(start, rule):
                if all(i >= m for i, m in zip(a, minimum, strict=True)):
                    end = tuple(i + len(p) for i, p in zip(a, RULES[rule][0], strict=True))
                    yield from extend(end, chosen + ((rule, a),))
    return extend((0,) * len(start), ())


def readings(start, size, allowed):
    if size == 0:
        yield ()
    else:
        for rule in allowed:
            for a in sites(start, rule):
                event = rule, a
                for rest in readings(replace(start, event), size - 1, allowed):
                    yield (event,) + rest


def statistics():
    counts = Counter()
    for start in (('', ''), ('ab', 'cd'), ('aa', 'cc'), ('b', 'cc')):
        for allowed in (range(4), range(6)):
            reverse_readings = set()
            for blocks in cubes(start, 3, allowed):
                orders = {p: tier(start, blocks, p) for p in permutations(range(3))}
                assert len({replay(start, h) for h in orders.values()}) == 1
                reverse_readings.add(orders[2, 1, 0])
                for p, h in orders.items():
                    for k in range(2):
                        if p[k] > p[k + 1]:
                            exchanged = p[:k] + (p[k + 1], p[k]) + p[k + 2:]
                            assert switch(h, k) == orders[exchanged]
                counts['literal triple cubes'] += 1
            seen = set()
            sinks = {}
            for h in readings(start, 3, allowed):
                counts['three-step readings'] += 1
                moves = [switch(h, k) for k in range(2)]
                if all(m is not None for m in moves):
                    seen.add(h)
                    assert h in reverse_readings
                for m in moves:
                    if m is not None:
                        assert replay(start, m) == replay(start, h)
                if len(allowed) == 4:
                    def normal(path):
                        if path not in sinks:
                            outgoing = [m for k in range(2) if (m := switch(path, k)) is not None]
                            grade = tuple(sum(a) for _, a in path)
                            assert all(tuple(sum(a) for _, a in m) < grade for m in outgoing)
                            names = occurrence_names(start, path)
                            for i in range(2):
                                m = switch(path, i)
                                if m is not None:
                                    assert occurrence_names(start, m) == (
                                        names[:i] + (names[i + 1], names[i]) + names[i + 2:])
                            values = {normal(m) for m in outgoing} or {path}
                            assert len(values) == 1
                            sinks[path] = values.pop()
                        return sinks[path]
                    normal(h)
            assert seen == reverse_readings
            counts['positive-input normalizations'] += len(sinks)
    # In disjoint tapes these two redexes are placed in opposite
    # orders by their gaps. Neither ordering of a spatial tier fits.
    blocked = ((0, (1, 0)), (1, (0, 1)))
    replay(('ba', 'c'), blocked)
    assert switch(blocked, 0) is None
    assert not any(blocked == tier(('ba', 'c'), c, p) for c in cubes(('ba', 'c'), 2, (0, 1))
                   for p in permutations(range(2)))
    # Both occurrences of the nullary loop at the empty tuple are the
    # same declaration. Its one elementary exchange is a nonzero braid.
    scalar = tuple(readings(('', ''), 2, (5,)))
    assert len(scalar) == 1 and switch(scalar[0], 0) == scalar[0]
    print(dict(counts))


PLANAR = ((1, 2), (2, 1), (1, 1))


@cache
def planar(start, history):
    """The port diagram of split, join and unary boxes on one spatial letter."""
    wires = [(i,) for i in range(start)]
    boxes = set()
    for rule, i in history:
        inputs, outputs = PLANAR[rule]
        assert 0 <= i <= len(wires) - inputs
        box = rule, tuple(wires[i:i + inputs])
        assert box not in boxes
        boxes.add(box)
        wires[i:i + inputs] = [(box, j) for j in range(outputs)]
    return start, frozenset(boxes), tuple(wires)


@cache
def planar_lists(start, length):
    if length == 0:
        return ((),)
    return tuple(((rule, i),) + tail for rule, (p, q) in enumerate(PLANAR)
                 for i in range(start + 1 - p) for tail in planar_lists(start + q - p, length - 1))


def check_cancellation():
    # Group independent serializations by their full ordered-port diagrams.
    left, right = {}, {}
    instances = 0
    for start, length in product(range(1, 4), range(1, 5)):
        for reading in planar_lists(start, length):
            diagram = planar(start, reading)
            for cut in range(1, length):
                prefix = planar(start, reading[:cut])
                suffix = planar(len(prefix[2]), reading[cut:])
                assert left.setdefault((prefix, diagram), suffix) == suffix
                assert right.setdefault((diagram, suffix), prefix) == prefix
                instances += 1
    # In the planar hom the composite of these two unary boxes has
    # two prefixes of the same degree, with the same generator name.
    l, r = ((2, 0),), ((2, 1),)
    assert planar(2, l + r) == planar(2, r + l) and planar(2, l) != planar(2, r)
    # Two local R => R rules in succession, with the first factorization
    # L;[R] and the second [R];L. The degree inequality would allow the
    # forward switch, but R cannot left-divide L (their lengths agree).
    assert not any(planar(2, r + gap) == planar(2, l) for gap in planar_lists(2, 0))
    print(f'{instances} cuts checked for both cancellations in path-changing planar diagrams')


def check_boundary(directory):
    ctx = (STAR, STAR, STAR, arr(STAR, v(0), v(1)), arr(STAR, v(1), v(2)))
    f, g = v(3), v(4)
    ctx += (arr(ctx[3], f, f), arr(ctx[4], g, g))
    left, right = comp2(ctx, 0, v(5), g), comp2(ctx, 0, f, v(6))
    double = comp2(ctx, 1, right, right)
    assert infer(ctx, left) == infer(ctx, right) == infer(ctx, double)
    ctx += (arr(infer(ctx, left), left, right), arr(infer(ctx, right), right, double))
    pair = tree_ctx(glue_tree(3, 1, 3))
    peaks = maximal_vars(pair)
    early, late = temporal_words(pair, *map(v, peaks), 1, 2)
    back, forth = head(pair, late, early), head(pair, early, late)
    loop = comp2(pair, 3, forth, back)
    unit = ident(pair, early)
    generic = head(pair, loop, unit)
    label = sub_from(pair, ctx, dict(zip(peaks, (v(7), v(8)), strict=True)))
    raw = subst_tm(generic, label)
    actual = tuple(subst_tm(t, label) for t in (loop, unit))
    required = arr(infer(ctx, actual[0]), *actual)
    assert infer(ctx, raw) == required and actual[0] != actual[1]
    emitter = Emitter()
    emitter.check_typed('shared', ctx, raw)
    emitter.check_type('shared-boundary', ctx, raw, required)
    # Two states of the transfer rule, with one generating higher change.
    ctx += (ctx[7], arr(ctx[7], v(7), v(9)))
    moving = tree_ctx(glue_tree(4, 1, 3))
    change, other = map(v, maximal_vars(moving))
    def beside(x, y):
        return comp2(moving, 1, x, y)
    first, last = src(moving, change), tgt(moving, change)
    def exchange(t):
        return subst_tm(forth, sub_from(pair, moving, dict(zip(peaks, (t, other), strict=True))))
    early_change = comp2(moving, 2, beside(change, src(moving, other)), beside(tgt(moving, first), other))
    late_change = comp2(moving, 2, beside(src(moving, first), other), beside(change, tgt(moving, other)))
    x = comp2(moving, 3, exchange(first), late_change)
    y = comp2(moving, 3, early_change, exchange(last))
    labels = sub_from(moving, ctx, dict(zip(maximal_vars(moving), (v(10), v(8)), strict=True)))
    record_square(emitter, 'label-change', ctx, labels, x, y, head(moving, x, y))
    if directory:
        directory.mkdir(parents=True, exist_ok=True)
        module = 'SharedOrdinaryHistories'
        (directory / (module + '.agda')).write_text(emitter.module(module, __doc__))
    print('Both raw 5-cells at the specified spanning-rule and label-change boundaries')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    options = parser.parse_args()
    statistics()
    check_cancellation()
    check_boundary(options.agda_dir)
