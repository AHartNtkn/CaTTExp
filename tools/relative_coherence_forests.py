"""Check the occurrence forests and the four-dimensional example in Response 12."""
import argparse
from functools import cache
from itertools import combinations, product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, fv_tm, fv_ty, infer, tdim_tm, v
from emit_agda import Emitter


def nonempty_subsets(items):
    for size in range(1, len(items) + 1):
        yield from combinations(items, size)


def word_histories(width, outputs):
    """Enumerate actual disjoint binary and ternary matches on unlabelled words."""
    if width == outputs:
        yield ()
        return
    matches = [(i, n) for i in range(width) for n in (2, 3) if i + n <= width]
    for tier in nonempty_subsets(matches):
        if any(i + n > j for (i, n), (j, _) in zip(tier, tier[1:])):
            continue
        new_width = width - sum(n - 1 for _, n in tier)
        if new_width >= outputs:
            for tail in word_histories(new_width, outputs):
                yield (tier,) + tail


def trace_leaves(width, history):
    slots = [(i, i + 1) for i in range(width)]
    schedule = []
    for tier in history:
        intervals = tuple((slots[i][0], slots[i + n - 1][1]) for i, n in tier)
        for (i, n), interval in reversed(tuple(zip(tier, intervals))):
            slots[i:i + n] = [interval]
        schedule.append(intervals)
    return tuple(schedule)


@cache
def trees(lo, hi):
    """Generate plane trees independently by cutting their ordered leaf interval."""
    if hi == lo + 1:
        return (frozenset(),)
    result = []
    for arity in (2, 3):
        for cuts in combinations(range(lo + 1, hi), arity - 1):
            ends = (lo,) + cuts + (hi,)
            children = [trees(a, b) for a, b in zip(ends, ends[1:])]
            for parts in product(*children):
                result.append(frozenset({(lo, hi)}).union(*parts))
    return tuple(result)


def frontier_schedules(nodes):
    if not nodes:
        yield ()
        return
    ready = sorted((a, b) for a, b in nodes
                   if not any(a <= i and j <= b and (i, j) != (a, b) for i, j in nodes))
    for tier in nonempty_subsets(ready):
        for tail in frontier_schedules(nodes.difference(tier)):
            yield (tier,) + tail


def check_forests(width, outputs):
    histories = {}
    for history in word_histories(width, outputs):
        schedule = trace_leaves(width, history)
        assert schedule not in histories
        histories[schedule] = history
    expected = set()
    forest_count = 0
    for cuts in combinations(range(1, width), outputs - 1):
        ends = (0,) + cuts + (width,)
        for roots in product(*(trees(a, b) for a, b in zip(ends, ends[1:]))):
            forest_count += 1
            for schedule in frontier_schedules(frozenset().union(*roots)):
                assert schedule not in expected
                expected.add(schedule)
    assert set(histories) == expected
    facets = 0
    for schedule, history in histories.items():
        for j, tier in enumerate(history):
            for early in nonempty_subsets(tier):
                if len(early) == len(tier):
                    continue
                # A preceding match shortens the word seen by the late matches.
                late = tuple((i - sum(n - 1 for k, n in early if k < i), size)
                             for i, size in tier if (i, size) not in early)
                split = history[:j] + (early, late) + history[j + 1:]
                first = tuple(node for match, node in zip(tier, schedule[j]) if match in early)
                second = tuple(node for node in schedule[j] if node not in first)
                assert histories[schedule[:j] + (first, second) + schedule[j + 1:]] == split
                facets += 1
    print(f"{width} inputs, {outputs} outputs: {forest_count} forests, "
          f"{len(histories)} chart strings, {facets} facet incidences")


def four_cell():
    context = (STAR,)
    x = v(0)

    def declare(source, target):
        nonlocal context
        ty = infer(context, source)
        assert ty == infer(context, target)
        result = v(len(context))
        context += (arr(ty, source, target),)
        return result

    f = declare(x, x)
    p = declare(f, f)
    a = declare(p, p)
    z = declare(comp2(context, 2, a, a), a)
    pair = comp2(context, 2, z, z)
    term = comp2(context, 3, pair, z)
    check_ctx(context)
    assert tdim_tm(context, term) == 4
    support = set(fv_tm(term))
    for i in reversed(range(len(context))):
        if i in support:
            support.update(fv_ty(context[i]))
    assert support == set(range(len(context)))
    return context, term


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    ctx, witness = four_cell()
    if args.agda:
        emitter = Emitter()
        emitter.check_typed("branching-four-cell", ctx, witness)
        args.agda.write_text(emitter.module(args.agda.stem, "An atomic-target branching four-cell."))
    for output_count in (1, 2):
        check_forests(7, output_count)
