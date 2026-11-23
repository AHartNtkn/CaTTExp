"""Check oriented top slots and emit a raw witness for a converted 4-boundary."""

from argparse import ArgumentParser
from collections import Counter
from pathlib import Path
from itertools import product

from catt import STAR, arr, comp2, infer, v
from emit_agda import Emitter
from partial_cylinder_steiner import globular, trees
from relative_coherence_exchange_faces import reassociate
from relative_coherence_hidden_seam import identity
from relative_coherence_slots import tableaux, transport_slots


def check_slots(limit):
    counts = Counter()
    for edges in range(limit + 1):
        for tree in trees(edges):
            cells = {x: (d, s, t) for x, d, s, t in globular(tree)}
            if max(d for d, _, _ in cells.values()) != 4:
                continue
            slots = transport_slots(cells, 3)
            step = {s: t for d, s, t in cells.values() if d == 4}
            for rows in tableaux(cells, 4):
                source, target = rows[3]
                finish = {slots[key]: key for key in target}
                assert set(finish) == {slots[key] for key in source}
                for key in source:
                    while key != finish[slots[key]]:
                        key = step[key]
                        counts["forward slot steps"] += 1
                counts["strict 4-cells"] += 1
    return counts


def column(events, tag):
    # Each state is a path of 1-arrows. Each event is an ordered list of
    # primitive steps with explicit left and right whiskers.
    states = [((tag, i),) for i in range(events + 1)]
    blocks = [(((), (tag, j), ()),) for j in range(events)]
    return states, blocks


def run_columns(columns):
    states = [states[0] for states, _ in columns]
    result = []
    for i, (path, blocks) in enumerate(columns):
        for j, block in enumerate(blocks):
            assert states[i] == path[j]
            left = sum(states[:i], ())
            right = sum(states[i + 1:], ())
            result.extend((left + l, event, r + right) for l, event, r in block)
            states[i] = path[j + 1]
    return result


def check_insertions():
    checks = Counter()
    for left_size, right_size in product(range(3), repeat=2):
        left = column(left_size, "left")
        right = column(right_size, "right")
        for width in range(4):
            for heights in product(range(3), repeat=width):
                inner = [column(n, ("inner", k)) for k, n in enumerate(heights)]
                first = sum((path[0] for path, _ in inner), ())
                last = sum((path[-1] for path, _ in inner), ())
                block = run_columns(inner)
                outer = ([first, last], [block])
                assert run_columns([left, outer, right]) == run_columns([left, *inner, right])
                checks["whole-column insertions"] += 1
                if width == 1:
                    before, after = column(1, "before"), column(1, "after")
                    wrapped = ([before[0][0], first, last, after[0][-1]],
                               before[1] + [block] + after[1])
                    spliced = ([before[0][0], *inner[0][0], after[0][-1]],
                               before[1] + inner[0][1] + after[1])
                    assert run_columns([left, wrapped, right]) == run_columns([left, spliced, right])
                    checks["within-column insertions"] += 1
    return checks


def directed_example():
    ctx = (STAR,)
    unit = identity(ctx, v(0))
    scalar_type = arr(infer(ctx, unit), unit, unit)
    ctx += (scalar_type,)
    letter = arr(scalar_type, v(1), v(1))
    ctx += (letter,) * 4
    r, s, t, d = map(v, range(2, 6))
    left = comp2(ctx, 2, comp2(ctx, 2, r, s), t)
    right = comp2(ctx, 2, r, comp2(ctx, 2, s, t))
    ctx += (arr(letter, left, d),)
    assert left != right and infer(ctx, left) == infer(ctx, right)
    witness = comp2(ctx, 3, reassociate(ctx, (r, s, t), True), v(6))
    expected = arr(letter, right, d)
    assert infer(ctx, witness) == expected
    emitter = Emitter()
    emitter.check_typed("directed", ctx, witness)
    emitter.check_type("directed", ctx, witness, expected)
    return emitter


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--edges", type=int, default=8)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    for name, total in sorted((check_slots(args.edges) + check_insertions()).items()):
        print(f"{total:,} {name}")
    emitter = directed_example()
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, "A directed 4-cell at a rebracketed boundary."))
    print("Directed 4-term checks at the prescribed right-bracketed source.")
