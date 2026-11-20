"""Check support and endpoint isolation on strict tableaux of products of globes."""

import argparse
from collections import defaultdict
from functools import cache

from gray_globe_comparison import boundary, strict_cells
from gray_globe_section import trim


@cache
def generator_closure(generator):
    faces = boundary(generator)
    return frozenset({generator}).union(
        *(generator_closure(face) for face, coefficient in faces.items() if coefficient)
    )


def support(cell):
    return frozenset().union(*(
        generator_closure(generator)
        for row in cell for chain in row for generator in chain
    ))


def pole(cell, cut, side):
    row = cell[cut][side]
    return trim(cell[:cut] + ((row, row),))


def check(shape):
    cells = strict_cells(shape, sum(shape))
    supports = {trim(cell): support(cell) for cell in cells}
    assert len(set(supports.values())) == len(cells)
    pairs = 0
    for cut in range(sum(shape)):
        incoming, outgoing = defaultdict(list), defaultdict(list)
        for cell in cells:
            if len(trim(cell)) <= cut + 1:
                continue
            source, target = pole(cell, cut, 0), pole(cell, cut, 1)
            assert source != target
            incoming[target].append(cell)
            outgoing[source].append(cell)

        for middle in incoming.keys() & outgoing.keys():
            for left in incoming[middle]:
                for right in outgoing[middle]:
                    upper = tuple(
                        tuple(tuple(sorted(a + b)) for a, b in zip(row, col))
                        for row, col in zip(left[cut + 1:], right[cut + 1:])
                    )
                    composite = trim(left[:cut] + ((left[cut][0], right[cut][1]),) + upper)
                    whole = supports[composite]
                    first, second = supports[trim(left)], supports[trim(right)]
                    assert first < whole and second < whole and first | second == whole
                    assert pole(composite, cut, 0) == pole(left, cut, 0)
                    assert pole(composite, cut, 1) == pole(right, cut, 1)
                    pairs += 1
    print(f"{shape}: {len(cells)} distinct supports, {pairs} nonunit binary cuts")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shape", nargs="+", type=int, metavar="DIM")
    args = parser.parse_args()
    if min(args.shape) < 0:
        parser.error("globe dimensions must be nonnegative")
    check(tuple(args.shape))
