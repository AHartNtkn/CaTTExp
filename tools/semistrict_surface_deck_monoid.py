"""Check directed top counts, units and translated Wang-tile readings."""
from argparse import ArgumentParser
from collections import Counter
from itertools import product
from pathlib import Path

from catt import comp2, infer, subst_tm, v
from emit_agda import Emitter
from semistrict_surface_cover_transport import context, reader
from semistrict_surface_directed_top_counts import linear_system
from semistrict_surface_penultimate_intervals import check
from semistrict_surface_reversible_five import quotient


def decisions(relations, steps, targets):
    queries = []
    for target in targets:
        _, _, equation = linear_system(relations, steps, target).partition('\n')
        queries.append(f'(push)\n{equation}\n(check-sat)\n(pop)')
    answers = check('(set-logic QF_LIA)\n' + '\n'.join(queries)).splitlines()
    assert len(answers) == len(targets) and set(answers) <= {'sat', 'unsat'}
    return [answer == 'sat' for answer in answers]


def unit_check(period, plain_step):
    # Two cycles of free sphere names z_i and w_i with one-way z_i -> w_i bridges.
    # In layer z the forward move also adds the local Hopf class h_i.
    size = 3 * period

    def step(start, end, hopf=None):
        row = [0] * size
        row[start] -= 1
        row[end] += 1
        if hopf is not None:
            row[2 * period + hopf] += 1
        return row

    cycles, bridges, relations = [], [], []
    for i in range(period):
        j = (i + 1) % period
        cycles.extend([step(i, j, i), step(period + i, period + j)])
        if plain_step:
            cycles.append(step(i, j))
        bridges.append(step(i, period + i))
        row = [0] * size
        row[2 * period + i] = 2
        relations.append(row)
    steps = cycles + bridges
    masks = [[0] * (2 * period) + list(bits) for bits in product(range(2), repeat=period)]
    inverses = [[-value for value in row] for row in steps]
    answers = decisions(relations, steps, inverses + masks)
    # Every cycle move has an inverse by going around twice. The total w mass
    # grows strictly on bridges and is constant on all other moves.
    assert answers[:len(steps)] == [True] * len(cycles) + [False] * len(bridges)
    for mask, answer in zip(masks, answers[len(steps):], strict=True):
        assert answer == (not any(quotient(relations + cycles, mask)))
        # Without the plain z step a zero free difference requires the same
        # total count at every sheet, so only constant parity masks can occur.
        assert answer == (plain_step or len(set(mask[2 * period:])) == 1)
    return len(answers)


def tile_chain(tile, x, y):
    north, east, south, west = tile
    row = Counter()
    for dx, dy, axis, colour, sign in [(0, 1, 'H', north, 1), (1, 0, 'V', east, 1),
                                      (0, 0, 'H', south, -1), (0, 0, 'V', west, -1)]:
        if colour:
            row[x + dx, y + dy, axis, colour] += sign
    return row


def bounded_tile_sum(tiles, target, budget):
    """Test an infinite-sheet tile query with at most budget occurrences."""
    if budget < 0:
        raise ValueError('expected a nonnegative occurrence budget')
    target = {key: value for key, value in target.items() if value}
    if not target:
        return True
    xs, ys = zip(*[(x, y) for x, y, _, _ in target], strict=True)
    xs = range(min(xs) - budget, max(xs) + budget + 1)
    ys = range(min(ys) - budget, max(ys) + budget + 1)
    placements = [tile_chain(tile, x, y) for tile, x, y in product(tiles, xs, ys)]
    keys = sorted(set(target).union(*placements))
    # Slack turns the cost bound into one extra integer equation.
    steps = [[p[key] for key in keys] + [1] for p in placements]
    steps.append([0] * len(keys) + [1])
    face = [target.get(key, 0) for key in keys] + [budget]
    return decisions([], steps, [face])[0]


def tile_check():
    cases = 0
    # Assign colours to entire grid lines. All interior edges of a rectangle
    # then match; the independently constructed reading uses only its perimeter.
    for width, height, x, y in product(range(1, 5), range(1, 4), (-2, 0, 3), (-3, 1)):
        row, boundary = Counter(), Counter()
        for i, j in product(range(x, x + width), range(y, y + height)):
            row.update(tile_chain(((j+1) % 3, (i+1) % 4, j % 3, i % 4), i, j))
        for j in range(y, y + height):
            if x % 4:
                boundary[x, j, 'V', x % 4] -= 1
            if (x + width) % 4:
                boundary[x + width, j, 'V', (x + width) % 4] += 1
        for i in range(x, x + width):
            if y % 3:
                boundary[i, y, 'H', y % 3] -= 1
            if (y + height) % 3:
                boundary[i, y + height, 'H', (y + height) % 3] += 1
        assert row == boundary
        cases += 1
    # A mismatched shared edge must retain both colours with opposite signs.
    row = tile_chain((0, 1, 0, 0), -1, 0)
    row.update(tile_chain((0, 0, 0, 2), 0, 0))
    assert row == Counter({(0, 0, 'V', 1): 1, (0, 0, 'V', 2): -1})
    return cases


def raw_faces(sphere_rank, emitter=None):
    # The common edge spine visits 0, X, 0, Y. The four sphere slots
    # name the north, east, south and west colours of a generic tile.
    small, unit = context(2, sphere_rank)
    ctx = small + (small[-1],) * 3
    first = len(small) - 1
    north, east, south, west = (v(first + i) for i in range(4))

    def paste(s, w, e, n):
        terms = (s, w, v(1), e, v(3), v(2), n)
        result = terms[0]
        for term in terms[1:]:
            result = comp2(ctx, 0, result, term)
        return result

    before, after = paste(south, west, unit, unit), paste(unit, unit, east, north)
    common_type = infer(ctx, before)
    assert common_type == infer(ctx, after)
    if emitter is not None:
        emitter.check_type(f'source{sphere_rank}', ctx, before, common_type)
        emitter.check_type(f'target{sphere_rank}', ctx, after, common_type)
    # Project to each sphere name and use the generic strict-slot reader.
    shifts = [[3*y + (x+1) % 3 for y, x in product(range(3), repeat=2)],
              [3*((y+1) % 3) + x for y, x in product(range(3), repeat=2)]]
    read = reader(shifts, sphere_rank)
    expected = ((1, 1), (0, 1), (None, -1), (None, -1))
    for index, (axis, sign) in enumerate(expected):
        sub = tuple(v(i) for i in range(first)) + tuple(
            v(first) if i == index else unit for i in range(4))
        a, b = subst_tm(before, sub), subst_tm(after, sub)
        assert infer(small, a) == infer(small, b)
        for sheet in range(9):
            end, value = read(b, sheet)
            begin_end, before_value = read(a, sheet)
            assert begin_end == end == shifts[1][sheet]
            value.subtract(before_value)
            address = sheet if axis is None else shifts[axis][sheet]
            assert value == Counter({address: sign})
    return 4 * 9


def budget_check():
    # Production and reception of the same vertical-edge colour one step east.
    east = (0, 1, 0, 1)
    cases = 0
    for dx, dy, budget in product(range(-1, 4), (0, 1), range(4)):
        target = Counter({(-2, -1, 'V', 1): -1})
        target[dx - 2, dy - 1, 'V', 1] += 1
        assert bounded_tile_sum([east], target, budget) == (dy == 0 and 0 <= dx <= budget)
        cases += 1
    return cases


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda_dir else None
    count = sum(unit_check(period, plain) for period, plain in product(range(1, 6), (False, True)))
    print(f'{count} positive membership queries matched the cycle and unit-subgroup calculations.')
    print(f'{tile_check()} translated Wang-tile patches matched their perimeter, and the mismatch persisted.')
    readings = raw_faces(4, emitter) + raw_faces(5, emitter)
    print(f'{readings} signed tile coefficients checked at the sheets of literal parallel raw faces.')
    print(f'{budget_check()} infinite-sheet budget decisions matched directed path lengths.')
    if emitter is not None:
        (args.agda_dir / 'DeckTileFaces.agda').write_text(emitter.module('DeckTileFaces', __doc__))
