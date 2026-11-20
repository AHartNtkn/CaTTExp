"""Recover all codimension-one cube cells and print the residual six-cube lifting tests."""
import argparse
import json
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, product
from pathlib import Path

from gray_cube_path_intervals import inversions
from gray_globe_comparison import atom, strict_cells


# A cubical face is (moving axes, axes fixed at one), both bitmasks in tensor order.
def pack_cell(cell):
    def pack(g):
        return (sum(1 << i for i, z in enumerate(g) if z[0]),
                sum(1 << i for i, z in enumerate(g) if z == (0, 1)))
    return tuple(tuple(tuple(sorted(pack(g) for g in chain)) for chain in pair) for pair in cell)


def insert_bit(mask, axis):
    low = (1 << axis)-1
    return (mask & low) | ((mask & ~low) << 1)


def delete_bit(mask, axis):
    low = (1 << axis)-1
    return (mask & low) | ((mask >> 1) & ~low)


@cache
def omit(cell, axis):
    return tuple(tuple(tuple(sorted((delete_bit(d, axis), delete_bit(b, axis)) for d, b in row
                                    if not d & (1 << axis))) for row in pair) for pair in cell)


@cache
def inflated(chain, axis):
    return tuple((insert_bit(d, axis), insert_bit(b, axis)) for d, b in chain)


def compatible_tests(options):
    order = sorted(range(len(options)), key=lambda i: len(options[i]))
    chosen = {}

    def extend():
        if len(chosen) == len(order):
            yield tuple(chosen[i] for i in range(len(order)))
            return
        j = order[len(chosen)]
        for candidate in options[j]:
            if all(omit(candidate, i-int(i > j)) == omit(value, j-int(j > i))
                   for i, value in chosen.items()):
                chosen[j] = candidate
                yield from extend()
                del chosen[j]
    return extend()


def lower_chain(tests, degree, side):
    positions = defaultdict(int)
    for axis, cell in enumerate(tests):
        for directions, ones in inflated(cell[degree][side], axis):
            positions[directions] |= ones
    return tuple(sorted(positions.items()))


@cache
def differential(chain):
    result = Counter()
    for directions, ones in chain:
        axes = directions
        sign = 1
        while axes:
            bit = axes & -axes
            axes ^= bit
            result[directions ^ bit, ones | bit] += sign
            result[directions ^ bit, ones] -= sign
            sign = -sign
    return result


def boundary_equals(chain, pair):
    rhs = Counter(pair[1])
    rhs.subtract(pair[0])
    return differential(chain) == rhs


def recover(tests, pinned_axis, pinned_side):
    n = len(tests)
    full = (1 << n)-1
    rows = tuple(tuple(lower_chain(tests, d, side) for side in (0, 1)) for d in range(n-1))
    if not all(len(chain) == 1 for chain in rows[0]):
        return
    if not all(boundary_equals(chain, lower) for lower, pair in zip(rows, rows[1:]) for chain in pair):
        return
    other = [i for i in range(n) if i != pinned_axis and tests[i][-1][0]]
    for sides in product((0, 1), repeat=len(other)):
        labels = ((pinned_axis, pinned_side), *zip(other, sides))
        top = tuple(sorted((full ^ (1 << i), side << i) for i, side in labels))
        if not boundary_equals(top, rows[-1]):
            continue
        cell = rows + ((top, top),)
        if all(omit(cell, i) == value for i, value in enumerate(tests)):
            yield cell


def all_codimension_one(n):
    small = [pack_cell(c) for c in strict_cells((1,)*(n-1), n-1)]
    native = pack_cell(atom(((1, 2),)*(n-1)))
    full = (1 << n)-1
    recovered = set()
    for x, side in product(range(n), (0, 1)):
        face = full ^ (1 << x), side << x
        options = []
        for i in range(n):
            if i == x:
                options.append([native])
            else:
                restricted = tuple(delete_bit(mask, i) for mask in face)
                options.append([v for v in small if any(restricted in row for row in v[-2])])
        for tests in compatible_tests(options):
            recovered.update(recover(tests, x, side))
    return recovered


def path_word(chain):
    return tuple(d.bit_length()-1 for d, b in sorted(chain, key=lambda g: g[1].bit_count()))


def signature(u, v, chain):
    positive = set()
    for d, fixed in chain:
        a, b = [i for i in u if d & (1 << i)]
        a, b = min(a, b), max(a, b)
        for z in range(a):
            if fixed & (1 << z) and u.index(b) < u.index(a) < u.index(z) and v.index(z) < v.index(a) < v.index(b):
                positive.add((z, a, b))
    return frozenset(positive)


@cache
def sector(cell_prefix):
    start, end = (row[0][1] for row in cell_prefix[0])
    if (start, end) != (0, 63):
        return 'proper face'
    u, v = map(path_word, cell_prefix[1])
    fixed = set(combinations(range(6), 2)) - (inversions(u) - inversions(v))
    if fixed:
        center = set.intersection(*(set(pair) for pair in fixed))
        assert center
        cluster = set.union(*(set(pair) for pair in fixed))
        if len(fixed) >= 2 and (min(cluster) == 0 or max(cluster) == 5):
            return 'one-sided wedge'
    source, target = (signature(u, v, row) for row in cell_prefix[2])
    assert source <= target
    changes = target - source
    five_sets = [set(combinations([j for j in range(6) if j != i], 3)) for i in range(6)]
    assert any(required <= changes for required in five_sets)
    if any(required == changes for required in five_sets):
        return 'stationary sixth axis'
    return 'moving axis in star' if fixed else 'moving axis in full interval'


@cache
def moving_four_sets(prefix):
    # Compare the actual signed three-poles after projection onto each four-set.
    poles = tuple(prefix[:-1] + ((row, row),) for row in prefix[-1])
    changed = set()
    for i, j in combinations(range(6), 2):
        if omit(omit(poles[0], j), i) != omit(omit(poles[1], j), i):
            changed.add(63 ^ (1 << i) ^ (1 << j))
    return changed


def stationary_three_poles(cell):
    changes = moving_four_sets(cell[:4])
    for directions, station in cell[-1][0]:
        x = 63 ^ directions
        if any(f & x for f in changes):
            continue
        assert changes == {directions ^ (1 << j) for j in range(6) if directions & (1 << j)}
        # All higher rows are literally in the same copy of the facet.
        for pair in cell[4:]:
            assert all(not (d & x) and (b & x) == station for row in pair for d, b in row)
        return True
    return False


def check_stationary(cell):
    """Independently reassemble each pole by sorting the exterior letter to its stationary side."""
    (directions, ones), *_ = cell[-1][0]
    x_bit = 63 ^ directions
    x = x_bit.bit_length()-1
    station = int(bool(ones & x_bit))
    u, v = map(path_word, cell[1])
    cuts = []
    for word, first in ((u, True), (v, False)):
        path = list(word)
        swaps = []
        end = 0 if station else 5
        while path.index(x) != end:
            pos = path.index(x)
            i = pos if pos < end else pos-1
            a, b = path[i:i+2]
            assert (a > b) == first
            swaps.append(((1 << a) | (1 << b), sum(1 << t for t in path[:i])))
            path[i:i+2] = [b, a]
        cuts.extend(swaps)
    inner = omit(cell, x)
    for d in range(2, len(cell)):
        for side in (0, 1):
            chain = [(a, b | ones) for a, b in inflated(inner[d][side], x)]
            if d == 2:
                chain.extend(cuts)
            assert tuple(sorted(chain)) == cell[d][side]


def check_serialization(cells):
    """Peel one matching singleton off each multiple-facet cell at the top cut."""
    outgoing = defaultdict(list)
    for cell in cells:
        if len(cell[-1][0]) == 1:
            outgoing[cell[:-2], cell[-2][0]].append(cell)
    for cell in cells:
        top = cell[-1][0]
        if len(top) == 1:
            continue
        for step in outgoing[cell[:-2], cell[-2][0]]:
            facet, = step[-1][0]
            if facet not in top:
                continue
            rest = tuple(f for f in top if f != facet)
            tail = cell[:-2] + ((step[-2][1], cell[-2][1]), (rest, rest))
            if tail in cells:
                break
        else:
            raise AssertionError(('no single-facet first step', cell))


def check_raw_transport(output):
    from catt import (arr, check_ctx, comp2, disc_tree, glue_tree, infer, maximal_vars,
                      src, sub_from, subst_tm, tgt, tree_ctx, v)
    from ct_suspension import ident
    from emit_agda import Emitter
    from relative_coherence_exchange_faces import head

    emitter = Emitter() if output else None
    disk = tree_ctx(disc_tree(2))
    slot = len(disk)-1
    x = v(slot)
    right = comp2(disk, 1, x, ident(disk, tgt(disk, x)))
    left = comp2(disk, 1, ident(disk, src(disk, x)), x)

    for station in (0, 1):
        dims = (1, 5) if station else (5, 1)
        base = tree_ctx(glue_tree(dims[0], 0, dims[1]))
        inputs = list(map(v, maximal_vars(base)))
        high, edge = (inputs[1], inputs[0]) if station else inputs
        def exterior(cell):
            pair = (edge, cell) if station else (cell, edge)
            return comp2(base, 0, *pair)
        chains = [[high], [high]]
        for side, face in enumerate((src, tgt)):
            for _ in range(4):
                chains[side].append(face(base, chains[side][-1]))
            chains[side].reverse()
        u, w = [exterior(chain[0]) for chain in chains]
        common = infer(base, u)
        assert infer(base, w) == common
        a, b, alpha, beta = map(v, range(len(base), len(base)+4))
        context = base + (common, common, arr(common, a, u), arr(common, w, b))
        check_ctx(context)
        def middle(cell):
            return comp2(context, 1, comp2(context, 1, alpha, exterior(cell)), beta)
        p, q = [middle(chain[1]) for chain in chains]
        def at(term, pole):
            return subst_tm(term, sub_from(disk, context, {slot: pole}))
        p_new, q_new = at(right, p), at(left, q)
        assert p_new != p and q_new != q
        before, after = at(head(disk, right, x), p), at(head(disk, x, left), q)
        previous = p_new, q_new
        for rank in (3, 4, 5):
            terms = tuple(comp2(context, 2, comp2(context, 2, before, middle(chain[rank-1])), after)
                          for chain in chains)
            ty = arr(infer(context, previous[0]), *previous)
            assert all(infer(context, term) == ty for term in terms)
            if rank == 3:
                poles = terms
            if emitter and rank == 5:
                emitter.check_type(f'station{station}', context, terms[0], ty)
            previous = terms
        # Attach genuine four-cells on both sides at cut three. The two
        # resulting four-faces can be chosen freely for an isolated edge.
        base_type = infer(context, poles[0])
        assert infer(context, poles[1]) == base_type
        fresh, last, incoming, outgoing = map(v, range(len(context), len(context)+4))
        extended = context + (base_type, base_type, arr(base_type, fresh, poles[0]),
                              arr(base_type, poles[1], last))
        check_ctx(extended)
        def caps(term):
            return comp2(extended, 3, comp2(extended, 3, incoming, term), outgoing)
        five = terms[0]
        ends = tuple(caps(face(context, five)) for face in (src, tgt))
        wanted = arr(infer(extended, ends[0]), *ends)
        assert infer(extended, caps(five)) == wanted
        if emitter:
            emitter.check_type(f'isolated{station}', extended, caps(five), wanted)
    if output:
        output.write_text(emitter.module(output.stem, 'Both exterior whiskerings at fixed two-poles.'))
    print('Raw CaTT: both exterior whiskerings with cut-one and cut-two corrections through rank five.', flush=True)


def check_components(requests):
    """Classify the remaining directed incidence graphs at fixed three-poles."""
    sectors = defaultdict(list)
    for cell in requests:
        sectors[cell[:-2]].append(cell[-2])
    paths = Counter()
    forks = []
    for edges in sectors.values():
        outgoing, incoming = defaultdict(set), Counter()
        vertices = set()
        for a, b in edges:
            assert b not in outgoing[a]
            outgoing[a].add(b)
            incoming[b] += 1
            vertices.update((a, b))
        start, = (v for v in vertices if not incoming[v])
        end, = (v for v in vertices if not outgoing[v])
        assert all(incoming[v] == len(outgoing[v]) == 1 for v in vertices - {start, end})
        seen = {start, end}
        lengths = []
        for first in outgoing[start]:
            v, length = first, 1
            while v != end:
                assert v not in seen
                seen.add(v)
                v, = outgoing[v]
                length += 1
            lengths.append(length)
        assert seen == vertices and sum(lengths) == len(edges)
        if len(lengths) == 1:
            paths[lengths[0]] += 1
        else:
            forks.append(sorted(lengths))
    assert paths == {2: 212, 3: 28, 4: 6} and forks == [[6, 6]]
    print(f'Remaining components: {dict(sorted(paths.items()))} paths by length and two six-edge paths with shared ends.')


def check(output):
    for n in (4, 5):
        recovered = all_codimension_one(n)
        reference = {pack_cell(c) for c in strict_cells((1,)*n, n-1) if c[-1][0]}
        assert recovered == reference
        print(f'{n}-cube: matched all {len(reference)} intrinsic {n-1}-cells against composition closure.', flush=True)
    cells = all_codimension_one(6)
    check_serialization(cells)
    counts = Counter()
    requests = []
    for cell in cells:
        group = sector(cell[:3])
        if group == 'stationary sixth axis':
            check_stationary(cell)
        if group.startswith('moving axis') and stationary_three_poles(cell):
            group = 'stationary at three-poles'
        counts[group, len(cell[-1][0])] += 1
        if group.startswith('moving axis') and len(cell[-1][0]) == 1:
            requests.append(cell)
    degree = Counter((cell[:-2], row) for cell in requests for row in cell[-2])
    remaining = []
    for cell in requests:
        if all(degree[cell[:-2], row] == 1 for row in cell[-2]):
            counts[sector(cell[:3]), 1] -= 1
            counts['isolated at four-poles', 1] += 1
        else:
            remaining.append(cell)
    requests = remaining
    check_components(requests)
    print(f'Six-cube: {len(cells)} intrinsic five-cells. Counts by number of top facets:', flush=True)
    for group in sorted({g for g, _ in counts}):
        print(group, [counts[group, k] for k in range(1, 7)])
    print(f'Residual singleton tests: {len(requests)}, in {len({c[:3] for c in requests})} pairs of two-poles.')
    print(f"Distinct ordered three-poles: {len({c[:4] for c in requests})}.")
    assert (len(cells), len(requests), len({c[:3] for c in requests}),
            len({c[:4] for c in requests})) == (4054, 544, 63, 247)
    if output:
        output.write_text(json.dumps(sorted(requests), separators=(',', ':'))+'\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--requests', type=Path, help='write signed tableaux for the residual single-facet lifts')
    parser.add_argument('--agda', type=Path, help='emit the two raw degree-five typing judgments')
    args = parser.parse_args()
    check_raw_transport(args.agda)
    check(args.requests)
