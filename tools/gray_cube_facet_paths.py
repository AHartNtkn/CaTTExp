"""Read the possible codimension-one steps of a cube from one signed ridge row."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations
from pathlib import Path

from gray_cube_six_poles import (all_codimension_one, boundary_equals, compatible_tests,
                                 delete_bit, lower_chain, omit, pack_cell)
from gray_globe_comparison import atom, strict_cells


def negative_station(missing, axis):
    """Station of axis in the negative hemisphere of the facet missing 'missing'."""
    return (axis - int(missing < axis)) % 2


def ridge_positions(n, row):
    full = (1 << n)-1
    return {full ^ directions: ones for directions, ones in row}


def activity(n, positions):
    """Uniform bits can flip. A mixed or absent collection stays fixed."""
    bits = {}
    for i in range(n):
        values = set()
        for j in range(n):
            if j == i:
                continue
            pair = (1 << i) | (1 << j)
            if pair not in positions:
                break
            values.add(((positions[pair] >> j) & 1) ^ negative_station(i, j))
        else:
            if len(values) == 1:
                bits[i], = values
    return bits


def neighbors(n, row, old_bit):
    """Return all outgoing (old_bit=0) or incoming (old_bit=1) labelled edges."""
    full = (1 << n)-1
    positions = ridge_positions(n, row)
    bits = activity(n, positions)
    for i, value in bits.items():
        if value != old_bit:
            continue
        fixed = {(ones >> i) & 1 for pair, ones in positions.items() if pair & (1 << i)}
        if len(fixed) != 1:
            continue
        station, = fixed
        new = positions.copy()
        for j in range(n):
            if i != j:
                new[(1 << i) | (1 << j)] ^= 1 << j
        new_row = tuple(sorted((full ^ pair, ones) for pair, ones in new.items()))
        yield (full ^ (1 << i), station << i), new_row


def check_component(n, vertices, edges):
    first = next(iter(vertices))
    labels = sorted(activity(n, ridge_positions(n, first)))
    bits_by_vertex = {}
    for row in vertices:
        bits = activity(n, ridge_positions(n, row))
        assert sorted(bits) == labels
        word = tuple(bits[i] for i in labels)
        assert word == tuple(sorted(word)) or word == tuple(sorted(word, reverse=True))
        bits_by_vertex[row] = word
    assert len(set(bits_by_vertex.values())) == len(vertices)
    uses = Counter()
    for source, facet, target in edges:
        a, b = bits_by_vertex[source], bits_by_vertex[target]
        axis = (((1 << n)-1) ^ facet[0]).bit_length()-1
        pos = labels.index(axis)
        assert a[pos] == 0 and b[pos] == 1 and a[:pos]+a[pos+1:] == b[:pos]+b[pos+1:]
        uses[axis] += 1
    if len(labels) < n:
        assert len({a for a, _, _ in edges}) == len({b for _, _, b in edges}) == len(edges)
        assert max(uses.values()) == 1 and len(edges) == len(vertices)-1
        return False
    assert len(vertices) == len(edges) == 2*n
    assert uses == Counter({i: 2 for i in range(n)})
    start, = (row for row in vertices if not any(bits_by_vertex[row]))
    outgoing = defaultdict(list)
    for a, facet, b in edges:
        outgoing[a].append((facet, b))
    routes = []
    for facet, row in outgoing[start]:
        route = [facet]
        while outgoing[row]:
            (facet, row), = outgoing[row]
            route.append(facet)
        routes.append(route)
    # The two complete routes have precisely the native atom's two signed
    # hemisphere chains. The order is forced separately by the directed graph.
    hemispheres = native(n)[-2]
    assert {tuple(sorted(path)) for path in routes} == set(hemispheres)
    axis_orders = [tuple((((1 << n)-1) ^ d).bit_length()-1 for d, _ in path) for path in routes]
    assert set(axis_orders) == {tuple(range(n)), tuple(reversed(range(n)))}
    return True


@cache
def native(n):
    return pack_cell(atom(((1, 2),)*n))


def check(n, five_axis_exceptions):
    candidates = (all_codimension_one(n) if n == 6
                  else map(pack_cell, strict_cells((1,)*n, n-1)))
    if n == 6:
        check_six_axis_peaks(candidates, five_axis_exceptions)
    sectors = defaultdict(set)
    for cell in candidates:
        top = cell[-1][0]
        if len(top) == 1:
            a, b = cell[-2]
            sectors[cell[:-2]].add((a, top[0], b))
    components = Counter()
    edge_count = 0
    for strict_edges in sectors.values():
        edge_count += len(strict_edges)
        incident = defaultdict(set)
        for a, facet, b in strict_edges:
            edge = (a, facet, b)
            incident[a].add(edge)
            incident[b].add(edge)
        # Compare signed enabledness with strict cells obtained without the bit rule.
        for row, edges in incident.items():
            assert {(row, f, b) for f, b in neighbors(n, row, 0)} == {e for e in edges if e[0] == row}
            assert {(a, f, row) for f, a in neighbors(n, row, 1)} == {e for e in edges if e[2] == row}
        unseen = set(incident)
        while unseen:
            stack = [next(iter(unseen))]
            vertices, edges = set(), set()
            while stack:
                row = stack.pop()
                if row in vertices:
                    continue
                vertices.add(row)
                for edge in incident[row]:
                    edges.add(edge)
                    stack.extend((edge[0], edge[2]))
            unseen -= vertices
            cycle = check_component(n, vertices, edges)
            components['cycle' if cycle else 'path'] += 1
    assert components['cycle'] == 1
    print(f'{n}-cube: {edge_count} facet steps, {components["path"]} path components and one {2*n}-edge cycle.', flush=True)


def transverse(n, cell, marked):
    """Keep cofaces of a set of moving axes. Reflect remaining axes by Koszul parity."""
    kept = [i for i in range(n) if not (marked >> i) & 1]
    reverse = sum(1 << i for i in kept if (marked & ((1 << i)-1)).bit_count() % 2)

    def compact(mask):
        return sum(1 << j for j, i in enumerate(kept) if mask & (1 << i))

    def chain(row):
        return tuple(sorted((compact(d), compact(b ^ (reverse & ~d))) for d, b in row
                            if d & marked == marked))
    result = tuple(tuple(chain(row) for row in pair) for pair in cell[marked.bit_count():])
    if not any(row for pair in result for row in pair):
        return None
    assert len(result[0][0]) == len(result[0][1]) == 1
    return result


@cache
def packed_atom(n, face):
    d, b = face
    return pack_cell(atom(tuple((1, 2) if d & (1 << i) else (0, (b >> i) & 1) for i in range(n))))


def check_slices():
    # All classes of tableaux, including composites and identity padding.
    by_size = {n: {pack_cell(c) for c in strict_cells((1,)*n, n)} for n in (1, 2, 3, 4, 5)}
    active = 0
    for n in (3, 4, 5):
        for cell in by_size[n]:
            for i in range(n):
                image = transverse(n, cell, 1 << i)
                if image is not None:
                    assert image in by_size[n-1]
                    active += 1
        assert all(transverse(n, native(n), m) == native(n-m.bit_count())
                   for m in range(1, (1 << n)-1))
    print(f'Compared {active} active transverse tableaux with independent cube closure.')


def continuations(graph, start):
    # An intrinsic k-step changes one projected native k-cell from source to target.
    # It cannot repeat that direction set, so all directed paths terminate.
    active = [(start, ())]
    totals = defaultdict(set)
    while active:
        vertex, steps = active.pop()
        totals[vertex].add(tuple(sorted(steps)))
        active.extend((target, steps+(facet,)) for facet, target in graph.get(vertex, {}).items())
    return totals


def predicted_extra(n, cube, start):
    # With one spectator, each misplaced inner ridge can arrive by just one
    # exterior edge at its prescribed inner position.
    spectator = ((1 << n)-1) ^ cube[0]
    assert spectator.bit_count() == 1
    return Counter((d | spectator, ones & ~spectator) for d, ones in packed_atom(n, cube)[-3][0]
                   if (d, ones) not in start)


def check_five_axis_peaks():
    n = 5
    sectors = defaultdict(lambda: defaultdict(dict))
    for table in strict_cells((1,)*n, 3):
        cell = pack_cell(table)
        if len(cell[-1][0]) == 1:
            a, b = cell[-2]
            sectors[cell[:-2]][a][cell[-1][0][0]] = b
    fillers = defaultdict(list)
    for table in strict_cells((1,)*n, 4):
        cell = pack_cell(table)
        if len(cell[-1][0]) == 1:
            fillers[cell[:2], cell[2][0], cell[-1][0][0]].append(cell)
    counts = Counter()
    exceptions = set()
    for poles, graph in sectors.items():
        for start, edges in graph.items():
            for a, b in combinations(edges, 2):
                overlap = set(packed_atom(n, a)[-2][0]) & set(packed_atom(n, b)[-2][0])
                if not overlap:
                    continue
                axes = a[0] | b[0]
                cube = axes, a[1] & ~axes
                assert cube[1] == b[1] & ~axes
                bare = set(packed_atom(n, cube)[-3][0]) <= set(start)
                counts[bare] += 1
                if bare:
                    native_rows = packed_atom(n, cube)[3]
                    assert any(cell[3] == native_rows for cell in fillers[poles, start, cube])
                    continue
                exceptions.add((poles, start, frozenset((a, b))))
                left = continuations(graph, edges[a])
                right = continuations(graph, edges[b])
                joint = left.keys() & right.keys()
                shortest = min(min(map(len, left[v])) for v in joint)
                join, = (v for v in joint if min(map(len, left[v])) == shortest)
                assert shortest == min(map(len, right[join])) == 4
                filler, = (cell for cell in fillers[poles, start, cube] if cell[2][1] == join)
                lhs = {tuple(sorted(path+(a,))) for path in left[join]}
                rhs = {tuple(sorted(path+(b,))) for path in right[join]}
                assert any(filler[3][side] in lhs and filler[3][1-side] in rhs for side in (0, 1))
                interior = packed_atom(n, cube)[3]
                extra = [Counter(whole)-Counter(part) for whole, part in zip(filler[3], interior)]
                assert extra[0] == extra[1] == predicted_extra(n, cube, start)
                assert sum(extra[0].values()) == 1
    assert counts == {True: 80, False: 10}
    print('Five axes: 80 native overlapping peaks, 10 with a unique shortest join using one extra step per side.')
    return exceptions


def six_axis_starts(cube, steps, small):
    # The five-axis projection of a fork is the unique double negative native
    # face. Every other deletion must retain the incoming ridges it sees.
    y = (63 ^ cube[0]).bit_length()-1
    base = native(5)[:3] + ((native(5)[3][0],)*2,)
    required = {f for step in steps for f in packed_atom(6, step)[-2][0]}
    options = []
    for j in range(6):
        if j == y:
            options.append([base])
            continue
        visible = {(delete_bit(d, j), delete_bit(b, j)) for d, b in required if not d & (1 << j)}
        common = omit(base, j-int(j > y))
        options.append([c for c in small if visible <= set(c[-1][0])
                        and omit(c, y-int(y > j)) == common])
    for tests in compatible_tests(options):
        rows = tuple(tuple(lower_chain(tests, k, side) for side in (0, 1)) for k in range(4))
        if any(len(r) != 1 for r in rows[0]):
            continue
        if not all(boundary_equals(r, pair) for pair, nxt in zip(rows, rows[1:]) for r in nxt):
            continue
        if all(omit(rows, j) == c for j, c in enumerate(tests)):
            assert required <= set(rows[-1][0]) and rows[-1][0] == rows[-1][1]
            yield rows


def check_six_axis_peaks(cells, exceptions):
    small = [pack_cell(c) for c in strict_cells((1,)*5, 3)]
    fillers = defaultdict(set)
    for c in cells:
        if len(c[-1][0]) == 1:
            fillers[c[:3], c[3][0], c[-1][0][0]].add(c[4])
    counts = Counter()
    for y in range(6):
        axes = [i for i in range(6) if i != y]
        for side in (0, 1):
            cube = 63 ^ (1 << y), side << y
            # First facet of the increasing and of the decreasing sweep.
            a = cube[0] ^ (1 << axes[0]), cube[1]
            b = cube[0] ^ (1 << axes[-1]), cube[1] | (1 << axes[-1])
            for vertex in six_axis_starts(cube, (a, b), small):
                start = set(vertex[-1][0])
                extra = predicted_extra(6, cube, start)
                detected = False
                for i in axes[1:-1]:
                    image = transverse(6, vertex, 1 << i)
                    faces = frozenset(transverse(6, packed_atom(6, f), 1 << i)[-1][0][0] for f in (a, b))
                    detected |= (image[:2], image[-1][0], faces) in exceptions
                assert detected == bool(extra)
                caps = tuple(tuple(sorted((Counter(r)+extra).elements())) for r in packed_atom(6, cube)[4])
                assert caps in fillers[vertex[:3], vertex[-1][0], cube]
                counts[sum(extra.values())] += 1
    assert counts == {0: 1044, 1: 228, 2: 64, 3: 8}
    print(f'All six-axis overlapping four-step peaks have their predicted filler; counts by extra steps {dict(sorted(counts.items()))}.')


def check_cycle_terms(output):
    from catt import arr, check_ctx, comp2, disc_tree, infer, maximal_vars, src, sub_from, subst_tm, tgt, tree_ctx, v
    from emit_agda import Emitter
    from gray_globe_exterior_actions import coherence
    from gray_singleton_pole_actions import act
    from relative_coherence_cut import top_counts

    rank = 4
    disk = tree_ctx(disc_tree(rank))
    slot, = maximal_vars(disk)
    template = v(slot)
    ctx = disk + (disk[slot],)*11
    vertices = [v(slot+i) for i in range(12)]
    def plug(term, pole):
        return subst_tm(term, sub_from(disk, ctx, {slot: pole}))

    def junction(a, b, vertex):
        comparison = coherence(disk, a, b)
        return plug(comparison, vertex)

    paths = []
    for side, route in enumerate(((0, 1, 2, 3, 4, 5, 11), (0, 6, 7, 8, 9, 10, 11))):
        path = None
        used = []
        for j, (i, k) in enumerate(zip(route, route[1:])):
            old_left = act(disk, rank, template, 1+(j+side)%2)
            old_right = act(disk, rank, template, 1+(j+side+1)%2)
            left = plug(old_left, vertices[i])
            right = plug(old_right, vertices[k])
            boundary = arr(infer(ctx, left), left, right)
            used.append(len(ctx))
            edge = v(len(ctx))
            ctx += (boundary,)
            # One pole action acts on both ends of an edge, even when the
            # endpoints subsequently need different representatives.
            stage = 1+j%2
            moved = act(ctx, rank, edge, stage)
            a = junction(template, act(disk, rank, old_left, stage), vertices[i])
            b = junction(act(disk, rank, old_right, stage), template, vertices[k])
            fitted = comp2(ctx, rank, comp2(ctx, rank, a, moved), b)
            assert src(ctx, fitted) == vertices[i] and tgt(ctx, fitted) == vertices[k]
            path = fitted if path is None else comp2(ctx, rank, path, fitted)
        assert top_counts(ctx, path) == Counter(used)
        paths.append(path)
    wanted = arr(infer(ctx, vertices[0]), vertices[0], vertices[-1])
    assert paths[0] != paths[1] and all(infer(ctx, path) == wanted for path in paths)
    filled = ctx + (arr(wanted, *paths),)
    check_ctx(filled)
    if output:
        emitter = Emitter()
        for i, path in enumerate(paths):
            emitter.check_type(f'route{i}', ctx, path, wanted)
        emitter.check_type('native', filled, v(len(ctx)), arr(wanted, *paths))
        output.write_text(emitter.module(output.stem, 'Two separately retyped routes bounding one generator.'))
    print('Raw CaTT: twelve retyped steps, two six-step composites and a six-generator at their literal faces.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path, help='emit the raw circuit typing judgments')
    check_cycle_terms(parser.parse_args().agda)
    check_slices()
    exceptions = check_five_axis_peaks()
    for dimension in (3, 4, 5, 6):
        check(dimension, exceptions)
