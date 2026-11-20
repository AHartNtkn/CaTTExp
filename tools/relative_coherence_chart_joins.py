"""Check synchronized chart readings and the missing lower states in a product of switches."""
from argparse import ArgumentParser
from functools import cache
from itertools import chain, combinations, product
from pathlib import Path

from catt import (STAR, TypeError_, arr, check_ctx, comp2, disc_tree, fv_tm, fv_ty, infer, maximal_vars, src,
                  sub_from, subst_tm, subst_ty, tdim_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_intermediates import charts, terms_of_rank
from relative_coherence_state_paths import at, common, serialize, temporal


def tuple_connector(ambient, arities, labels, left, right):
    """Decide a synchronized change for arities of height at most the state rank."""
    generators = {}
    declarations = []

    def read(terms):
        if any(t[0] == 'v' for t in terms):
            if terms not in generators:
                types = [infer(p, t) for p, t in zip(arities, terms, strict=True)]
                if types[0] == STAR:
                    ty = STAR
                else:
                    source = read(tuple(a[2] for a in types))
                    target = read(tuple(a[3] for a in types))
                    ty = arr(infer(tuple(declarations), source), source, target)
                generators[terms] = len(declarations)
                declarations.append(ty)
            return v(generators[terms])
        first = terms[0]
        assert all(t[:3] == first[:3] for t in terms)
        return (*first[:3], tuple(read(args) for args in zip(*(t[3] for t in terms), strict=True)))

    for ends in (left, right):
        assert len({subst_tm(t, s) for t, s in zip(ends, labels, strict=True)}) == 1
    assert all(infer(p, a) == infer(p, b) for p, a, b in zip(arities, left, right, strict=True))
    ranks = [tdim_tm(p, t) for p, t in zip(arities, left, strict=True)]
    assert all(max(tdim_tm(p, v(i)) for i in range(len(p))) <= r for p, r in zip(arities, ranks, strict=True))
    a, b = read(left), read(right)
    joint = tuple(declarations)
    check_ctx(joint)
    projections = list(zip(*generators.keys(), strict=True))
    assert all((subst_tm(a, sigma), subst_tm(b, sigma)) == (x, y)
               for sigma, x, y in zip(projections, left, right, strict=True))
    witness = common(joint, a, b)
    if witness is None:
        return None
    lifts = [subst_tm(witness, sigma) for sigma in projections]
    assert all(infer(p, t)[2:] == (x, y) for p, t, x, y in zip(arities, lifts, left, right, strict=True))
    result, = {subst_tm(t, sigma) for t, sigma in zip(lifts, labels, strict=True)}
    assert infer(ambient, result)[2:] == tuple(subst_tm(t, labels[0]) for t in (left[0], right[0]))
    return result, lifts


@cache
def readings(arity, labels, actual):
    results = [v(i) for i, t in enumerate(labels) if t == actual]
    if actual[0] == 'coh':
        for args in product(*(readings(arity, labels, child) for child in actual[3])):
            term = (*actual[:3], args)
            try:
                infer(arity, term)
            except TypeError_:
                continue
            results.append(term)
    return tuple(results)


def globular_trees(glob, rank):
    """Enumerate strict cells in a finite globular set with a strong order."""
    @cache
    def trees(objects, depth):
        starts = [((), (x,)) for x in objects]
        if not depth:
            return starts
        edges = {}
        for i, ty in enumerate(glob):
            if ty != STAR and ty[2][1] in objects and ty[3][1] in objects:
                edges.setdefault((ty[2][1], ty[3][1]), []).append(i)
        outgoing = {}
        for (x, y), between in edges.items():
            outgoing.setdefault(x, []).extend((y, tree, row) for tree, row in trees(tuple(between), depth-1))
        result = []
        def extend(x, tree, labels):
            result.append((tree, labels))
            for y, branch, row in outgoing.get(x, ()):
                assert y not in labels
                extend(y, tree+(branch,), labels+(y,)+row)
        for _, (x,) in starts:
            extend(x, (), (x,))
        return result
    return trees(tuple(i for i, ty in enumerate(glob) if ty == STAR), rank)


def representatives(ambient, records):
    """Enumerate the intersection classes of full root charts and a state for each."""
    arities, labels, refs = zip(*records, strict=True)
    poles = [infer(p, t) for p, t in zip(arities, refs, strict=True)]
    rank = tdim_tm(arities[0], refs[0])
    assert rank > 0 and all(tdim_tm(p, t) == rank for p, t in zip(arities, refs, strict=True))
    primitive = set()
    for i, sigma in enumerate(labels):
        for j, t in enumerate(sigma):
            choices = [(v(j),) if k == i else readings(p, s, t)
                       for k, (p, s) in enumerate(zip(arities, labels, strict=True))]
            primitive.update(product(*choices))
    rows = sorted(primitive, key=lambda row: (tdim_tm(arities[0], row[0]), row))
    ids = {row: i for i, row in enumerate(rows)}
    glob = []
    for row in rows:
        if infer(arities[0], row[0]) == STAR:
            glob.append(STAR)
        else:
            def face(side):
                return ids[tuple(side(p, t) for p, t in zip(arities, row, strict=True))]
            s, t = face(src), face(tgt)
            glob.append(arr(glob[s], v(s), v(t)))
    glob = tuple(glob)
    check_ctx(glob)
    result = []
    for tree, positions in globular_trees(glob, rank):
        arity = tree_ctx(tree)
        maps = [tuple(rows[j][i] for j in positions) for i in range(len(records))]
        choices = [readings(arity, maps[0], pole) for pole in poles[0][2:]]
        for a, b in product(*choices):
            if infer(arity, a) != infer(arity, b):
                continue
            ty = arr(infer(arity, a), a, b)
            if any(subst_ty(ty, s) != p for s, p in zip(maps, poles, strict=True)):
                continue
            try:
                mid = head(arity, a, b)
            except TypeError_:
                continue
            lifts = tuple(subst_tm(mid, s) for s in maps)
            if any(fv_tm(t) | fv_ty(ty) != set(range(len(p)))
                   for t, ty, p in zip(lifts, poles, arities, strict=True)):
                continue
            actual, = {subst_tm(t, s) for t, s in zip(lifts, labels, strict=True)}
            assert infer(ambient, actual) == subst_ty(poles[0], labels[0])
            result.append((actual, lifts))
            break
    return result


def test_joins(emitter):
    # Two different readings of the same four-edge state. Each projection
    # sees all three of its own slots, including the opaque pair on its side.
    ctx = tree_ctx(string_tree(0, [1]*4))
    p = tree_ctx(string_tree(0, [1]*3))
    a, b, c, d = map(v, maximal_vars(ctx))
    def label(args):
        return sub_from(p, ctx, dict(zip(maximal_vars(p), args, strict=True)))
    labels = [label((a, b, comp2(ctx, 0, c, d))), label((comp2(ctx, 0, a, b), c, d))]
    e, f, g = map(v, maximal_vars(p))
    x = comp2(p, 0, comp2(p, 0, e, f), g)
    y = comp2(p, 0, e, comp2(p, 0, f, g))
    joined = (x, y)
    disk = tree_ctx(disc_tree(1))
    for rank in range(1, 4):
        arity = tree_ctx(disc_tree(rank))
        slot, = maximal_vars(arity)
        wrapper = head(arity, src(arity, v(slot)), tgt(arity, v(slot)))
        wrapped = tuple(subst_tm(wrapper, sub_from(arity, p, {slot: t})) for t in joined)
        result = tuple_connector(ctx, [p, p, ctx], [*labels, tuple(map(v, range(len(ctx))))],
                                 (*joined, subst_tm(joined[0], labels[0])),
                                 (*wrapped, subst_tm(wrapped[0], labels[0])))
        assert result is not None
        raw, _ = result
        if emitter and tdim_tm(ctx, raw) == 4:
            emitter.check_type('commonConnector', ctx, raw, infer(ctx, raw))
        joined = tuple(ident(p, t) for t in joined)
    point = (STAR,)
    i = ident(point, v(0))
    sigma = (v(0), v(0), i)
    f = v(2)
    late = comp2(disk, 0, f, ident(disk, v(1)))
    early = comp2(disk, 0, ident(disk, v(0)), f)
    assert tuple_connector(point, [disk, disk], [sigma, sigma], (f, f), (late, early)) is None
    assert tuple_connector(point, [disk, disk], [sigma, sigma], (f, f), (late, late)) is not None
    representatives_at_disk = representatives(point, [(disk, sigma, f)]*2)
    assert len(representatives_at_disk) == 3
    for sample in ((f, f), (late, early), (early, late)):
        assert sum(tuple_connector(point, [disk, disk], [sigma, sigma], sample, lifts) is not None
                   for _, lifts in representatives_at_disk) == 1
    print('Three common chart readings lifted in ranks 1–3; incompatible synchronizations distinguished.')


def test_nested_slot():
    rank = 3
    disk = tree_ctx(disc_tree(rank))
    idx, = maximal_vars(disk)
    x = v(idx)
    wrap = head(disk, src(disk, x), tgt(disk, x))
    arrow = head(disk, x, wrap)
    pair = tree_ctx(string_tree(0, [rank, rank]))
    first, second = maximal_vars(pair)
    generic = ucomp(pair)
    # Give the root chart a composite second label. The left slot of the
    # alternative carrier still evaluates in the separate disk chart.
    ambient = tree_ctx(string_tree(0, [rank, rank, rank]))
    a, b, c = map(v, maximal_vars(ambient))
    root_labels = sub_from(pair, ambient, {first: a, second: comp2(ambient, 0, b, c)})
    disk_labels = sub_from(disk, ambient, {idx: a})
    inside_root = subst_tm(arrow, sub_from(disk, pair, {idx: v(first)}))
    start = subst_tm(generic, root_labels)
    via_root = subst_tm(at(pair, generic, (first,), inside_root), root_labels)
    via_disk = at(ambient, start, (first,), subst_tm(arrow, disk_labels))
    assert via_root == via_disk
    # If the root reading stops at an opaque variable instead, its label
    # fixes the residual hole. The second endpoint cannot read there.
    opaque = sub_from(disk, ambient, {idx: start})
    assert x in readings(disk, opaque, start)
    assert not readings(disk, opaque, tgt(ambient, via_disk))
    print('Nested chart action agreed literally; an opaque root fixed the residual slot.')


def test_triangle(rank, emitter):
    """Three different labelled arities share a state realising a triangle relation."""
    groups = {}
    for bits in range(8):
        groups[bits] = list(chain.from_iterable(
            [tuple(range(2*i, 2*i+2))] if bits & (1<<i) else [(2*i,), (2*i+1,)] for i in range(3)))
    arity = {m: tree_ctx(string_tree(0, [1]*len(row))) for m, row in groups.items()}

    def projection(finer, coarser):
        assert finer | coarser == coarser
        fine = arity[finer]
        letters = list(zip(groups[finer], map(v, maximal_vars(fine)), strict=True))
        labels = []
        for group in groups[coarser]:
            factors = [x for block, x in letters if block[0] in group]
            labels.append(factors[0] if len(factors) == 1 else comp2(fine, 0, *factors))
        return sub_from(arity[coarser], fine, dict(zip(maximal_vars(arity[coarser]), labels, strict=True)))

    def state(mask):
        pole = subst_tm(ucomp(arity[7]), projection(mask, 7))
        for _ in range(rank-2):
            pole = ident(arity[mask], pole)
        return head(arity[mask], pole, pole)

    def view(chart, mask):
        return subst_tm(state(mask), projection(chart, mask))

    def edge(chart, x, y):
        return head(arity[chart], view(chart, x), view(chart, y))

    ctx = arity[0]
    def spoke(i, j, reverse=False):
        mask = i|j
        charts = (i, j)
        sides = tuple(tuple(view(k, m) for k in charts) for m in (mask, 7))
        if reverse:
            sides = sides[::-1]
        shared = tuple_connector(ctx, [arity[k] for k in charts], [projection(0, k) for k in charts], *sides)
        assert shared is not None
        actual, generic = shared
        return actual, dict(zip(charts, generic, strict=True))

    indices = (1, 2, 4)
    family = [(arity[i], projection(0, i), state(i)) for i in indices]
    (actual, triple), = representatives(ctx, family)
    assert actual == view(0, 7) and triple == tuple(view(i, 7) for i in indices)
    for i, j in combinations(indices, 2):
        pair, = representatives(ctx, [(arity[k], projection(0, k), state(k)) for k in (i, j)])
        assert pair[0] == view(0, i|j)
    a, ga = spoke(1, 2)
    b, gb = spoke(2, 4)
    c, gc = spoke(1, 4, True)
    ab, bc, ac = edge(2, 3, 6), edge(4, 6, 5), edge(1, 3, 5)
    u, vv, w = [subst_tm(e, projection(0, i)) for e, i in ((ab, 2), (bc, 4), (ac, 1))]
    lower = rank
    def local(i, x, y):
        return subst_tm(head(arity[i], x, y), projection(0, i))
    t1 = local(4, bc, comp2(arity[4], lower, gb[4], gc[4]))
    t2 = local(2, comp2(arity[2], lower, ab, gb[2]), ga[2])
    t3 = local(1, comp2(arity[1], lower, ga[1], gc[1]), ac)
    line = tree_ctx(string_tree(lower, [rank+1]*3))
    x, y, z = map(v, maximal_vars(line))
    assoc = head(line, comp2(line, lower, x, comp2(line, lower, y, z)), comp2(line, lower, comp2(line, lower, x, y), z))
    assoc = subst_tm(assoc, sub_from(line, ctx, dict(zip(maximal_vars(line), (u, b, c), strict=True))))
    start = comp2(ctx, lower, u, vv)
    proof = temporal(ctx, start, [comp2(ctx, lower, u, t1), assoc, comp2(ctx, lower, t2, c), t3])
    assert infer(ctx, proof)[2:] == (start, w)
    assert view(0, 7) not in {view(0, j) for j in (3, 5, 6)}
    if emitter:
        emitter.check_type('threeCharts', ctx, proof, infer(ctx, proof))
    print(f'Rank {rank+1}: filled the three-chart boundary through its common state.')


def test_moving_writing(rank, emitter):
    """Separate the mixed naturality square from every fixed product piece."""
    r = rank-1
    path = tree_ctx(string_tree(0, [1, 1]))
    p = ucomp(path)
    c = v(len(path))
    z = v(len(path)+1)
    ctx = path + (infer(path, p), arr(infer(path, p), p, c))
    d = p
    for _ in range(r-2):
        d = ident(path, d)
    l, k = ident(path, d), head(path, d, d)
    q = head(path, l, k)
    f = comp2(ctx, 1, l, z)
    i, = (j for j in maximal_vars(f[1]) if tdim_tm(ctx, f[3][j]) == r)
    e = at(ctx, f, (i,), q)
    g = tgt(ctx, e)

    disk = tree_ctx(disc_tree(r))
    j, = maximal_vars(disk)
    enclosing = tree_ctx(disc_tree(rank))
    top = v(len(enclosing)-1)
    a, b = src(enclosing, top), tgt(enclosing, top)
    lengths = (2, 3, 4)
    operations = {}
    for length in lengths:
        line = tree_ctx(string_tree(r-1, [r]*length))
        operations[length] = composite_state(disk, line, [v(j)] + [ident(disk, tgt(disk, v(j)))]*(length-1))

    def evaluated(target, term, value):
        return subst_tm(term, sub_from(disk, target, {j: value}))

    @cache
    def weight(t):
        if t[0] == 'v':
            return 0
        return int(t == k) + sum(weight(arg) for i, arg in enumerate(t[3]) if tdim_tm(t[1], v(i)) == r)

    def integral(route, operation):
        return sum((weight(tgt(ctx, edge))-weight(src(ctx, edge))) *
                   (src(ctx, edge)[:3] == operation[:3]) for edge in route)

    assert (weight(f), weight(g)) == (0, 1)
    for length, op in operations.items():
        cap, undo = head(disk, v(j), op), head(disk, op, v(j))
        first = comp2(enclosing, r, top, evaluated(enclosing, cap, b))
        op_a = evaluated(enclosing, op, a)
        active = maximal_vars(op[1])[0]
        second = comp2(enclosing, r, evaluated(enclosing, cap, a), at(enclosing, op_a, (active,), top))
        proof = subst_tm(head(enclosing, first, second), sub_from(enclosing, ctx, {top[1]: e}))
        u, w = infer(ctx, proof)[2:]
        before, after = serialize(ctx, u), serialize(ctx, w)
        assert len(before) == len(after) == 2
        back = at(ctx, g, (i,), head(path, k, l))
        suffix = comp2(ctx, r, evaluated(ctx, undo, g), back)
        loop_proof = comp2(ctx, r, proof, suffix)
        loop_u, loop_w = infer(ctx, loop_proof)[2:]
        assert infer(ctx, loop_u)[2:] == infer(ctx, loop_w)[2:] == (f, f)
        assert [integral(serialize(ctx, loop_w), op2)-integral(serialize(ctx, loop_u), op2)
                for op2 in operations.values()] == [int(t == length) for t in lengths]
        for state in (f, g, evaluated(ctx, op, f), evaluated(ctx, op, g)):
            assert all(all(label != v(1) for ty, label in zip(c.arity, c.labels, strict=True) if ty == STAR)
                       for c in charts(ctx, state))
        if emitter and length == 3:
            emitter.check_type('movingWriting', ctx, proof, infer(ctx, proof))
            emitter.check_type('basedMovingWriting', ctx, loop_proof, infer(ctx, loop_proof))
    print(f'Rank {rank}: three independent mixed-square classes checked at one literal loop base.')


def wedge_switches(rank, width):
    line = tree_ctx(disc_tree(1))
    p = head(line, v(0), v(1))
    seed = line + (line[2], arr(line[2], p, v(3)))
    d = p
    for _ in range(rank-3):
        d = ident(line, d)
    low, high = ident(line, d), head(line, d, d)
    change = head(line, low, high)
    lo = comp2(seed, 1, low, v(4))
    slot, = (i for i in maximal_vars(lo[1]) if tdim_tm(seed, lo[3][i]) == rank-1)
    switch = at(seed, lo, (slot,), change)
    ctx = (STAR,)
    right = v(0)
    edges, protected = [], []
    for _ in range(width):
        sigma = [right]
        for ty in seed[1:]:
            sigma.append(v(len(ctx)))
            ctx += (subst_ty(ty, sigma),)
        right = sigma[1]
        edges.append(subst_tm(switch, sigma))
        protected.append((sigma[2], subst_tm(p, sigma)))
    check_ctx(ctx)
    return ctx, edges, protected


def composite_state(ctx, trunk, values):
    return subst_tm(ucomp(trunk), sub_from(trunk, ctx, dict(zip(maximal_vars(trunk), values, strict=True))))


def schedule(ctx, trunk, edges, order):
    slots = maximal_vars(trunk)
    values = [src(ctx, e) for e in edges]
    states = [composite_state(ctx, trunk, values)]
    path = []
    for i in order:
        path.append(at(ctx, states[-1], (slots[i],), edges[i]))
        values[i] = tgt(ctx, edges[i])
        states.append(composite_state(ctx, trunk, values))
    return states, path


def is_protected(t, f, p):
    return t == p or (t != f and (t[0] == 'v' or all(is_protected(a, f, p) for a in t[3])))


def test_polygon(rank, width, emitter):
    ctx, moves, barriers = wedge_switches(rank, width)
    trunk = tree_ctx(string_tree(0, [rank-1]*width))
    forward = tuple(range(width))
    backward = tuple(reversed(forward))
    s, p = schedule(ctx, trunk, moves, forward)
    t, q = schedule(ctx, trunk, moves, backward)
    u, w = temporal(ctx, s[0], p), temporal(ctx, t[0], q)
    assert serialize(ctx, u) == tuple(p) and serialize(ctx, w) == tuple(q)
    ring = s + t[-2:0:-1]
    closure = terms_of_rank(ctx, (*ring, u, w), rank-1)
    assert {z for z in closure if infer(ctx, z) == infer(ctx, ring[0])} == set(ring)
    flags = []
    for state in ring:
        flags.append(tuple(not is_protected(state, f, wrap) for f, wrap in barriers))
    assert len(set(flags)) == 2*width
    # Check all charts on each factor. The chart gluing proof then applies
    # to arbitrary width, without expanding the product of these tables.
    for e, (f, wrap) in zip(moves, barriers, strict=True):
        assert all(all(is_protected(label, f, wrap) for label in ch.labels) for ch in charts(ctx, src(ctx, e)))
        assert not is_protected(tgt(ctx, e), f, wrap)
    chords = [(i, j) for i, j in combinations(range(len(ring)), 2)
              if sum(a != b for a, b in zip(flags[i], flags[j], strict=True)) == 1]
    assert set(chords) == {(i, i+1) for i in range(len(ring)-1)} | {(0, len(ring)-1)}
    # All unit and length-one/two relations have zero winding on the ring.
    def short_paths(i):
        yield i, 0
        for shift in (-1, 0, 1):
            yield (i+shift) % len(ring), shift
            for more in (-1, 0, 1):
                yield (i+shift+more) % len(ring), shift+more
    for i in range(len(ring)):
        destinations = {}
        for end, displacement in short_paths(i):
            assert destinations.setdefault(end, displacement) == displacement
    # Each adjacent swap supplies its square, with other coordinates frozen.
    order = list(forward)
    used = set(ring)
    squares = 0
    for k, desired in enumerate(backward):
        place = order.index(desired)
        while place > k:
            old_states, old = schedule(ctx, trunk, moves, order)
            order[place-1], order[place] = order[place], order[place-1]
            new_states, new = schedule(ctx, trunk, moves, order)
            used.update(new_states)
            j = place-1
            local = tree_ctx(string_tree(0, [rank if i in order[j:j+2] else rank-1 for i in forward]))
            labels = [moves[i] if i in order[j:j+2] else
                      (tgt(ctx, moves[i]) if i in order[:j] else src(ctx, moves[i])) for i in forward]
            actual = sub_from(local, ctx, dict(zip(maximal_vars(local), labels, strict=True)))
            generic = list(map(v, maximal_vars(local)))
            def face_path(axes):
                ends = [src(local, x) if i in axes else x for i, x in enumerate(generic)]
                start = composite_state(local, trunk, ends)
                row = start
                path = []
                for axis in axes:
                    step = at(local, row, (maximal_vars(trunk)[axis],), generic[axis])
                    path.append(step)
                    row = tgt(local, step)
                return temporal(local, start, path)
            x, y = order[j:j+2]
            square = subst_tm(head(local, face_path((y, x)), face_path((x, y))), actual)
            assert infer(ctx, square)[2:] == (temporal(ctx, old_states[j], old[j:j+2]),
                                             temporal(ctx, new_states[j], new[j:j+2]))
            squares += 1
            place -= 1
    assert order == list(backward) and len(used) > len(ring)
    # The very same two inputs also have a one-head comparison on the entire product.
    grid = tree_ctx(string_tree(0, [rank]*width))
    variables = list(map(v, maximal_vars(grid)))
    def generic_path(order):
        states, word = schedule(grid, trunk, variables, order)
        return temporal(grid, states[0], word)
    h = subst_tm(head(grid, generic_path(forward), generic_path(backward)),
                 sub_from(grid, ctx, dict(zip(maximal_vars(grid), moves, strict=True))))
    assert infer(ctx, h)[2:] == (u, w)
    if emitter:
        emitter.check_type('oppositeSchedules', ctx, h, infer(ctx, h))
    print(f'Rank {rank}, {width} switches: {len(ring)} boundary states, {len(used)-len(ring)} added, {squares} squares.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rank', type=int, default=4)
    parser.add_argument('--width', type=int, default=3)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.rank < 4 or args.width < 3:
        parser.error('rank must be at least four and width at least three')
    out = Emitter() if args.agda else None
    test_joins(out)
    test_nested_slot()
    test_triangle(args.rank-1, out)
    test_moving_writing(args.rank, out)
    test_polygon(args.rank, args.width, out)
    if out:
        args.agda.write_text(out.module(args.agda.stem, 'Shared chart connectors and opposite schedules.'))
