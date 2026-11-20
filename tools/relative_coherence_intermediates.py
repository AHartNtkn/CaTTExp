"""Compile raw comparisons using a finite set of admissible intermediate terms."""
from argparse import ArgumentParser
from dataclasses import dataclass
from functools import cache
from itertools import product
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, fv_tm, fv_ty, infer, is_ps,
                  maximal_vars, restrict, src, sub_from, subst_tm, tdim,
                  tdim_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from partial_cylinder_steiner import trees
from relative_coherence_exchange_faces import head, string_tree


@dataclass(frozen=True)
class Chart:
    arity: tuple
    term: tuple
    labels: tuple


@cache
def face_chart(chart, side):
    term = infer(chart.arity, chart.term)[side]
    keep = fv_tm(term) | fv_ty(infer(chart.arity, term))
    small, inclusion = restrict(chart.arity, keep)
    inverse = [None] * len(chart.arity)
    for i, old in enumerate(inclusion):
        inverse[old[1]] = v(i)
    assert is_ps(small)
    face = Chart(small, subst_tm(term, inverse), tuple(chart.labels[y[1]] for y in inclusion))
    return face, inclusion


def position_order(faces):
    # A pasting tree is totally ordered by source < position < target.
    incoming = {i: set() for i in faces}
    for i, boundary in faces.items():
        if boundary is not None:
            s, t = boundary
            incoming[i].add(s)
            incoming[t].add(i)
    order = []
    while incoming:
        ready = [i for i, earlier in incoming.items() if not earlier]
        assert len(ready) == 1, 'the tree gluing must have a unique position order'
        i, = ready
        order.append(i)
        del incoming[i]
        for earlier in incoming.values():
            earlier.discard(i)
    return order


def shape(degrees):
    objects = [i for i, degree in enumerate(degrees) if degree == 0]
    assert objects and objects[0] == 0 and objects[-1] == len(degrees)-1
    return tuple(shape([d-1 for d in degrees[i+1:j]]) for i, j in zip(objects, objects[1:]))


def immediate(ty):
    return None if ty == STAR else (ty[2][1], ty[3][1])


def assemble(root, pieces):
    parent = {(i, j): (i, j) for i, c in pieces.items() for j in range(len(c.arity))}

    def find(q):
        while parent[q] != q:
            parent[q] = parent[parent[q]]
            q = parent[q]
        return q

    for i, ty in enumerate(root):
        if ty != STAR:
            for side in (2, 3):
                j = ty[side][1]
                _, inclusion = face_chart(pieces[i], side)
                for k, old in enumerate(inclusion):
                    parent[find((j, k))] = find((i, old[1]))

    faces, ranks, actual = {}, {}, {}
    for i, chart in pieces.items():
        for j, (ty, label) in enumerate(zip(chart.arity, chart.labels, strict=True)):
            q = find((i, j))
            boundary = None if ty == STAR else tuple(find((i, k)) for k in immediate(ty))
            if q in faces:
                assert faces[q] == boundary and actual[q] == label
            else:
                faces[q], actual[q], ranks[q] = boundary, label, tdim(ty) + 1
    order = position_order(faces)
    arity = tree_ctx(shape([ranks[q] for q in order]))
    target_order = position_order({i: immediate(ty) for i, ty in enumerate(arity)})
    ren = dict(zip(order, target_order, strict=True))
    for q, i in ren.items():
        expected = None if faces[q] is None else tuple(ren[x] for x in faces[q])
        assert immediate(arity[i]) == expected
    labels = [None] * len(arity)
    for q, i in ren.items():
        labels[i] = actual[q]
    args = []
    for i in range(len(root)):
        chart = pieces[i]
        inclusion = tuple(v(ren[find((i, j))]) for j in range(len(chart.arity)))
        args.append(subst_tm(chart.term, inclusion))
    return arity, tuple(labels), tuple(args)


@cache
def charts(ctx, term):
    disk = tree_ctx(disc_tree(tdim_tm(ctx, term)))
    slot = len(disk)-1
    result = {Chart(disk, v(slot), sub_from(disk, ctx, {slot: term})): None}
    if term[0] == 'v':
        return tuple(result)
    _, root, ty, args = term
    maxima = maximal_vars(root)
    for choice in product(*(charts(ctx, args[i]) for i in maxima)):
        pieces = {}
        todo = list(zip(maxima, choice))
        while todo:
            i, c = todo.pop()
            if i in pieces:
                if pieces[i] != c:
                    break
                continue
            pieces[i] = c
            if root[i] != STAR:
                for side in (2, 3):
                    small, _ = face_chart(c, side)
                    todo.append((root[i][side][1], small))
        else:
            arity, labels, generic_args = assemble(root, pieces)
            generic = ('coh', root, ty, generic_args)
            generic_type = infer(arity, generic)
            assert fv_tm(generic) | fv_ty(generic_type) == set(range(len(arity)))
            assert subst_tm(generic, labels) == term
            result[Chart(arity, generic, labels)] = None
    return tuple(result)


def openings(a, b, rank):
    if a.arity != b.arity or infer(a.arity, a.term) != infer(b.arity, b.term):
        return None
    active = []
    for i, (x, y) in enumerate(zip(a.labels, b.labels, strict=True)):
        if x != y:
            if tdim(a.arity[i]) + 1 != rank:
                return None
            active.append(i)
    return active


def fill_chart(ctx, a, b, active, proofs):
    if not active:
        return subst_tm(head(a.arity, a.term, b.term), a.labels)
    wide, minus, arrows = cylinder(a.arity, set(active))
    plus = list(minus)
    labels = [None] * len(wide)
    for i, x in enumerate(minus):
        labels[x[1]] = a.labels[i]
        if i in arrows:
            z = arrows[i]
            plus[i] = tgt(wide, z)
            labels[plus[i][1]] = b.labels[i]
            labels[z[1]] = proofs[a.labels[i], b.labels[i]]
    witness = head(wide, subst_tm(a.term, minus), subst_tm(b.term, plus))
    return subst_tm(witness, tuple(labels))


def terms_of_rank(ctx, start, rank):
    result, seen = {}, set()
    todo = list(start)
    while todo:
        t = todo.pop()
        if t in seen:
            continue
        seen.add(t)
        dim = tdim_tm(ctx, t)
        if dim < rank:
            continue
        if dim == rank:
            result[t] = None
        else:
            todo.extend(infer(ctx, t)[2:])
        if t[0] == 'coh':
            todo.extend(t[3])
    return tuple(result)


def interpolate(ctx, start, end, extra=()):
    rank = tdim_tm(ctx, start)
    assert infer(ctx, start) == infer(ctx, end) and all(tdim(ty)+1 <= rank for ty in ctx)
    assert all(tdim_tm(ctx, item) == rank for item in extra)
    terms = terms_of_rank(ctx, (start, end, *extra), rank)
    proofs = {(t, t): ident(ctx, t) for t in terms}
    pairs = [(x, y) for x in terms for y in terms if x != y and infer(ctx, x) == infer(ctx, y)]
    while (start, end) not in proofs:
        added = False
        for x, y in pairs:
            if (x, y) in proofs:
                continue
            for z in terms:
                if (x, z) in proofs and (z, y) in proofs:
                    proofs[x, y] = comp2(ctx, rank, proofs[x, z], proofs[z, y])
                    break
            else:
                for a, b in product(charts(ctx, x), charts(ctx, y)):
                    active = openings(a, b, rank)
                    if active is not None and all((a.labels[i], b.labels[i]) in proofs for i in active):
                        proofs[x, y] = fill_chart(ctx, a, b, active, proofs)
                        break
            if (x, y) in proofs:
                assert infer(ctx, proofs[x, y]) == arr(infer(ctx, x), x, y)
                added = True
        if not added:
            return None
    return proofs[start, end]


def in_chart(ctx, arity, term, values):
    return subst_tm(term, sub_from(arity, ctx, dict(zip(maximal_vars(arity), values, strict=True))))


def example(rank):
    line = tree_ctx(disc_tree(1))
    f = v(2)
    p = head(line, v(0), v(1))
    parallel = v(len(line))
    ctx = line + (infer(line, f), arr(infer(line, p), p, parallel))
    z = v(len(ctx)-1)
    # L and K have rank n-1, literally the same poles, and distinct supports
    # as expression trees: K's label for the line is the unwrapped f.
    base = p
    for _ in range(rank-3):
        base = ident(line, base)
    l, k = ident(line, base), head(line, base, base)
    q, back = head(line, l, k), head(line, k, l)
    a, b = comp2(ctx, 1, q, z), comp2(ctx, 1, back, z)
    u = ident(ctx, comp2(ctx, 1, l, z))
    v_term = comp2(ctx, rank-1, a, b)

    # First move the unit inside the whiskering, then insert the return pair.
    arity = tree_ctx(string_tree(1, [rank-1, 2]))
    x, w = map(v, maximal_vars(arity))
    first = head(arity, ident(arity, comp2(arity, 1, x, w)),
                 comp2(arity, 1, ident(arity, x), w))
    first = in_chart(ctx, arity, first, [l, z])
    pair = comp2(line, rank-1, q, back)
    middle = comp2(ctx, 1, head(line, ident(line, l), pair), z)

    # The last step distributes a fixed right whisker over a temporal product.
    column = string_tree(rank-1, [rank, rank])
    arity = tree_ctx((column[0] + disc_tree(2)[0],))
    x, y, w = map(v, maximal_vars(arity))
    assert tdim_tm(arity, x) == rank
    factor = comp2(arity, 1, comp2(arity, rank-1, x, y), w)
    separate = comp2(arity, rank-1, comp2(arity, 1, x, w), comp2(arity, 1, y, w))
    last = in_chart(ctx, arity, head(arity, factor, separate), [q, back, z])
    result = comp2(ctx, rank, comp2(ctx, rank, first, middle), last)
    assert infer(ctx, result) == arr(infer(ctx, u), u, v_term)
    extra = [comp2(ctx, 1, ident(line, l), z), comp2(ctx, 1, pair, z)]
    return ctx, u, v_term, extra, result


def check_parsing():
    point = (STAR,)
    units = [v(0)]
    for _ in range(4):
        units.append(ident(point, units[-1]))
    count = 0
    for size in range(5):
        for tree in trees(size):
            arity = tree_ctx(tree)
            op = ucomp(arity)
            labels = tuple(units[tdim(ty)+1] for ty in arity)
            t = subst_tm(op, labels)
            # Variables can map to equal terms without losing their distinct
            # positions in a full chart of the evaluated operation.
            assert Chart(arity, op, labels) in charts(point, t)
            count += 1
    # Glue two horizontal pairs of squares along their common two-edge path.
    ctx = tree_ctx((((), ()), ((), ())))
    a, b, c, d = map(v, maximal_vars(ctx))
    top, bottom = comp2(ctx, 0, a, c), comp2(ctx, 0, b, d)
    grid = comp2(ctx, 1, top, bottom)
    assert Chart(ctx, grid, tuple(map(v, range(len(ctx))))) in charts(ctx, grid)
    labels = tuple(units[tdim(ty)+1] for ty in ctx)
    assert Chart(ctx, grid, labels) in charts(point, subst_tm(grid, labels))
    # Force simultaneous changes, with two different literal generic ends.
    arity = tree_ctx(string_tree(0, [2, 2]))
    x, y = map(v, maximal_vars(arity))
    left = ucomp(arity)
    right = comp2(arity, 1, comp2(arity, 0, x, src(arity, y)),
                  comp2(arity, 0, tgt(arity, x), y))
    a, b = units[2], head(point, units[1], units[1])
    c = comp2(point, 1, a, b)
    m, n = maximal_vars(arity)
    lo = Chart(arity, left, sub_from(arity, point, {m: a, n: b}))
    hi = Chart(arity, right, sub_from(arity, point, {m: b, n: c}))
    active = openings(lo, hi, 2)
    assert active == [m, n]
    proof = fill_chart(point, lo, hi, active,
                       {(a, b): head(point, a, b), (b, c): head(point, b, c)})
    assert infer(point, proof)[2:] == (subst_tm(left, lo.labels), subst_tm(right, hi.labels))
    print(f'Recovered {count} collapsed charts, both square grids and a two-column comparison.',
          flush=True)


def check(rank, emitter):
    ctx, u, v_term, extra, result = example(rank)
    assert interpolate(ctx, u, v_term) is None
    assert not any(openings(a, b, rank) == [] for a, b in product(charts(ctx, u), charts(ctx, v_term)))
    # Supply intermediate terms only; the solver reconstructs its own columns.
    terms = terms_of_rank(ctx, (u, v_term, *extra), rank)
    assert set(terms) == set(terms_of_rank(ctx, (result,), rank))
    rebuilt = interpolate(ctx, u, v_term, extra)
    assert rebuilt is not None
    expected = arr(infer(ctx, u), u, v_term)
    assert infer(ctx, rebuilt) == expected
    if emitter:
        emitter.check_type('interpolated', ctx, rebuilt, expected)
    print(f'Rank {rank}: endpoint vocabulary insufficient; '
          f'{len(terms)} terms suffice for reconstruction.', flush=True)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rank', type=int, default=4)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.rank < 3:
        parser.error('rank must be at least three')
    emitter = Emitter() if args.agda else None
    check_parsing()
    for r in range(3, args.rank+1):
        check(r, emitter if r == args.rank else None)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Reconstructed from rank-n intermediate terms.'))
