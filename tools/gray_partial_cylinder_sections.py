"""Check the interval decomposition of partial cylinders and the one-ended hom substitution."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from functools import cache
from pathlib import Path

from canonical_gray_two_discs import tableau_interpreter
from catt import (STAR, arr, comp2, disc_tree, fv_tm, fv_ty, infer, ps_dim, src, subst_tm,
                  subst_ty, tgt, tree_ctx, v)
from ct_suspension import T, bd, build, cells as cylinder_cells, dim, ident, susp_tm, susp_ty
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from gray_globe_comparison import boundary, close_atoms
from gray_globe_section import cells as globe_cells, trim
from gray_path_wedge import compose
from partial_cylinder_steiner import trees


def positions(tree):
    """Generators in the declaration order of tree_ctx."""
    result = [((), 0)]
    def visit(address, children):
        for j, child in enumerate(children):
            result.extend(((address, j+1), (address+(j,), 0)))
            visit(address+(j,), child)
    visit((), tree)
    return result


def selections(old, i=0, marks=frozenset()):
    if i == len(old):
        yield marks
        return
    ty = old[i]
    if ty == STAR or (ty[2][1] not in marks and ty[3][1] not in marks):
        yield from selections(old, i+1, marks)
    yield from selections(old, i+1, marks | {i})


@cache
def presentation(tree, marks):
    old = tree_ctx(tree)
    ctx, minus, changes = cylinder(old, marks)
    plus = [v(t[1]+1) if i in marks else t for i, t in enumerate(minus)]
    atoms = []
    evaluate = tableau_interpreter(ctx, atoms.__getitem__)
    for i, ty in enumerate(ctx):
        top = ((i,), (i,))
        if ty == STAR:
            rows = (top,)
        else:
            a, b = evaluate(ty[2]), evaluate(ty[3])
            assert a[:-1] == b[:-1]
            rows = a[:-1] + ((a[-1][0], b[-1][0]), top)
        atoms.append(rows)
    height = ps_dim(old) + 1
    by_ends = defaultdict(set)
    for w in close_atoms(atoms, height):
        a, b = w[0]
        by_ends[a[0], b[0]].add(w)
    return ctx, tuple(minus), tuple(plus), changes, tuple(atoms), by_ends


def relabel(table, labels):
    return tuple(tuple(tuple(sorted(labels[g] for g in row if labels[g] is not None))
                       for row in pair) for pair in table)


def check_tree(tree, stats):
    old = tree_ctx(tree)
    names = positions(tree)
    full_marks = frozenset(range(len(old)))
    _, fm, fp, fh, _, full = presentation(tree, full_marks)
    roots = [names.index(((), k)) for k in range(len(tree)+1)]
    for marks in selections(old):
        stats['selections'] += 1
        _, minus, plus, change, _, actual = presentation(tree, marks)
        labels = {}
        for i in range(len(old)):
            labels[fm[i][1]] = minus[i][1]
            labels[fp[i][1]] = plus[i][1]
            labels[fh[i][1]] = change[i][1] if i in marks else None
        for a, left in enumerate(roots):
            for b in range(a+1, len(roots)):
                right = roots[b]
                fixed = next((i for i in roots[a+1:b] if i not in marks), None)
                starts = {minus[left][1], plus[left][1]}
                ends = {minus[right][1], plus[right][1]}
                for s in starts:
                    for t in ends:
                        target = actual[s, t]
                        if fixed is not None:
                            seam = minus[fixed][1]
                            ls, rs = actual[s, seam], actual[seam, t]
                            image = {compose(x, y, 0) for x in ls for y in rs}
                            assert image == target and len(target) == len(ls)*len(rs)
                            stats['point wedge cells'] += len(target)
                        elif b == a+1 and left not in marks and right not in marks:
                            # Desuspend and retain exactly the selection on the child.
                            inner = positions(tree[a])
                            old_indices = [names.index(((a,)+u, j)) for u, j in inner]
                            restricted = frozenset(k for k, i in enumerate(old_indices) if i in marks)
                            _, im, ip, ih, _, inner_cells = presentation(tree[a], restricted)
                            down = {}
                            for k, i in enumerate(old_indices):
                                down[minus[i][1]], down[plus[i][1]] = im[k][1], ip[k][1]
                                if i in change:
                                    down[change[i][1]] = ih[k][1]
                            images = {trim(relabel(w[1:], down)) for w in target}
                            expected = {trim(w) for group in inner_cells.values() for w in group}
                            assert images == expected and len(images) == len(target)
                            stats['suspended cells'] += len(target)
                        else:
                            start = fm[left] if s == minus[left][1] else fp[left]
                            end = fp[right] if t == plus[right][1] else fm[right]
                            lifts = full[start[1], end[1]]
                            assert {relabel(w, labels) for w in lifts} == target
                            assert len(lifts) == len(target)
                            if left not in marks or right not in marks:
                                stats['collapsed end cells'] += len(target)


def check_half(level, marked_end, emitter):
    d = level.k + 1
    tree = disc_tree(d)
    marks = frozenset({marked_end, *range(2, len(tree_ctx(tree)))})
    ctx, minus, plus, change, atoms, groups = presentation(tree, marks)
    sigma = [minus[0], plus[1]] + [None] * len(level.G)
    for (side, (_, j, sign)), var in level.end.items():
        # In D^(k+1), the suspended j-position of the smaller disc starts at 2j+2.
        i = 2*j+2 + int(sign == '+')
        term = (minus if side == 0 else plus)[i]
        if side == 0 and marked_end == 1:
            term = comp2(ctx, 0, term, change[1])
        if side == 1 and marked_end == 0:
            term = comp2(ctx, 0, change[0], term)
        sigma[var+2] = term
    for (_, j, sign), var in level.mix.items():
        sigma[var+2] = change[2*j+2 + int(sign == '+')]
    sigma = tuple(sigma)
    for i, ty in enumerate(level.G):
        assert infer(ctx, sigma[i+2]) == subst_ty(susp_ty(ty), sigma[:i+2])
    evaluate = tableau_interpreter(ctx, atoms.__getitem__)
    @cache
    def lift(c):
        return subst_tm(susp_tm(T(level, c)), sigma)
    values = set()
    intrinsic_terms = {}
    example = None
    for c in cylinder_cells(level, level.k+1):
        h = lift(c)
        a, b = (sigma[:2] if not dim(level, c) else tuple(lift(x) for x in bd(level, c)))
        assert (src(ctx, h), tgt(ctx, h)) == (a, b)
        val = evaluate(h)
        values.add(trim(val))
        if trim(val) == val:
            assert intrinsic_terms.setdefault(val, h) == h
        if val in atoms:
            assert h == v(atoms.index(val))
        elif val == trim(val) and (example is None or len(val) > example[0]):
            example = len(val), h, arr(infer(ctx, a), a, b)
    expected = {trim(w) for w in groups[sigma[0][1], sigma[1][1]]}
    assert values == expected
    if emitter:
        # The cap whisker is present on exactly one side of this declaration.
        term = change[len(tree_ctx(tree))-1]
        old_top = level.mix[('g', level.k, '*')]
        expected_type = subst_ty(susp_ty(level.G[old_top]), sigma[:old_top+2])
        emitter.check_type('transferred-change-'+str(marked_end), ctx, term, expected_type)
        _, h, ty = example
        emitter.check_type('transferred-composite-'+str(marked_end), ctx, h, ty)
    return len(values)


def check_thresholds(p, n):
    @cache
    def dependencies(g):
        return {g}.union(*(dependencies(h) for h in boundary(g)))

    count = 0
    for w in globe_cells((p, n)) - {()}:
        support = set().union(*(dependencies(g) for pair in w for row in pair for g in row))
        for j in range(n):
            d = p+j
            caps = w[d] if d < len(w) else ((), ())
            column = {g for g in support if g[0][0] == p and g[1][0] > j}
            for bit in (0, 1):
                x = ((p, 2), (j, bit))
                marks = [x in row for row in caps]
                assert (x in support) == any(marks)
                assert bool(column) == (marks[0] != marks[1])
                if column:
                    assert marks[bit ^ (p % 2)]
                count += 1
    print(f'D^{p} x D^{n}: {count} signed support and transition tests')


def check_slot_labels(level):
    """Realize a switch at each edge, including constant labellings, using actual weak poles."""
    d = level.k
    if d == 0:
        return 0
    ctx = level.G
    g = v(level.mix[('g', d, '*')])
    xs = {v(level.mix['g', d-1, sign])[1] for sign in ('-', '+')}
    poles = []
    a = b = g
    for _ in range(d+1):
        a, b = src(ctx, a), tgt(ctx, b)
        poles.append((a, b))
    poles.reverse()
    # Four parallel positions in the chosen slot. Each intervening segment
    # carries higher parallel positions, and each ancestor has siblings.
    tree = (((),), ((),), ((),))
    slot = (1,)*d
    for _ in range(d):
        tree = ((), tree, ())
    old = tree_ctx(tree)
    names = positions(tree)
    count = 0
    for split in range(5):
        sigma = []
        for i, (address, j) in enumerate(names):
            k = len(address)
            if k < d and address == slot[:k]:
                label = poles[k][int(j > slot[k])]
            elif address == slot:
                label = poles[d][int(j >= split)]
            elif k == d+1 and address[:-1] == slot and address[-1]+1 == split:
                label = g
            else:
                label = ident(ctx, sigma[old[i][2][1]])
            assert infer(ctx, label) == subst_ty(old[i], tuple(sigma))
            sigma.append(label)
        for x in xs:
            source_marked = x in (fv_tm(poles[d][0]) | fv_ty(infer(ctx, poles[d][0])))
            marked = set()
            for i, ((address, j), label) in enumerate(zip(names, sigma)):
                expected = ((j < split) == source_marked) if address == slot else False
                if old[i] != STAR:
                    expected |= old[i][2][1] in marked or old[i][3][1] in marked
                assert expected == (x in (fv_tm(label) | fv_ty(infer(ctx, label))))
                if expected:
                    marked.add(i)
            count += 1
    return count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('edges', type=int)
    parser.add_argument('--disc', type=int, default=4)
    parser.add_argument('--globe-pair', type=int, nargs=2, metavar=('P', 'N'))
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.edges < 0 or args.disc < 1:
        parser.error('use a nonnegative edge bound and a positive disc dimension')
    stats = Counter()
    for size in range(args.edges+1):
        for tree in trees(size):
            check_tree(tree, stats)
            stats['trees'] += 1
        presentation.cache_clear()
    print(dict(sorted(stats.items())))
    emitter = Emitter() if args.agda else None
    levels = build(args.disc-1)
    print(f'{sum(check_slot_labels(level) for level in levels)} typed prefix and suffix labellings')
    for level in levels:
        counts = [check_half(level, end, emitter if level == levels[-1] else None)
                  for end in (0, 1)]
        print(f'D^{level.k+1} one-ended diagonal strict cells with verified terms: {counts}')
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'The two one-ended partial cylinder substitutions.'))
    if args.globe_pair:
        if min(args.globe_pair) < 1:
            parser.error('use positive dimensions for the threshold check')
        check_thresholds(*args.globe_pair)
