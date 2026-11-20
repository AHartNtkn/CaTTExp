"""Build the raw four-simplex by substituting into the suspended three-cube."""
from argparse import ArgumentParser
from itertools import combinations
from pathlib import Path

from canonical_gray_cube import build_cube
from catt import (arr, check_ctx, coh_between, comp2, glue_tree, infer, maximal_vars,
                  src, sub_from, subst_tm, subst_ty, tgt, tree_ctx, v)
from ct_suspension import susp_ctx
from emit_agda import Emitter
from rc2 import kappa, rc2_full
from relative_coherence_based_columns import Brackets, difference
from relative_coherence_colour_degree import relative_columns
from relative_coherence_cut import top_counts
from relative_coherence_hidden_seam import identity


def seven_vertex_context():
    """One explicit three-skeleton containing every cut at an internal vertex."""
    p = Brackets(7)
    vertices = tuple(range(7))
    atoms = {(i,): v(i) for i in vertices}
    for size in range(2, 5):
        for s in combinations(vertices, size):
            if s[0] == 0 and s[-1] == 6:
                continue
            if size == 2:
                a, b = s
                source, target = v(a), v(b)
            elif size == 3:
                a, b, c = s
                source, target = atoms[a,c], comp2(p.ctx, 0, atoms[a,b], atoms[b,c])
            else:
                a, b, c, d = s
                source = comp2(p.ctx, 1, atoms[a,c,d], comp2(p.ctx, 0, atoms[a,b,c], atoms[c,d]))
                target = comp2(p.ctx, 1, atoms[a,b,d], comp2(p.ctx, 0, atoms[a,b], atoms[b,c,d]))
                assoc = kappa(p.ctx, tgt(p.ctx, source), tgt(p.ctx, target))
                source = comp2(p.ctx, 1, source, assoc)
            atoms[s] = p.bracket(source, target)
            assert difference(p.ctx, source, target) == {
                atoms[s[:j]+s[j+1:]][1]: (-1)**j for j in range(size)}
    check_ctx(p.ctx)
    assert len(atoms) == len(p.ctx) == 82
    print('Seven-vertex three-skeleton: 82 typed variables and all signed simplex boundaries.')
    return p.ctx, atoms


def middle_square(p, left, right):
    """Both generic exchange directions on two horizontally consecutive two-cells."""
    tree = glue_tree(2, 0, 2)
    arity = tree_ctx(tree)
    a, b = map(v, maximal_vars(arity))
    high_first = comp2(arity, 1, comp2(arity, 0, src(arity, a), b),
                       comp2(arity, 0, a, tgt(arity, b)))
    low_first = comp2(arity, 1, comp2(arity, 0, a, src(arity, b)),
                      comp2(arity, 0, tgt(arity, a), b))
    return (coh_between(p.ctx, tree, (left, right), high_first, low_first),
            coh_between(p.ctx, tree, (left, right), low_first, high_first))


def marked_replacement(agda=None):
    """Localize a contextual replacement to a whole strict three-state."""
    marked_tree = glue_tree(4, 0, 4)
    marked = tree_ctx(marked_tree)
    z, y = map(v, maximal_vars(marked))
    direct = comp2(marked, 0, z, y)
    first = comp2(marked, 0, src(marked, z), y)
    last = comp2(marked, 0, z, tgt(marked, y))
    serial = comp2(marked, 3, first, last)
    ctx = tree_ctx(glue_tree(4, 0, 3))
    h, x = map(v, maximal_vars(ctx))
    unit = identity(ctx, x)
    endpoints, steps, tails, to_serial, from_serial = [], [], [], [], []
    for old in (unit, comp2(ctx, 3, unit, unit)):
        args = sub_from(marked, ctx, {z[1]: h, y[1]: old})
        endpoints.append(subst_tm(direct, args))
        steps.append(subst_tm(first, args))
        tails.append(subst_tm(last, args))
        to_serial.append(coh_between(ctx, marked_tree, (h,old), direct, serial))
        from_serial.append(coh_between(ctx, marked_tree, (h,old), serial, direct))
    assert tails[0] == tails[1] and top_counts(ctx, tails[0]) == {h[1]: 1}
    assert all(not top_counts(ctx, step) for step in steps)

    state_tree = glue_tree(3, 0, 3)
    state = tree_ctx(state_tree)
    a, b = map(v, maximal_vars(state))
    local_unit = identity(state, b)
    local = [comp2(state, 0, a, t) for t in (local_unit, comp2(state, 3, local_unit, local_unit))]
    emitter = Emitter() if agda else None
    for i, j, name in ((0,1,'forward'), (1,0,'reverse')):
        change = coh_between(ctx, state_tree, (src(ctx,h), x), local[i], local[j])
        assert infer(ctx, change) == arr(infer(ctx, steps[i]), steps[i], steps[j])
        action = comp2(ctx, 3, change, tails[0])
        witness = comp2(ctx, 4, comp2(ctx, 4, to_serial[i], action), from_serial[j])
        ty = arr(infer(ctx, endpoints[i]), endpoints[i], endpoints[j])
        assert infer(ctx, witness) == ty
        if emitter:
            emitter.check_type(name, ctx, witness, ty)
    if emitter:
        agda.write_text(emitter.module(agda.stem, 'Replacing an old four-term in a marked context.'))
    print('Marked replacement: both five-arrows typed, one stationary step changes, the unary step agrees.')


def four_simplex(agda=None, whole=False):
    p = Brackets(5)
    atoms = {(i,): v(i) for i in range(5)}
    for edge in combinations(range(5), 2):
        atoms[edge] = p.bracket(*(v(i) for i in edge))
    for a, b, c in combinations(range(5), 3):
        atoms[a,b,c] = p.bracket(atoms[a,c], comp2(p.ctx, 0, atoms[a,b], atoms[b,c]))

    def path_tree(vertices):
        if len(vertices) == 2:
            return atoms[vertices]
        # Fixing vertex two splits the mixed square into literal left/right factors.
        cut = vertices.index(2) if 2 in vertices[1:-1] else 1
        return path_tree(vertices[:cut+1]), path_tree(vertices[cut:])

    def evaluate(tree):
        if tree[0] == 'v':
            return tree
        return comp2(p.ctx, 0, evaluate(tree[0]), evaluate(tree[1]))

    def step(vertices, i):
        lo = max(a for a in vertices if a < i)
        hi = min(a for a in vertices if i < a)

        def change(tree):
            if tree == atoms[lo,hi]:
                return atoms[lo,i,hi]
            if tree[0] == 'v':
                return None
            left, right = tree
            first = change(left)
            if first is not None:
                return comp2(p.ctx, 0, first, evaluate(right))
            second = change(right)
            if second is not None:
                return comp2(p.ctx, 0, evaluate(left), second)
            return None

        term = change(path_tree(vertices))
        after = evaluate(path_tree(tuple(sorted((*vertices, i)))))
        if tgt(p.ctx, term) != after:
            correction = kappa(p.ctx, tgt(p.ctx, term), after)
            term = comp2(p.ctx, 1, term, correction)
        return term

    def vertices(mask):
        return (0, *(i for i in (1,2,3) if mask & (1 << (i-1))), 4)

    def whiskered_face(fixed, source, target):
        # The inner tetrahedron relates the two orders of splitting an edge.
        segment = (1,2,3,4) if fixed == 1 else (0,1,2,3)
        a, b, c, d = segment

        def route(i, j):
            return comp2(p.ctx, 1, step((a,d), i), step((a,i,d), j))

        inner = p.bracket(route(c,b), route(b,c))
        atoms[segment] = inner
        if fixed == 1:
            term = comp2(p.ctx, 0, atoms[0,1], inner)
        else:
            term = comp2(p.ctx, 0, inner, atoms[3,4])
        # Align the literal one-boundaries first, then the two-boundaries.
        u, w = src(p.ctx, source), tgt(p.ctx, source)
        initial = src(p.ctx, src(p.ctx, term))
        final = tgt(p.ctx, tgt(p.ctx, term))
        if u != initial:
            term = comp2(p.ctx, 1, kappa(p.ctx, u, initial), term)
        if final != w:
            term = comp2(p.ctx, 1, term, kappa(p.ctx, final, w))
        if source != src(p.ctx, term):
            term = comp2(p.ctx, 2, rc2_full(p.ctx, source, src(p.ctx, term)), term)
        if tgt(p.ctx, term) != target:
            term = comp2(p.ctx, 2, term, rc2_full(p.ctx, tgt(p.ctx, term), target))
        return term

    cube, _ = build_cube()
    domain = susp_ctx(cube)
    labels = [v(0), v(4)]
    labels.extend(evaluate(path_tree(vertices(i))) for i in range(8))
    for ty in cube[8:20]:
        before, after = (t[1] for t in ty[2:])
        labels.append(step(vertices(before), (before ^ after).bit_length()))
    for i, term in enumerate(labels):
        assert infer(p.ctx, term) == subst_ty(domain[i], labels[:i])

    emitter = Emitter() if agda else None
    for ix in range(20,26):
        ty = subst_ty(domain[ix+2], labels)
        source, target = ty[2:]
        before, after = (src(cube, cube[ix][2])[1], tgt(cube, cube[ix][2])[1])
        active = tuple(i for i in (1,2,3) if (before ^ after) & (1 << (i-1)))
        fixed, = set((1,2,3)) - set(active)
        if not before:
            term = p.bracket(source, target)
            atoms[(0, *active, 4)] = term
        elif fixed == 2:
            term, back = middle_square(p, atoms[0,1,2], atoms[2,3,4])
            reverse_type = arr(ty[1], target, source)
            assert infer(p.ctx, back) == reverse_type
            if emitter:
                emitter.check_type('middle', p.ctx, term, ty)
                emitter.check_type('middleReverse', p.ctx, back, reverse_type)
        else:
            term = whiskered_face(fixed, source, target)
        assert infer(p.ctx, term) == ty
        labels.append(term)

    ty = subst_ty(domain[-1], labels)
    top = p.bracket(*ty[2:])
    assert infer(p.ctx, top) == ty
    labels.append(top)
    assert len(labels) == len(domain) == 29
    names = tuple(range(5))
    atoms[names] = top
    assert len(atoms) == len(p.ctx) == 31
    assert difference(p.ctx, *ty[2:]) == {atoms[names[:i]+names[i+1:]][1]: (-1)**i for i in names}
    check_ctx(p.ctx)
    columns, degrees = relative_columns(p.ctx, list(names), 4)
    assert columns == {top[1]: {}} and degrees == {top[1]: 1}
    if emitter:
        if whole:
            emitter.check_type('fourSimplex', p.ctx, top, ty)
        agda.write_text(emitter.module(agda.stem, 'Suspended-cube comparisons in the ordered simplex.'))
    print('Four-simplex: 31 literal atoms, all 29 substitution entries typed, five signed tetrahedra, degree +1.')
    return p.ctx, atoms


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path, help='emit the forward and reverse mixed judgments')
    parser.add_argument('--whole', action='store_true', help='also emit the entire four-simplex judgment')
    parser.add_argument('--cuts-only', action='store_true', help='check just the seven-vertex cut context')
    parser.add_argument('--marked', action='store_true', help='check the marked replacement and its reverse')
    args = parser.parse_args()
    if args.marked:
        marked_replacement(args.agda)
    else:
        seven_vertex_context()
        if not args.cuts_only:
            four_simplex(args.agda, args.whole)
