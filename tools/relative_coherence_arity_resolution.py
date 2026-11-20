"""Check the top-count kernel resolution, interval models, and bar zero row."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import product
from pathlib import Path

from catt import (STAR, comp2, fv_tm, fv_ty, glue_tree, infer, maximal_vars, restrict,
                  src, sub_from, subst_tm, subst_ty, tdim, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident, susp_ctx, susp_tm, susp_ty
from emit_agda import Emitter
from partial_cylinder_steiner import trees
from relative_coherence_cut import top_counts
from relative_coherence_hom_chains import hom_chain, strip_head


def linear(chain, operation):
    total = Counter()
    for cell, coefficient in chain.items():
        for key, value in operation(cell).items():
            total[key] += coefficient * value
    return {key: n for key, n in total.items() if n}


def difference(positive, negative):
    total = Counter(positive)
    total.subtract(negative)
    return {key: n for key, n in total.items() if n}


def raw_boundary(ctx, term):
    ty = infer(ctx, term)
    if ty == STAR:
        return {}
    return difference({ty[3]: 1}, {ty[2]: 1})


def slots(term, hom):
    if term[0] == 'v':
        return None
    _, model, ty, labels = term
    if hom and strip_head(model, ty) is None:
        return None
    return [label for slot, label in zip(model, labels, strict=True)
            if tdim(slot) == tdim(ty)]


def relation(term, hom):
    args = slots(term, hom)
    assert args is not None
    return difference({term: 1}, Counter(args))


@cache
def expand(term, hom):
    """Coordinates in the elementary relation basis of [term] minus its count."""
    args = slots(term, hom)
    if args is None:
        return {}
    rows = Counter({term: 1})
    for value in args:
        rows.update(expand(value, hom))
    return rows


def check_relation(ctx, term, sigma, hom):
    n = tdim(infer(ctx, term)) + 1 - int(hom)
    assert n > 0
    rel = relation(term, hom)
    expanded = linear(expand(term, hom), lambda t: relation(t, hom))
    counts = (hom_chain(ctx, term) if hom else
              {v(i): k for i, k in top_counts(ctx, term).items()})
    assert expanded == difference({term: 1}, counts)
    dr = linear(rel, lambda t: raw_boundary(ctx, t))
    coords = linear(dr, lambda t: expand(t, hom))
    assert linear(coords, lambda t: relation(t, hom)) == dr
    if n >= 2:
        assert not linear(dr, lambda t: raw_boundary(ctx, t))

    def relabel(chain):
        return linear(chain, lambda t: {subst_tm(t, sigma): 1})

    image = subst_tm(term, sigma)
    assert infer(ctx, image) == subst_ty(infer(ctx, term), sigma)
    assert relation(image, hom) == relabel(rel)
    new_dr = linear(relation(image, hom), lambda t: raw_boundary(ctx, t))
    assert new_dr == relabel(dr)
    assert linear(new_dr, lambda t: expand(t, hom)) == relabel(coords)
    return image


def model_checks(bound):
    counts = Counter()
    for size in range(bound + 1):
        for tree in trees(size):
            ctx = tree_ctx(tree)
            counts['arities'] += 1
            # Degree -1 is the augmentation generator, encoded by -1.
            boundary = {-1: {}}
            homotopy = {-1: {0: 1}, 0: {}}
            boundary[0] = {-1: 1}
            for i in range(1, len(ctx), 2):
                x = ctx[i+1][2][1]
                boundary[i] = boundary[x]
                boundary[i+1] = {i: 1, x: -1}
                homotopy[i] = {**homotopy[x], i+1: 1}
                homotopy[i+1] = {}
            for i in boundary:
                assert linear(boundary[i], homotopy.__getitem__) == difference(
                    {i: 1}, linear(homotopy[i], boundary.__getitem__))
                counts['contraction entries'] += 1

            roots = [i for i, ty in enumerate(ctx) if ty == STAR]
            for first in range(len(roots)):
                for last in range(first, len(roots)):
                    start = roots[first]
                    kept = {start}
                    # Each branch after 'first' has its target root at its first index.
                    for j in range(first + 1, last + 1):
                        stop = roots[j+1] if j+1 < len(roots) else len(ctx)
                        kept.update(range(roots[j], stop))
                    segment, inclusion = restrict(ctx, kept)
                    assert segment == tree_ctx(tree[first:last])
                    target = subst_tm(ident(segment, ucomp(segment)), inclusion)
                    infer(ctx, target)
                    support = fv_tm(target) | fv_ty(infer(ctx, target))
                    assert support == kept
                    counts['root intervals'] += 1
    return counts


def labelled_relations(emitter):
    total = 0
    # Horizontal composition of two discs has a nonzero boundary in the
    # relation basis. One top input expands and the other becomes an identity.
    chart = tree_ctx(glue_tree(2, 0, 2))
    left, right = map(v, maximal_vars(chart))
    sigma = sub_from(chart, chart, {
        left[1]: comp2(chart, 1, left, ident(chart, tgt(chart, left))),
        right[1]: ident(chart, src(chart, right)),
    })
    horizontal = ucomp(chart)
    for step in range(5):
        dr = linear(relation(horizontal, False), lambda t: raw_boundary(chart, t))
        assert len(linear(dr, lambda t: expand(t, False))) == 2
        check_relation(chart, horizontal, sigma, False)
        total += 1
        if step:
            check_relation(chart, horizontal, sigma, True)
            total += 1
        horizontal = susp_tm(horizontal)
        chart = susp_ctx(chart)
        sigma = (v(0), v(1), *map(susp_tm, sigma))

    # Unit, branching and temporal heads, including repeated and composite labels.
    for k in range(1, 6):
        chart = tree_ctx(((), ()) if k == 1 else (((), ()),))
        base = ucomp(chart)
        while tdim(infer(chart, base)) + 1 < k:
            base = ident(chart, base)
        ctx = chart + (infer(chart, base),)
        letter = v(len(chart))
        # The substitution sends an actual variable to a nonvariable at its literal type.
        sigma = (*map(v, range(len(chart))), base)
        term = ident(ctx, letter)
        # The two copies of the same top label survive as coefficient two.
        repeated = comp2(ctx, k, term, term)
        for t in (term, repeated, ident(ctx, repeated)):
            check_relation(ctx, t, sigma, False)
            suspended = susp_tm(t)
            suspended_sigma = (v(0), v(1), *map(susp_tm, sigma))
            image = check_relation(susp_ctx(ctx), suspended, suspended_sigma, True)
            if emitter and t == repeated and k <= 3:
                emitter.check_type('suspended'+str(k), susp_ctx(ctx), image,
                                   susp_ty(subst_ty(infer(ctx, t), sigma)))
            total += 2
    return total


def flag_composition():
    """Check the inner bar face commutes with taking a face of the arity flag."""
    line = tree_ctx(((),))
    path = tree_ctx(((), ()))
    full_path = ucomp(path)
    subdivide = sub_from(line, path, {2: full_path})
    collapse = sub_from(path, line, {2: ident(line, v(0)), 4: v(2)})

    def wedge(left, right, left_target, right_target):
        # Include the right target in the concatenation of the two linear arities.
        shift = (v(len(left_target)-2),) + tuple(
            v(len(left_target)-1+i) for i in range(1, len(right_target)))
        return left + tuple(subst_tm(t, shift) for t in right[1:])

    first = wedge(subdivide, collapse, path, line)
    second = wedge(collapse, subdivide, line, path)
    composite = tuple(subst_tm(t, second) for t in first)
    lhs = tuple(subst_tm(t, collapse) for t in subdivide)
    rhs = tuple(subst_tm(t, subdivide) for t in collapse)
    assert composite == wedge(lhs, rhs, line, path)
    three = tree_ctx(((), (), ()))
    for sigma in (first, second, composite):
        for ty, value in zip(three, sigma, strict=True):
            assert infer(three, value) == subst_ty(ty, sigma)
    return len(composite)


def zero_row():
    # Product order with incomparable objects and two distinct lifts of its least vertex.
    images = ((0, 0), (0, 1), (1, 0), (1, 1), (0, 0))
    def le(i, j):
        return all(a <= b for a, b in zip(images[i], images[j], strict=True))
    def boundary(flag):
        result = Counter()
        for i in range(len(flag)):
            result[flag[:i]+flag[i+1:]] += (-1)**i
        return {key: n for key, n in result.items() if n}
    flags = [()]
    checked = 0
    for _ in range(6):
        for flag in flags:
            assert all(le(a,b) for a,b in zip((0,)+flag, flag))
            assert boundary((0,)+flag) == difference(
                {flag: 1}, linear(boundary(flag), lambda f: {(0,)+f: 1}))
            checked += 1
        flags = [flag+(i,) for flag, i in product(flags, range(len(images)))
                 if not flag or le(flag[-1], i)]
    return checked


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--bound', type=int, default=6)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    counts = model_checks(args.bound)
    counts['kernel and substitution checks'] = labelled_relations(emitter)
    counts['composed flag entries'] = flag_composition()
    counts['augmented preorder flags'] = zero_row()
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Suspended labelled arity relations.'))
    print(', '.join(f'{n} {key}' for key, n in counts.items()))
