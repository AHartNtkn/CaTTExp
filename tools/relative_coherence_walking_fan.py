"""Factor full-cylinder graph labellings through rooted fans of walking cells."""
from argparse import ArgumentParser
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from catt import (STAR, arr, chain_tree, check_ctx, comp2, disc_tree, infer, maximal_vars,
                  ps_dim, sub_from, subst_tm, subst_ty, tdim, tree_ctx, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from partial_cylinder_steiner import trees
from relative_coherence_based_columns import Brackets
from relative_coherence_exchange_faces import head
from relative_coherence_walking_graph import instantiate, template


@dataclass
class Ray:
    point: tuple
    out: tuple
    back: tuple
    cancel: tuple
    expand: tuple


def point_word(ctx, point, extra):
    identity = ident(ctx, point)
    word = identity
    for _ in range(extra):
        word = comp2(ctx, 0, word, identity)
    return word


def square(ctx, x, y, forward, inverse, extra, reverse):
    # First rewrite the minus path entirely over the one-ray disk.
    chart = tree_ctx(disc_tree(1))
    edge = v(2)
    left = comp2(chart, 0, point_word(chart, v(0), extra), edge)
    right = comp2(chart, 0, ident(chart, v(0)), edge)
    ray_sub = sub_from(chart, ctx, {2: y.out})
    unit = subst_tm(head(chart, right, left) if reverse else head(chart, left, right), ray_sub)

    # Reassociate over the three independent slots before assigning the returning ray.
    chart = tree_ctx(chain_tree(3))
    a, b, c = (v(i) for i in maximal_vars(chart))
    left = comp2(chart, 0, comp2(chart, 0, a, b), c)
    right = comp2(chart, 0, a, comp2(chart, 0, b, c))
    path_sub = sub_from(chart, ctx, dict(zip(maximal_vars(chart), (x.out, x.back, y.out))))
    assoc = subst_tm(head(chart, right, left) if reverse else head(chart, left, right), path_sub)
    if reverse:
        steps = [comp2(ctx, 0, x.out, inverse), assoc, comp2(ctx, 0, x.cancel, y.out), unit]
    else:
        steps = [unit, comp2(ctx, 0, x.expand, y.out), assoc, comp2(ctx, 0, x.out, forward)]
    result = steps[0]
    for step in steps[1:]:
        result = comp2(ctx, 1, result, step)
    return result


def labelled_edge(p, a, b, slot):
    # Let the image use positive names absent from its endpoints, and revisit one.
    via = v(1 + slot % 5)
    first = p.bracket(a, via)
    loop = p.bracket(via, via)
    last = p.bracket(via, b)
    for _ in range(slot % 4):
        first = comp2(p.ctx, 0, first, loop)
    return comp2(p.ctx, 0, first, last)


def check(tree, emitter=None):
    spatial = tree_ctx(tree)
    ctx = (STAR,)
    parameter = Brackets(7)
    mapped = [v(0)]
    rays, edges = {}, {}
    counts = Counter()

    def attach(rank, anchor, prescribed):
        nonlocal ctx
        work = template(rank, 2)
        types, sigma = instantiate(ctx, work, anchor)
        ctx += types
        for j, ty in enumerate(types, work.duplicate):
            actual = subst_ty(ty, mapped)
            if j in prescribed:
                value = prescribed[j]
            else:
                value = parameter.bracket(*actual[2:])
            assert infer(parameter.ctx, value) == actual
            mapped.append(value)
        counts['tower entries'] += len(types)
        return work, sigma

    objects = [i for i, ty in enumerate(spatial) if ty == STAR]
    position = {slot: j for j, slot in enumerate(objects)}
    for i in objects:
        image = v((i + 2) % 7)  # distinct abstract positions may map to the same object
        rail = labelled_edge(parameter, v(0), image, i)
        work = template(0, 2)
        _, sigma = attach(0, v(0), {work.duplicate: image, work.forward: rail})
        back, cancel = work.inverse_pairs[0]
        # The second layer starts with this cancellation and its two inverse declarations.
        expand = next(j for j in range(cancel + 1, len(work.ctx))
                      if work.ctx[j][2:] == tuple(reversed(work.ctx[cancel][2:])))
        rays[i] = Ray(sigma[work.duplicate], sigma[work.forward], sigma[back], sigma[cancel], sigma[expand])

    domain, minus, mixed = cylinder(spatial, set(range(len(spatial))))
    plus = [v(x[1]+1) for x in minus]
    labels = [None]*len(domain)
    for i, ray in rays.items():
        labels[minus[i][1]], labels[plus[i][1]], labels[mixed[i][1]] = v(0), ray.point, ray.out

    for i, ty in enumerate(spatial):
        if tdim(ty) != 0:
            continue
        a, b = (t[1] for t in ty[2:])
        assert position[b] == position[a]+1
        x, y = rays[a], rays[b]
        anchor = comp2(ctx, 0, x.back, y.out)
        image = labelled_edge(parameter, mapped[x.point[1]], mapped[y.point[1]], i)
        work = template(1, 2)
        _, sigma = attach(1, anchor, {work.duplicate: image})
        edge, forward, inverse = (sigma[j] for j in (work.duplicate, work.forward, work.forward+1))
        edges[i] = (forward, inverse)
        extra = i % 3
        labels[minus[i][1]] = point_word(ctx, v(0), extra)
        labels[plus[i][1]] = edge
        assert subst_tm(edge, mapped) == image
        caps = subst_ty(domain[mixed[i][1]], labels)
        for reverse in (False, True):
            cell = square(ctx, x, y, forward, inverse, extra, reverse)
            expected = arr(caps[1], caps[3], caps[2]) if reverse else caps
            assert infer(ctx, cell) == expected
            if not reverse:
                labels[mixed[i][1]] = cell
            if emitter:
                emitter.check_type(('back' if reverse else 'out')+str(i), ctx, cell, expected)
            counts['rail squares'] += 1

    for i, ty in enumerate(spatial):
        if tdim(ty) == 1:
            a, b = (x[1] for x in ty[2:])
            for first, second in [(a, b), (b, a)]:
                cell = comp2(ctx, 1, edges[first][1], edges[second][0])
                expected = arr(infer(ctx, labels[plus[first][1]]),
                               labels[plus[first][1]], labels[plus[second][1]])
                assert infer(ctx, cell) == expected
                if first == a:
                    labels[plus[i][1]] = cell
                counts['spatial comparisons'] += 1
    for ty, term in zip(domain, labels, strict=True):
        if tdim(ty) <= 0 or term is not None:
            actual = subst_ty(ty, labels)
            assert infer(ctx, term) == actual
            assert infer(parameter.ctx, subst_tm(term, mapped)) == subst_ty(actual, mapped)
            if tdim(ty) <= 0:
                counts['graph entries'] += 1
    check_ctx(ctx)
    return counts


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--bound', type=int, default=6)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    totals = Counter()
    for size in range(args.bound+1):
        for tree in trees(size):
            if ps_dim(tree_ctx(tree)) <= 2:
                totals.update(check(tree))
                totals['shapes'] += 1
    print(', '.join(f'{n} {key}' for key, n in sorted(totals.items())))
    if args.agda:
        emitter = Emitter()
        check((disc_tree(1),), emitter)
        args.agda.write_text(emitter.module(args.agda.stem, 'Both rail-square directions on parallel rim edges.'))
