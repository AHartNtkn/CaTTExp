"""Realize the commuting colour retractions on the walking graph as CaTT substitutions."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import product
from pathlib import Path

from catt import fv_tm, fv_ty, infer, restrict, sub_from, subst_tm, subst_ty, tdim, v
from emit_agda import Emitter
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head
from relative_coherence_walking_graph import WalkingGraph, linear


@cache
def fold_template(ctx, duplicate):
    globe = ctx[:duplicate]
    images = list(map(v, range(duplicate)))
    images.append(v(duplicate-1))
    for ty in ctx[duplicate+1:]:
        _, _, s, t = subst_ty(ty, images)
        images.append(head(globe, s, t))
    return tuple(images[duplicate:])


def retraction(graph, keep):
    sigma = [v(0)]
    for start, work, anchor, carrier in graph.blocks:
        assert len(sigma) == start
        size = len(work.ctx)-work.duplicate
        if carrier <= keep:
            sigma.extend(map(v, range(start, start+size)))
        else:
            globe = work.ctx[:work.duplicate]
            at = sub_from(globe, graph.ctx, {work.old: subst_tm(anchor, sigma)})
            sigma.extend(subst_tm(t, at) for t in fold_template(work.ctx, work.duplicate))
    return tuple(sigma)


def check(height, output):
    # Every generator of the seven-name presentation is carried by such a restriction.
    local = WalkingGraph(3, height)
    subsets = [frozenset({0} | {i+1 for i in range(2) if mask & (1 << i)}) for mask in range(4)]
    maps = {s: retraction(local, s) for s in subsets}
    for s, sigma in maps.items():
        for ty, image in zip(local.ctx, sigma, strict=True):
            assert infer(local.ctx, image) == subst_ty(ty, sigma)
        chains = [top_counts(local.ctx, term) for term in sigma]
        for i, ty in enumerate(local.ctx):
            if tdim(ty)+1 < height:
                assert linear(chains, local.h[i]) == linear(local.h, chains[i])
        for t, tau in maps.items():
            assert tuple(subst_tm(term, tau) for term in sigma) == maps[s & t]
    print(f'{len(local.ctx)} local declarations, four typed selections, all 16 composite substitutions literal.')
    graph = WalkingGraph(7, 3)
    # Distinct carriers, with ordered tensor factors. A factor is a single generator.
    supports = set(graph.carriers)
    full = frozenset(range(7))
    for degree in (1, 2, 3):
        by_size = Counter(len(frozenset.union(*s)-{0}) for s in product(supports, repeat=degree))
        print(f'{degree} carrier factors: {by_size[6]} ordered patterns using six positive names.')
        assert by_size[6] == (90 if degree == 3 else 0)
        if degree == 3:
            for a, b, c in product(supports, repeat=3):
                if a|b|c == full:
                    assert a & b == a & c == b & c == {0}
    if output:
        emitter = Emitter()
        # A mixed edge's anchor uses both rays. Check its two single collapses and their composite.
        edge = local.edges[1, 2][1]
        for idx, s in enumerate(subsets[:3]):
            sigma = maps[s]
            for tag, i in (('edge', edge), ('forward', edge+1),
                           ('inverse', edge+2), ('cancel', edge+4)):
                image, ty = sigma[i], subst_ty(local.ctx[i], sigma)
                support = set(fv_tm(image) | fv_ty(ty))
                for j in reversed(range(len(local.ctx))):
                    if j in support:
                        support.update(fv_ty(local.ctx[j]))
                ctx, incl = restrict(local.ctx, support)
                back = [None]*len(local.ctx)
                for j, term in enumerate(incl):
                    back[term[1]] = v(j)
                term, wanted = subst_tm(image, back), subst_ty(ty, back)
                assert subst_tm(term, incl) == image and subst_ty(wanted, incl) == ty
                emitter.check_type(tag+str(idx), ctx, term, wanted)
        output.write_text(emitter.module(output.stem, 'Walking edge retractions at their specialized types.'))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--height', type=int, default=4)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.height < 3:
        parser.error('height must include the first cancellation of an edge attachment')
    check(args.height, args.agda)
