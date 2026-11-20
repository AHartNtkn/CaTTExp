"""Check the depth-two cylinder skeleton and an actual rank-two bracket replacement."""
from argparse import ArgumentParser
from functools import reduce
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, infer, maximal_vars, ps_dim, src, sub_from,
                  subst_tm, tdim, tgt, tree_ctx, v)
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from gray_partial_cylinder_sections import selections
from partial_cylinder_steiner import trees
from relative_coherence_based_columns import Brackets
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_hidden_seam import identity


def skeletons(bound):
    counts = [0, 0, 0, 0]
    for size in range(bound+1):
        for tree in trees(size):
            old = tree_ctx(tree)
            if ps_dim(old) > 4:
                continue
            for marks in selections(old):
                if not marks or any(tdim(old[i])+1 < 2 for i in marks):
                    continue
                ctx, _, _ = cylinder(old, marks)
                counts[0] += 1
                for ty in ctx:
                    if ty == STAR:
                        continue
                    rank = tdim(ty)+1
                    if rank <= 3:
                        assert ty[2][0] == ty[3][0] == 'v'
                    if rank >= 4:
                        if rank == 4:
                            assert ty[1][2][0] == ty[1][3][0] == 'v'
                        if rank == 5:
                            # A fresh rank-four letter parallel to its attaching faces.
                            slot = ty[1]
                            assert slot[1][2][0] == slot[1][3][0] == 'v'
                            check_ctx(ctx + (slot,))
                        counts[rank-3] += 1
                if any(tdim(ty)+1 == 4 and ty[2][0] != 'v' and ty[3][0] != 'v' for ty in ctx):
                    counts[3] += 1
    print(f'{counts[0]} selected charts, {counts[1]} four-declarations, {counts[2]} formal slots, '
          f'{counts[3]} charts with a four-cell between two composites.')


def typed(output):
    p = Brackets(7)
    def tour(names):
        names = (0, *names, 0)
        return reduce(lambda a, b: comp2(p.ctx, 0, a, b),
                      (p.bracket(v(a), v(b)) for a, b in zip(names, names[1:])))
    w = tour((1, 2, 3))
    old = identity(p.ctx, w)
    fresh = p.bracket(w, w)
    a, b, c = (p.bracket(u, z) for u, z in ((old, fresh), (fresh, fresh), (fresh, old)))
    arity = tree_ctx(string_tree(2, (3, 3, 3)))
    slots = maximal_vars(arity)
    x, y, z = map(v, slots)
    l = comp2(arity, 2, comp2(arity, 2, x, y), z)
    r = comp2(arity, 2, x, comp2(arity, 2, y, z))
    sigma = sub_from(arity, p.ctx, dict(zip(slots, (a, b, c), strict=True)))
    s, t = (subst_tm(term, sigma) for term in (head(arity, l, r), head(arity, r, l)))
    pole = identity(p.ctx, old)
    enter, leave = p.bracket(pole, src(p.ctx, s)), p.bracket(tgt(p.ctx, t), pole)
    original = reduce(lambda u, z: comp2(p.ctx, 3, u, z), (enter, s, t, leave))
    rho = []
    for i, ty in enumerate(p.ctx):
        if v(i) == fresh:
            value = old
        elif ty == STAR:
            value = v(i)
        else:
            lo, hi = subst_tm(ty[2], rho), subst_tm(ty[3], rho)
            if (lo, hi) == (ty[2], ty[3]):
                value = v(i)
            else:
                value = identity(p.ctx, lo) if lo == hi else p.bracket(lo, hi)
        rho.append(value)
    restored = subst_tm(original, rho)
    down, up = p.bracket(original, restored), p.bracket(restored, original)
    external_path = tour((4, 5, 6))
    other = identity(p.ctx, identity(p.ctx, external_path))
    loop = p.bracket(other, other)
    check_ctx(p.ctx)
    emitter = Emitter()
    for power in (0, 1, 3):
        stationary = (reduce(lambda u, z: comp2(p.ctx, 3, u, z), [loop]*power)
                      if power else identity(p.ctx, other))
        outer = lambda u: comp2(p.ctx, 0, u, stationary)
        for tag, h, x, y in (('retract', down, original, restored), ('expand', up, restored, original)):
            wanted = arr(infer(p.ctx, outer(x)), outer(x), outer(y))
            term = outer(h)
            assert infer(p.ctx, term) == wanted
            if output:
                emitter.check_type(tag+str(power), p.ctx, term, wanted)
    if output:
        output.write_text(emitter.module(output.stem, 'A two-generator replacement with stationary powers.'))
    print('Both five-arrows through opposite structural four-heads at stationary powers 0, 1, 3.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('edges', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    skeletons(args.edges)
    typed(args.agda)
