"""Fixed parallel-cell extensions of globes and their strict retractions."""
from argparse import ArgumentParser
from pathlib import Path

from catt import (arr, check_ctx, comp2, disc_tree, fv_tm, fv_ty, infer, restrict,
                  sub_from, subst_tm, subst_ty, tdim_tm, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_based_columns import Brackets
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity


def globe_filler(globe, a, b):
    ty = infer(globe, a)
    assert ty == infer(globe, b)
    support = fv_tm(a) | fv_ty(ty)
    assert support == fv_tm(b) | fv_ty(ty)
    small, inclusion = restrict(globe, support)
    renaming = [None] * len(globe)
    for i, variable in enumerate(inclusion):
        renaming[variable[1]] = v(i)
    result = subst_tm(head(small, subst_tm(a, renaming), subst_tm(b, renaming)), inclusion)
    assert infer(globe, result) == arr(ty, a, b)
    return result


class ParallelCell:
    def __init__(self, k):
        self.globe = tree_ctx(disc_tree(k))
        self.ctx = self.globe + (self.globe[-1],)
        self.old = v(len(self.globe) - 1)
        self.new = v(len(self.globe))
        self.generators = {}
        self.collapse = [v(i) for i in range(len(self.globe))] + [self.old]
        self.k = k

    def bracket(self, source, target, image=None):
        assert tdim_tm(self.ctx, source) >= self.k
        ty = arr(infer(self.ctx, source), source, target)
        assert infer(self.ctx, source) == infer(self.ctx, target)
        a, b = (subst_tm(t, self.collapse) for t in (source, target))
        if image is None:
            image = globe_filler(self.globe, a, b)
        assert infer(self.globe, image) == subst_ty(ty, self.collapse)
        key = source, target, image
        if key not in self.generators:
            self.generators[key] = v(len(self.ctx))
            self.ctx += (ty,)
            self.collapse.append(image)
        return self.generators[key]


def check(k, emitter):
    e = ParallelCell(k)
    move = e.bracket(e.new, e.old)
    back = e.bracket(e.old, e.new)
    old_move = e.collapse[move[1]]
    # The target of move is stationary; only the source needs its moving face.
    padded = comp2(e.ctx, k, move, old_move)
    transport = e.bracket(move, padded)
    reverse = e.bracket(padded, move)
    cancel = e.bracket(comp2(e.ctx, k, move, back), identity(e.ctx, e.new))
    twice = comp2(e.globe, k, old_move, old_move)
    second = e.bracket(e.new, e.old, twice)
    assert second != move and e.collapse[second[1]] == twice
    change, undo = e.bracket(move, second), e.bracket(second, move)
    check_ctx(e.ctx)
    for label, t, s, u in (('go', move, e.new, e.old), ('back', back, e.old, e.new),
                          ('mixed', transport, move, padded), ('opposite', reverse, padded, move),
                          ('varyImage', change, move, second), ('restoreImage', undo, second, move)):
        ty = arr(infer(e.ctx, s), s, u)
        assert infer(e.ctx, t) == ty
        assert infer(e.globe, subst_tm(t, e.collapse)) == subst_ty(ty, e.collapse)
        if emitter:
            emitter.check_type(label + str(k), e.ctx, t, ty)
            emitter.check_type('image' + label + str(k), e.globe, subst_tm(t, e.collapse),
                               subst_ty(ty, e.collapse))
    assert infer(e.ctx, cancel)[3] == identity(e.ctx, e.new)
    if k != 2:
        return

    # The old generator of the universal two-disc can label a genuine composite.
    p = Brackets(3)
    x, y = p.bracket(v(0), v(1)), p.bracket(v(1), v(2))
    path = comp2(p.ctx, 0, x, y)
    direct = p.bracket(v(0), v(2))
    h, l = p.bracket(path, direct), p.bracket(direct, path)
    z = comp2(p.ctx, 1, h, l)
    other = p.bracket(path, path)
    labels = list(sub_from(e.globe, p.ctx, {e.old[1]: z})) + [other]
    for ty in e.ctx[len(labels):]:
        s, t = (subst_tm(x, labels) for x in ty[2:])
        labels.append(p.bracket(s, t))
    for label, source in (('specialized', transport), ('specializedBack', reverse)):
        t = subst_tm(source, labels)
        ty = subst_ty(infer(e.ctx, source), labels)
        assert infer(p.ctx, t) == ty
        if emitter:
            emitter.check_type(label, p.ctx, t, ty)
    assert labels[e.old[1]][0] == 'coh' and labels[e.new[1]][0] == 'v'
    check_ctx(p.ctx)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    for k in range(5):
        check(k, emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Parallel-cell templates and their globe projections.'))
    print('Ranks 0 through 4: both directions and mixed cells checked before and after collapse; '
          'the two-globe also specializes to a composite on a three-vertex path.')
