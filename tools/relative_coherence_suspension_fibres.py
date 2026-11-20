"""Reconstruct suspended terms over a generator map from their cut and projection."""
from argparse import ArgumentParser
from functools import cache
from pathlib import Path

from catt import STAR, arr, comp2, infer, src, sub_from, subst_tm, subst_ty, v
from ct_suspension import ident, susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_arity_covers import GROUP, cover, presentation as group_presentation
from relative_coherence_based_columns import Brackets
from relative_coherence_cut import Cut, arity_cut, outer_edge
from relative_coherence_face_transfer import lift


class Lift:
    def __init__(self, small, large, images):
        self.small, self.large = susp_ctx(small), susp_ctx(large)
        assert all(t[0] == 'v' and infer(small,t) == subst_ty(a,images)
                   for t, a in zip(images,large,strict=True))
        self.images = tuple(images)
        self.raised = (v(0),v(1))+tuple(susp_tm(t) for t in self.images)
        self.down = Cut(self.small,(1,))
        self.up = Cut(self.large,(1,))

    @cache
    def term(self, raw, lifted_cut):
        if raw[0] == 'v':
            assert lifted_cut[0] == 'v'
            result = susp_tm(lifted_cut)
        else:
            _, chart, sphere, labels = raw
            end_side = frozenset(i for i,a in enumerate(chart) if a == STAR and labels[i] == v(1))
            branch = arity_cut(chart,end_side)
            if sphere[1] == STAR:
                assert len(branch.indices) == 1
                active = (lifted_cut,)
            else:
                assert lifted_cut[:3] == ('coh',branch.context(),branch.type(sphere))
                active = lifted_cut[3]
            lifted = [self.term(t,active[branch.indices[i]]) if i in branch.indices else t
                      for i,t in enumerate(labels)]
            result = ('coh',chart,sphere,tuple(lifted))
        assert outer_edge(infer(self.large,result)) == (0,1)
        assert subst_tm(result,self.raised) == raw and self.up.term(result) == lifted_cut
        return result


def tower(ctx, pole, rank):
    result = pole
    for _ in range(rank):
        result = ident(ctx,result)
    return result


def pad(ctx, t, power):
    # Inactive pole expressions can themselves have nontrivial paths and high heads.
    for end in (0,1):
        word = ident(ctx,v(end))
        for _ in range(power):
            word = comp2(ctx,0,word,ident(ctx,v(end)))
        inactive = tower(ctx,word,2)
        t = comp2(ctx,0,inactive,t) if end == 0 else comp2(ctx,0,t,inactive)
    return t


def tests(emitter):
    base = group_presentation()
    sheets, _, _, _ = cover(base)
    projection = ((v(0),)*6+(v(1),)*6+(v(2),)*6+
                  tuple(v(i) for _ in GROUP for i in range(3,6)))
    cover_lift = Lift(base,sheets,projection)
    cols = []
    for i in range(18,len(sheets)):
        for power in (0,1,4):
            # Vary the writing upstairs before the recovery; lower sheet coordinates
            # in the right factor of a path need not match those in the left one.
            t = pad(cover_lift.large,susp_tm(v(i)),power)
            for raw_up in (t, ident(cover_lift.large,t)):
                raw = subst_tm(raw_up,cover_lift.raised)
                lower = cover_lift.up.term(raw_up)
                assert subst_tm(lower,projection) == cover_lift.down.term(raw)
                assert cover_lift.term(raw,lower) == raw_up
                cols.append(raw_up)
    # This map identifies parallel generators and has no unique lifting from an
    # initial object. The lower cut distinguishes all branches of the fibre.
    many = base+(base[3],)
    folded = Lift(base,many,tuple(v(i) for i in range(len(base)))+(v(3),))
    lifts = []
    for i in (3,len(base)):
        t = pad(folded.large,susp_tm(v(i)),2)
        raw, lower = subst_tm(t,folded.raised), folded.up.term(t)
        assert folded.term(raw,lower) == t
        lifts.append((raw,lower))
    assert lifts[0][0] == lifts[1][0] and lifts[0][1] != lifts[1][1]

    universal = Brackets(1)
    colours = lift(sheets,[0]*len(GROUP),universal)
    classifier = Lift(universal.ctx,sheets,colours)
    for t in cols:
        decorated = subst_tm(t,classifier.raised)
        lower = classifier.up.term(t)
        assert subst_tm(lower,colours) == classifier.down.term(decorated)
        assert classifier.term(decorated,lower) == t

    # Parallel encodings of the first (one-dimensional hom) output. Bracketing
    # and removing a unit generically on its disk gives actual opposite directions.
    from catt import disc_tree, tree_ctx
    from relative_coherence_exchange_faces import head
    disk = tree_ctx(disc_tree(2))
    atom = v(len(disk)-1)
    padded = comp2(disk,0,ident(disk,v(0)),atom)
    # The raw boundaries must stay literal: compare two writings of that pad
    # whose variable and inactive terms are identical at both immediate faces.
    twice = ident(disk,src(disk,padded))
    other = comp2(disk,1,twice,padded)
    for j,(a,b) in enumerate(((other,padded),(padded,other))):
        generic = head(disk,a,b)
        sample = susp_tm(v(6))
        sigma = sub_from(disk,cover_lift.large,{atom[1]:sample})
        original = subst_tm(generic,sigma)
        raw = subst_tm(original,cover_lift.raised)
        lower = cover_lift.up.term(original)
        answer = cover_lift.term(raw,lower)
        s,e = subst_tm(a,sigma),subst_tm(b,sigma)
        wanted = arr(infer(cover_lift.large,s),s,e)
        assert infer(cover_lift.large,answer) == wanted
        if emitter:
            emitter.check_type(('recover','recoverBack')[j],cover_lift.large,answer,wanted)
            emitter.check_type(('cut','cutBack')[j],sheets,lower,cover_lift.up.type(wanted))
    print(f'{len(cols)} suspended terms recovered over the cover and again over the universal '
          'one-vertex bracket algebra; two distinct lifts of a folded term; both directed disk changes and their cuts.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda',type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    tests(emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem,'Sheet reconstruction of two opposite raw disk changes.'))
