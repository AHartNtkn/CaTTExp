"""Decide based comparisons in higher groupoidal presentations by integer matrices."""
from argparse import ArgumentParser
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, tdim, v
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_cut import top_counts
from relative_coherence_hurewicz_three import biarrow, difference
from relative_coherence_integral_degree import integral_test


def presentation(rank, relations, vector, emitter=None):
    ctx, pole = (STAR,), v(0)
    for _ in range(rank-1):
        pole = ident(ctx,pole)
    unit = ident(ctx,pole)
    letters = []
    for _ in vector:
        ctx, forward, inverse = biarrow(ctx,pole,pole,rank+1)
        letters.append((forward,inverse))

    def word(exponents):
        result = unit
        for (pos,neg), count in zip(letters,exponents,strict=True):
            for _ in range(abs(count)):
                result = comp2(ctx,rank-1,result,pos if count > 0 else neg)
        return result

    directions = 0
    for index, relation in enumerate(relations):
        source = word(relation)
        ctx, collapse, expand = biarrow(ctx,source,unit,rank+1)
        for tail in (0,3):
            pad = word([tail*(-1)**i for i in range(len(vector))])
            for name, t, a, b in [('collapse',collapse,source,unit),('expand',expand,unit,source)]:
                framed = comp2(ctx,rank-1,t,pad)
                s, e = comp2(ctx,rank-1,a,pad), comp2(ctx,rank-1,b,pad)
                ty = arr(infer(ctx,s),s,e)
                assert infer(ctx,framed) == ty
                assert difference(ctx,s,e) == difference(ctx,a,b)
                directions += 1
                if emitter and index == 0 and tail == 3:
                    emitter.check_type(name,ctx,framed,ty)
    check_ctx(ctx)
    rows = [i for i,a in enumerate(ctx) if tdim(a)+1 == rank]
    cols = {i:difference(ctx,*a[2:]) for i,a in enumerate(ctx) if tdim(a) == rank}
    assert len(rows) == 3*len(vector)
    # Solve using all raw columns, including both return generators, and check
    # the same membership independently after eliminating the inverse rows.
    actual = top_counts(ctx,word(vector))
    raw = integral_test({i:{j:c[i] for j,c in cols.items() if c[i]} for i in rows},
                        {i:actual[i] for i in rows})
    reduced = integral_test({i:{j:r[i] for j,r in enumerate(relations) if r[i]} for i in range(len(vector))},
                            dict(enumerate(vector)))
    assert ('potential' in raw) == ('potential' in reduced)
    return raw, len(cols), directions


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rank', type=int)
    parser.add_argument('--relations', type=json.loads, default=[[4,2],[-2,2]])
    parser.add_argument('--vector', type=json.loads, default=[0,6])
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.rank is not None and args.rank < 2:
        parser.error('rank must be at least two')
    if not isinstance(args.vector,list) or not args.vector or not all(type(v) is int for v in args.vector):
        parser.error('vector must be a nonempty integer list')
    if not isinstance(args.relations,list) or not all(isinstance(r,list) and len(r) == len(args.vector)
            and all(type(v) is int for v in r) for r in args.relations):
        parser.error('relations must be integer vectors of the specified width')
    emitter = Emitter() if args.agda else None
    ranks = [args.rank] if args.rank else [2,3,4,5]
    for rank in ranks:
        result, cols, directions = presentation(rank,args.relations,args.vector,
                                               emitter if rank == ranks[-1] else None)
        print(f'Rank {rank}: {cols} raw boundary columns, {directions} typed directions; {result}.')
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Power relation at signed pads in both directions.'))
