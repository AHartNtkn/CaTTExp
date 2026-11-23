"""Compile finite quotients of PSL(2,Z) at a single-crossing scalar Gray boundary."""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from catt import arr, infer
from emit_agda import Emitter
from semistrict_surface_group_encoding import Z, finite_image, homogeneous_kernel, positive_equation, power
from semistrict_surface_shared_edge import inverse
from semistrict_surface_three_axis import raw_letters

P,Q = (1,2,1),(1,2)
LIFTS = dict(zip('pqPQ',(P,Q,inverse(P),inverse(Q)),strict=True))


def spelling(w):
    return tuple(i for c in w for i in LIFTS[c])


def degree(w):
    return sum(1 if i>0 else -1 for i in w)


def compile_group(relators):
    return homogeneous_kernel((P,Q),tuple(map(spelling,relators)),Z,degree)


def query(w,g,D):
    h = spelling(w)
    e = degree(h)
    if e % g:
        return None
    return positive_equation(h+power(D,-(e//g)))


def abelianization_order(relators):
    # In C6, p maps to 3 and q to 2.
    from math import gcd
    return gcd(6,*(degree(spelling(w)) for w in relators))


def finite_check(rels, p, q):
    g,D,rules = compile_group(rels)
    gens = dict(p=p,q=q,P=tuple(p.index(i) for i in range(len(p))),
                Q=tuple(q.index(i) for i in range(len(q))))
    one = tuple(range(len(p)))
    assert all(finite_image(w,gens)==one for w in ['pp','qqq',*rels])
    # sigma_1 = Q^-1 P, sigma_2 = P Q^-1 modulo the central full twist.
    x,y = finite_image('Qp',gens),finite_image('pQ',gens)
    positions = dict(a=x,b=y)
    assert g == abelianization_order(rels)
    def evaluate(w):
        return finite_image(('ab'[i-1] for i in w),positions)
    for l,r in rules:
        assert len(l)==len(r)>=6 and evaluate(l)==evaluate(r)
    count = 0
    for n in range(5):
        for w in product('pqPQ',repeat=n):
            pair = query(w,g,D)
            answer = pair is not None and evaluate(pair[0])==evaluate(pair[1])
            assert answer == (finite_image(w,gens)==one)
            count += 1
    return count, x==y


def check():
    identity = (0,1,2,3,4,5)
    cyclic = lambda k: tuple((i+k)%6 for i in identity)
    cases = [
        ([],cyclic(3),cyclic(2),True),   # test a C6 representation
        (['p'],identity,cyclic(2),True),
        (['q'],cyclic(3),identity,True),
        (['p','q'],identity,identity,True),
        (['pqpq'],(1,0,2),(1,2,0),False),  # S3
        (['pqpqpqpqpq'],(1,0,3,2,4),(0,2,4,3,1),False),  # (2,3,5)
    ]
    count = 0
    for rels,p,q,cyclic_case in cases:
        n,agrees = finite_check(rels,p,q)
        assert agrees == cyclic_case
        count += n
    print(f'{count:,} compiled judgments compared with finite permutation evaluations.')
    print('Both answers at the single-crossing boundary; tested all four residue moduli of 6.')


def raw_boundary():
    emitter = Emitter()
    ctx,x,y = raw_letters(emitter)
    old = arr(infer(ctx,x),x,y)
    g = emitter.ctx(ctx)
    emitter.checks.append(f'fixed-test : {g} ⊢ty {emitter.ty(old)}\n'
                          f'fixed-test = from-just (checkTy {g} (from-just (checkCtx {g}))'
                          f' {emitter.ty(old)})\n')
    return emitter


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--relators',nargs='*',help='extra relators in pqPQ, with p^2=q^3=1 implicit')
    parser.add_argument('--word',default='',help='modular word to compile at the same three-scalar input')
    parser.add_argument('--agda',type=Path)
    args = parser.parse_args()
    if args.relators is not None:
        if any(set(w)-set(LIFTS) for w in [*args.relators,args.word]):
            parser.error('only pqPQ are modular letters')
        g,D,rules = compile_group(args.relators)
        print(json.dumps(dict(width=3,symmetric_rules=rules,fixed_boundary=[[1],[2]],
                              query=query(args.word,g,D),abelianization_order=g)))
        return
    check()
    if args.agda:
        emitter = raw_boundary()
        module = emitter.module(args.agda.stem,'Fixed single-crossing undecidability boundary.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n','open import CaTTExp.Gray.Pure\n'))


if __name__ == '__main__':
    main()
