"""Compile a two-generator group presentation into homogeneous three-color Gray 4-rules."""
from argparse import ArgumentParser
from collections import deque
from functools import cache
from itertools import product
import json
from pathlib import Path

from catt import arr, comp2, infer, maximal_vars, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, string_tree
from semistrict_surface_shared_edge import braid_image, inverse
from semistrict_surface_three_axis import fitted_exchange, scalar_context, specialize

A, B = (1,1), (2,2)
Z = (1,2,1,1,2,1)
GENERATORS = dict(zip('abAB',(A,B,inverse(A),inverse(B)),strict=True))


def spelling(word):
    return tuple(i for g in word for i in GENERATORS[g])


def power(word, exponent):
    return word*exponent if exponent >= 0 else inverse(word)*(-exponent)


def weight(word):
    # Half the exponent sum on a pure braid.
    return sum(1 if i>0 else -1 for i in word)//2


def positive_equation(word, guard_twists=1):
    """Clear negatives by full twists, optionally padding both sides at the source."""
    assert sum(1 if i>0 else -1 for i in word) == 0
    pieces = {1:(1,), 2:(2,), -1:(2,1,1,2,1), -2:(1,2,1,2,1)}
    left = Z*guard_twists + tuple(j for i in word for j in pieces[i])
    right = Z*(guard_twists+sum(i<0 for i in word))
    assert len(left) == len(right)
    return left,right


def homogeneous_kernel(generators, rels, central, degree):
    """Generate the kernel of (the quotient by rels and central, integer degree)."""
    g, D = degree(central), central
    for r in rels:
        # Keep Bezout coefficients in the Euclidean algorithm. D represents
        # a trivial quotient element of the current positive gcd degree.
        e = degree(r)
        if e % g:
            hi,lo = g,abs(e)
            u,v,s,t = 1,0,0,1
            while lo:
                q,rem = divmod(hi,lo)
                hi,lo = lo,rem
                u,v,s,t = s,t,u-q*s,v-q*t
            g,D = hi,power(D,u)+power(r,v if e>=0 else -v)
    assert degree(D) == g
    kernel = [D+x+inverse(D)+inverse(x) for x in generators]
    kernel.extend(r + power(D,-(degree(r)//g)) for r in (*rels,central))
    return g, D, [positive_equation(k) for k in kernel]


def compile_group(relators):
    return homogeneous_kernel((A,B),tuple(map(spelling,relators)),Z,weight)


def query(word, g, D):
    w = spelling(word)
    e = weight(w)
    if e % g:
        return None
    return positive_equation(w + power(D,-(e//g)))


def matrix(word):
    """Three-strand representation in PSL(2,Z), killing exactly the center of B3."""
    a,b,c,d = 1,0,0,1
    for i in word:
        sign = 1 if i>0 else -1
        if abs(i)==1:
            b,d = b+sign*a,d+sign*c
        else:
            a,c = a-sign*b,c-sign*d
    return min((a,b,c,d),(-a,-b,-c,-d))


def permute(order, letter):
    i = abs(letter)-1
    return order[:i] + (order[i+1],order[i]) + order[i+2:]


def schreier_table():
    origin = (0,1,2)
    paths = {origin:()}
    todo = deque([origin])
    while todo:
        p = todo.popleft()
        for i in (1,2):
            q = permute(p,i)
            if q not in paths:
                paths[q] = paths[p]+(i,)
                todo.append(q)
    table = {}
    for p,line in paths.items():
        for i in (1,2,-1,-2):
            q = permute(p,i)
            target = matrix(line+(i,)+inverse(paths[q]))
            table[p,i] = next(w for n in range(5) for w in product('abAB',repeat=n)
                              if matrix(spelling(w)) == target)
    return table


def finite_image(word, generators):
    state = tuple(range(len(next(iter(generators.values())))))
    for c in word:
        state = tuple(generators[c][i] for i in state)
    return state


def read_loop(word, table, generators):
    origin = order = (0,1,2)
    w = []
    for i in word:
        w.extend(table[order,i])
        order = permute(order,i)
    assert order == origin
    return finite_image(w,generators)


def check():
    table = schreier_table()
    count = 0
    groups = [(['aaa','abAB','aB'],(1,2,0),(1,2,0),3),
              (['aa','bbb','abab'],(1,0,2),(1,2,0),1),
              (['a','b'],(0,1,2),(0,1,2),1)]
    for rels,a,b,expected in groups:
        generators = dict(a=a,b=b,A=tuple(a.index(i) for i in range(3)),
                          B=tuple(b.index(i) for i in range(3)))
        g,D,rules = compile_group(rels)
        assert g == expected
        for l,r in rules:
            assert read_loop(l,table,generators) == read_loop(r,table,generators)
            assert len(l) == len(r) >= 6
        for n in range(5):
            for w in product('abAB',repeat=n):
                pair = query(w,g,D)
                if pair is not None:
                    l,r = pair
                    actual = read_loop(l,table,generators) == read_loop(r,table,generators)
                else:
                    actual = False
                assert actual == (finite_image(w,generators) == (0,1,2))
                count += 1
    for i in (1,2):
        l,r = positive_equation((i,-i))
        assert braid_image(3,l) == braid_image(3,r)
    return count


def raw_example():
    ctx = scalar_context(3)
    arity = tree_ctx(string_tree(1,[2]*3))
    slots = tuple(map(v,maximal_vars(arity)))
    outside = composite(arity,1,slots)
    pads = {i:fitted_exchange(ctx,v(i),v(i))[0] for i in (1,2,3)}

    @cache
    def letter(order, pos):
        i = pos-1
        _,cross = fitted_exchange(ctx,v(order[i]),v(order[i+1]))
        terms = tuple(pads[c] for c in order)
        pair = comp2(arity,1,slots[i],slots[i+1])
        grouped = composite(arity,1,slots[:i]+(pair,)+slots[i+2:])
        move = composite(ctx,1,terms[:i]+(cross,)+terms[i+2:])
        if grouped == outside:
            return move
        enter = specialize(head(arity,outside,grouped),arity,ctx,terms)
        terms = tuple(pads[c] for c in permute(order,pos))
        leave = specialize(head(arity,grouped,outside),arity,ctx,terms)
        return composite(ctx,2,[enter,move,leave])

    def path(word):
        order = (1,2,3)
        moves = []
        for i in word:
            moves.append(letter(order,i))
            order = permute(order,i)
        assert order == (1,2,3)
        return composite(ctx,2,moves)

    left,right = path(A),path(B)
    # A guarded form of A = B, the cyclic quotient's single identifying relation.
    larger = arr(infer(ctx,left),path(Z+A),path(Z+B))
    ctx += (larger,)
    emitter = Emitter()
    emitter.check_type('guarded-equation',ctx,v(4),larger)
    g = emitter.ctx(ctx)
    old = arr(infer(ctx,left),left,right)
    emitter.checks.append(f'fixed-boundary : {g} ⊢ty {emitter.ty(old)}\n'
                          f'fixed-boundary = from-just (checkTy {g} (from-just (checkCtx {g}))'
                          f' {emitter.ty(old)})\n')
    return emitter


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--relators',nargs='*', help='words in abAB; capitals are inverses')
    parser.add_argument('--word',default='',help='word to test in that presentation')
    parser.add_argument('--agda',type=Path)
    args = parser.parse_args()
    if args.relators is not None:
        if any(set(w)-set(GENERATORS) for w in [*args.relators,args.word]):
            parser.error('only abAB are group letters')
        g,D,rules = compile_group(args.relators)
        print(json.dumps(dict(order='ABC',symmetric_rules=rules,query=query(args.word,g,D),
                              residue_modulus=g)))
        return
    print(f'{check():,} compiled judgments checked in cyclic, symmetric and trivial quotients.')
    if args.agda:
        emitter = raw_example()
        module = emitter.module(args.agda.stem,'Three named strands and the fixed two-crossing test.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n','open import CaTTExp.Gray.Pure\n'))


if __name__ == '__main__':
    main()
