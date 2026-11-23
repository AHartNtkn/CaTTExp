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


def positive_equation(word):
    """Clear negatives by a common full twist; one extra twist guards the raw relation."""
    assert weight(word) == 0
    pieces = {1:(1,), 2:(2,), -1:(2,1,1,2,1), -2:(1,2,1,2,1)}
    left = Z + tuple(j for i in word for j in pieces[i])
    right = Z*(1+sum(i<0 for i in word))
    assert len(left) == len(right)
    return left,right


def compile_group(relators):
    rels = tuple(map(spelling,relators))
    g, D = 3, Z
    for r in rels:
        e = weight(r)
        if e % 3:
            sign = 1 if e % 3 == 1 else -1
            g, D = 1, power(r,sign)+power(Z,(1-sign*e)//3)
            break
    assert weight(D) == g
    kernel = [D+x+inverse(D)+inverse(x) for x in (A,B)]
    kernel.extend(r + power(D,-(weight(r)//g)) for r in (*rels,Z))
    return g, D, [positive_equation(k) for k in kernel]


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
    state = tuple(range(len(generators['a'])))
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
