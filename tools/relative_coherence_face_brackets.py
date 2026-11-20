"""Find and type edge-path comparisons in the facewise bracket algebra of RP²."""
from argparse import ArgumentParser
from functools import cache
from itertools import combinations
from pathlib import Path

from catt import STAR, arr, chain_tree, comp2, fv_ty, infer, maximal_vars, sub_from, subst_tm, tree_ctx, v
from ct_suspension import ident, susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_based_columns import Brackets
from relative_coherence_exchange_faces import composite, head
from relative_coherence_cut import top_counts
from relative_coherence_signed_colours import projective_plane, support_test, typed_test


def moves(path, allowed, vertices, bound):
    for i in range(len(path)-2):
        a, b, c = path[i:i+3]
        if frozenset((a,b,c)) in allowed:
            replacement = (a,) if a == c else (a,c)
            yield path[:i]+replacement+path[i+3:], (i, 2, len(replacement)-1)
    if len(path)-1 < bound:
        for i, (a,b) in enumerate(zip(path,path[1:])):
            for c in vertices:
                if c not in (a,b) and frozenset((a,b,c)) in allowed:
                    yield path[:i+1]+(c,)+path[i+1:], (i,1,2)
    if len(path)+1 <= bound:
        for i,a in enumerate(path):
            for b in vertices:
                if b != a and frozenset((a,b)) in allowed:
                    yield path[:i+1]+(b,)+path[i:], (i,0,2)


def edge_proof(start, end, allowed, vertices, bound):
    """Bidirectional breadth-first search; retain the exact local replacement."""
    previous = [{start: None}, {end: None}]
    fronts = [[start], [end]]
    while all(fronts):
        side = int(len(fronts[1]) < len(fronts[0]))
        new_front = []
        for path in fronts[side]:
            for dest, move in moves(path, allowed, vertices, bound):
                if dest in previous[side]:
                    continue
                previous[side][dest] = path, move
                if dest in previous[1-side]:
                    halves = []
                    for j in (0,1):
                        chain = []
                        at = dest
                        while previous[j][at] is not None:
                            prior, (i,l,r) = previous[j][at]
                            chain.append((prior,at,i,l,r) if j == 0 else (at,prior,i,r,l))
                            at = prior
                        halves.append(chain)
                    return halves[0][::-1] + halves[1]
                new_front.append(dest)
        fronts[side] = new_front
    raise ValueError(f'No certificate through {bound} edges')


def word(ctx, edges, initial):
    return composite(ctx, 0, edges) if edges else ident(ctx, initial)


@cache
def word_alignment(length, start, width, enter):
    """Align one specified interval with its two fixed flanks on a generic path."""
    ctx = tree_ctx(chain_tree(length))
    vertices = [v(i) for i, ty in enumerate(ctx) if ty == STAR]
    edges = [v(i) for i in maximal_vars(ctx)] if length else []
    finish = start+width
    parts = [word(ctx, edges[a:b], vertices[a]) for a,b in ((0,start),(start,finish),(finish,length))]
    raw, framed = word(ctx, edges, vertices[0]), composite(ctx, 0, parts)
    return ctx, head(ctx, raw, framed) if enter else head(ctx, framed, raw)


def specialize(p, path, start, width, enter):
    chart, action = word_alignment(len(path)-1, start, width, enter)
    edges = [p.bracket(v(a),v(b)) for a,b in zip(path,path[1:])]
    images = dict(zip(maximal_vars(chart), edges)) if edges else {0:v(path[0])}
    return subst_tm(action, sub_from(chart, p.ctx, images))


def segment(p, path):
    edges = [p.bracket(v(a),v(b)) for a,b in zip(path,path[1:])]
    return word(p.ctx, edges, v(path[0]))


def step(p, source, target, i, l, r):
    left = segment(p, source[:i+1])
    right = segment(p, source[i+l:])
    a, b = segment(p, source[i:i+l+1]), segment(p, target[i:i+r+1])
    change = p.bracket(a,b)
    enter = specialize(p, source, i, l, True)
    leave = specialize(p, target, i, r, False)
    middle = composite(p.ctx, 0, (left,change,right))
    return composite(p.ctx, 1, (enter,middle,leave))


def aligned_power(p, around):
    # The search uses a flat six-edge word. The asserted power is a binary square.
    double = around+around[1:]
    chart = tree_ctx(chain_tree(6))
    edges = [v(i) for i in maximal_vars(chart)]
    a = composite(chart, 0, edges)
    b = comp2(chart, 0, composite(chart,0,edges[:3]), composite(chart,0,edges[3:]))
    values = [p.bracket(v(x),v(y)) for x,y in zip(double,double[1:])]
    sub = sub_from(chart, p.ctx, dict(zip(maximal_vars(chart),values,strict=True)))
    return subst_tm(head(chart,b,a),sub), subst_tm(head(chart,a,b),sub)


def run(emitter):
    facets, cycle = projective_plane()
    vertices = tuple(range(6))
    allowed = {frozenset(s) for f in facets for k in range(1,4) for s in combinations(f,k)}
    edges = [s for s in allowed if len(s) == 2]
    assert len(vertices)-len(edges)+len(facets) == 1
    for i in vertices:
        link = [set(f)-{i} for f in facets if i in f]
        assert all(sum(j in edge for edge in link) == 2 for j in vertices if j != i)
        reached = {next(j for j in vertices if j != i)}
        for _ in range(len(vertices)-1):
            reached.update(set().union(*(edge for edge in link if edge & reached)))
        assert reached == set(vertices)-{i}
    around = (0,1,4,0)
    proof = edge_proof(around+around[1:], (0,), allowed, vertices, 8)
    p = Brackets(6)
    forwards = [step(p, a,b,i,l,r) for a,b,i,l,r in proof]
    backwards = [step(p, b,a,i,r,l) for a,b,i,l,r in reversed(proof)]
    enter, leave = aligned_power(p, around)
    forward = composite(p.ctx,1,[enter,*forwards])
    reverse = composite(p.ctx,1,[*backwards,leave])
    loop = segment(p,around)
    square = comp2(p.ctx,0,loop,loop)
    unit = ident(p.ctx,v(0))

    # Check the full transitive carrier of each generator and its image in B(C2).
    cert = support_test(facets,cycle,2,2)
    assert cert['degree'] == 1
    weights, supports = [], []
    def parity(t):
        return sum(n*weights[j] for j,n in top_counts(p.ctx,t).items()) % 2
    for i, ty in enumerate(p.ctx):
        if ty == STAR:
            supports.append({i})
            weights.append(0)
            continue
        names = set().union(*(supports[j] for j in fv_ty(ty)))
        assert frozenset(names) in allowed
        supports.append(names)
        a,b = ty[2:]
        if ty[1] == STAR:
            weights.append(cert['chain'].get(tuple(sorted((a[1], b[1]))),0) % 2)
        else:
            assert parity(a) == parity(b)
            weights.append(0)
    assert parity(loop) == 1 and parity(square) == parity(unit) == 0
    judgements = [(forward,square,unit), (reverse,unit,square)]
    for power in (0,1,4):
        pad = unit if not power else composite(p.ctx,0,[loop]*power)
        for term,a,b in judgements:
            t = comp2(p.ctx,0,term,pad)
            s, e = comp2(p.ctx,0,a,pad), comp2(p.ctx,0,b,pad)
            assert infer(p.ctx,t) == arr(infer(p.ctx,s),s,e)

    ctx = p.ctx
    for depth in range(5):
        for name, (t,s,e) in zip(('collapse','expand'),judgements,strict=True):
            ty = arr(infer(ctx,s),s,e)
            assert infer(ctx,t) == ty
            if emitter and depth == 0:
                emitter.check_type(name,ctx,t,ty)
        if depth < 4:
            judgements = [tuple(susp_tm(t) for t in triple) for triple in judgements]
            ctx = susp_ctx(ctx)
    print(f'{len(proof)} local edge moves, {len(p.ctx)-6} bracket generators on the ten facets; '
          'both directions at three pads and at suspension depths 0 through 4.')


def meridian_cycle(emitter):
    facets, _ = projective_plane()
    south, north = 6, 7
    p = Brackets(8)
    chart = tree_ctx(chain_tree(3))
    x,y,z = (v(i) for i in maximal_vars(chart))
    right = comp2(chart,0,x,comp2(chart,0,y,z))
    left = comp2(chart,0,comp2(chart,0,x,y),z)
    assoc = head(chart,right,left)

    def meridian(a,b):
        sa, sb = (p.bracket(v(south),v(i)) for i in (a,b))
        an, bn = (p.bracket(v(i),v(north)) for i in (a,b))
        edge = p.bracket(v(a),v(b))
        expand = p.bracket(an,comp2(p.ctx,0,edge,bn))
        collapse = p.bracket(comp2(p.ctx,0,sa,edge),sb)
        sub = sub_from(chart,p.ctx,dict(zip(maximal_vars(chart),(sa,edge,bn),strict=True)))
        return composite(p.ctx,1,(comp2(p.ctx,0,sa,expand),subst_tm(assoc,sub),
                                  comp2(p.ctx,0,collapse,bn)))

    sides = [meridian(a,b) for a,b in ((0,1),(1,4),(4,0))]
    loop = composite(p.ctx,1,sides)
    base = segment(p,(south,0,north))
    ty = arr(infer(p.ctx,base),base,base)
    assert infer(p.ctx,loop) == ty
    unit = ident(p.ctx,base)
    facets = [(*f,tip) for f in facets for tip in (south,north)]
    carriers = []
    for i, a in enumerate(p.ctx):
        carrier = {i} if a == STAR else set().union(*(carriers[j] for j in fv_ty(a)))
        assert any(carrier <= set(f) for f in facets)
        carriers.append(carrier)
    # These two caps belong to the full eight-vertex algebra.
    for name, a,b in [('outward',loop,unit),('inward',unit,loop)]:
        cap = p.bracket(a,b)
        assert infer(p.ctx,cap) == arr(ty,a,b)
        if emitter:
            emitter.check_type(name,p.ctx,cap,arr(ty,a,b))
        assert typed_test(p.ctx,{cap[1]:1},3,facets,2)
    print('Suspended projective loop: all generating faces carried; both full caps have odd signed degree.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    run(emitter)
    meridian_cycle(emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'The double projective loop and its reverse expansion on the allowed facets.'))
