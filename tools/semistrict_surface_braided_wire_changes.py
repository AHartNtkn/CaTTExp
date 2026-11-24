"""Compute the root braid group before and after a word rewrite on a floating wire."""
from argparse import ArgumentParser
from collections import deque
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_planar_tiers import artin_step, reduce_letters

RULE = {'B':('','ab'), 'D':('ab',''), 'X':('',''), 'U':('a','a'),
        'V':('a','z'), 'W':('z','a')}


def moves(h):
    for k, ((a, i), (b, j)) in enumerate(zip(h,h[1:])):
        p,q = map(len,RULE[a[0]])
        r,s = map(len,RULE[b[0]])
        if j+r <= i:
            yield k, 1, h[:k]+((b,j),(a,i+s-r))+h[k+2:]
        if i+q <= j:
            yield k, -1, h[:k]+((b,j-q+p),(a,i))+h[k+2:]


def action(n, path):
    basis = tuple((i+1,) for i in range(n))
    for i,sign in path:
        if sign == 1:
            basis = artin_step(basis,i)
        else:
            a,b = basis[i:i+2]
            conjugate = reduce_letters((*(-k for k in reversed(b)),*a,*b))
            basis = basis[:i]+(b,conjugate)+basis[i+2:]
    return basis


def shuffle(m,n):
    return tuple((i,1) for j in range(n) for i in reversed(range(j,j+m)))


def inverse(path):
    return tuple((i,-s) for i,s in reversed(path))


def segments(h):
    live = []
    words = [[],[]]
    for (g, tag),i in h:
        source, target = RULE[g]
        assert ''.join(x for x,_ in live[i:i+len(source)]) == source
        if g == 'X':
            assert live[i-1][1] == live[i][1] == tag
        if g in 'UVW':
            assert live[i][1] == tag
            words[tag].append(g)
        if g == 'D':
            assert [t for _,t in live[i:i+2]] == [tag,tag]
        live[i:i+len(source)] = [(x,tag) for x in target]
    assert not live
    return tuple(''.join(w) for w in words)


def audit(left,right,base=None):
    def lens(tag,word):
        return tuple(((g,tag),int(g=='X')) for g in 'B'+word+'XD')
    a,b = lens(0,left),lens(1,right)
    root = a+b
    n = len(root)
    full = shuffle(len(a),len(b))+shuffle(len(b),len(a))
    check = root
    for i,s in full:
        check, = [u for j,t,u in moves(check) if (i,s)==(j,t)]
    assert check == root
    queue = deque([root])
    paths = {root:()}
    turns = {root:0}
    loops = []
    while queue:
        h = queue.popleft()
        assert segments(h) == (left,right)
        for i,s,u in moves(h):
            t = turns[h]+(s if h[i][0][0] == h[i+1][0][0] == 'B' else 0)
            path = paths[h]+((i,s),)
            if u not in paths:
                paths[u],turns[u] = path,t
                queue.append(u)
            elif s == 1:
                loops.append((path+inverse(paths[u]),t-turns[u]))
    model = {}
    for path,t in loops:
        assert t % 2 == 0
        if t not in model:
            generator = full if t >= 0 else inverse(full)
            model[t] = action(n,generator*(abs(t)//2))
        assert action(n,path) == model[t]
    projection = {tuple(step for step in h if step[0][0] in 'BXD') for h in paths}
    if base is not None:
        assert projection == base
    print(f'wire words {left!r}, {right!r}: {len(paths)} marked schedules, '
          f'{len(loops)} checked return words, full twist survives')
    return projection


def wire_braids():
    # Three empty-word local rewrites on each of two wire segments.
    crossings = [(0,1),(1,1)]
    first = action(3,crossings)
    second = action(3,tuple(reversed(crossings)))
    assert first != second
    assert action(3,((0,1),(1,1),(0,1))) == action(3,((1,1),(0,1),(1,1)))
    root = tuple(((g,t),int(g=='X')) for t in range(2) for g in 'BXD')
    decorated = root
    for i,s in shuffle(3,3):
        decorated, = [u for j,t,u in moves(decorated) if (i,s)==(j,t)]
    births = [tag for (g,tag),_ in decorated if g == 'B']
    assert tuple((first,second)[t] for t in births) == (second,first)


def typed(output):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    a,z,b = v(2),v(3),v(4)
    unit = identity(ctx,v(0))
    pair = comp2(ctx,0,a,b)
    def change(s,t):
        assert infer(ctx,s) == infer(ctx,t)
        return arr(infer(ctx,s),s,t)
    ctx += (change(unit,pair),change(unit,pair),change(pair,unit),
            change(a,a),change(a,z),change(z,a))
    gate = change(v(5),v(6))
    wire = change(v(8),comp2(ctx,1,v(9),v(10)))
    ctx += (gate,wire)
    check_ctx(ctx)
    def lens(start,middle):
        return comp2(ctx,1,comp2(ctx,1,start,comp2(ctx,0,middle,b)),v(7))
    # A gate change on one lens, a wire word rewrite on the other.
    mixed = comp2(ctx,1,lens(v(11),v(8)),lens(v(5),v(12)))
    ty = infer(ctx,mixed)
    if output:
        emitter = Emitter()
        for name,tm,A in [('gateChange',v(11),gate),('wireChange',v(12),wire),
                          ('onTwoClosedLenses',mixed,ty)]:
            emitter.check_type(name,ctx,tm,A)
        (output/'BraidedWireChanges.agda').write_text(emitter.module('BraidedWireChanges',__doc__))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    base = audit('','')
    audit('U','U',base)
    audit('VW','U',base)
    audit('VW','VW',base)
    wire_braids()
    typed(args.agda_dir)
