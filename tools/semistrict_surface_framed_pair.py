"""Presburger raw and signed decisions for two strands with invertible abelian unary labels.

JSON has rank and rules. Each rule is [width,left,right], with each face
[crossing_count, list_of_framings] and a framing vector of length rank per
input strand. --presentation also accepts 'query': [left,right] at width two.
"""
import argparse
import json
from itertools import product
from pathlib import Path

import islpy as isl


def linear(weights, names):
    return ' + '.join(f'{k}*{x}' for k,x in zip(weights,names) if k) or '0'


def swapped(v,rank):
    return v[rank:]+v[:rank]


def face(entry,n,rank):
    k,rows = entry
    if k < 0 or n < 2 and k or len(rows) != n or any(len(row)!=rank for row in rows):
        raise ValueError('invalid positive framed face')
    return k,tuple(x for row in rows for x in row)


def moves(rank,rules):
    triples = set()
    for width,l,r in rules:
        a,p = face(l,width,rank)
        b,q = face(r,width,rank)
        if width == 0 or width > 2:
            continue
        changed = tuple(t-s for s,t in zip(p,q)) + (0,)*((2-width)*rank)
        for parity in (0,1):
            w = swapped(changed,rank) if parity else changed
            # At width one this is a direct placement at either strand.
            guard = a+(parity if width==2 else 0)
            triples.add((guard,guard+b-a,w))
    return sorted(triples,key=lambda e: (0,e[0]) if e[1]>=e[0] else (1,-e[1]))


def relation(rank,transitions,signed):
    # Coordinates are input crossing count, output crossing count, and frame difference.
    dz = [f'z{i}' for i in range(2*rank)]
    ns = [f'n{i}' for i in range(len(transitions))]
    hidden = list(ns)
    clauses = ['k >= 0','h >= 0']+[f'{x} >= 0' for x in ns]
    delta = [b-a for a,b,_ in transitions]
    clauses.append('h = k + '+linear(delta,ns))
    if not signed:
        for i,(a,b,_) in enumerate(transitions):
            if delta[i] >= 0:
                amount = 'k + '+linear(delta[:i],ns[:i])
                need = a
            else:
                amount = 'k + '+linear(delta[:i+1],ns[:i+1])
                need = b
            clauses.append(f'({ns[i]} = 0 or {amount} >= {need})')
    odd = [n for n,d in zip(ns,delta) if d%2]
    transfers = [f't{i}' for i in range(rank)] if odd else []
    if transfers:
        hidden.extend(transfers)
        clauses.append('('+'+'.join(odd)+' > 0 or ('+' and '.join(t+' = 0' for t in transfers)+'))')
    for j,z in enumerate(dz):
        expression = linear([w[j] for _,_,w in transitions],ns)
        if transfers:
            expression += (' + ' if j < rank else ' - ')+transfers[j%rank]
        clauses.append(f'{z} = '+expression)
    body = ' and '.join(clauses)
    if hidden:
        body='exists ('+', '.join(hidden)+': '+body+')'
    return isl.Set('{ ['+', '.join(['k','h',*dz])+'] : '+body+' }').coalesce()


def point(values):
    return isl.Set('{ ['+', '.join(str(x) for x in values)+'] }')


def decide(data):
    rank=data['rank']
    if rank < 0:
        raise ValueError('rank must be nonnegative')
    es=moves(rank,data['rules'])
    raw,signed=(relation(rank,es,s) for s in (False,True))
    result={}
    if 'query' in data:
        (k,p),(h,q)=(face(v,2,rank) for v in data['query'])
        asked=point([k,h,*[b-a for a,b in zip(p,q)]])
        result.update(raw=not raw.is_disjoint(asked),surface=not signed.is_disjoint(asked))
    missing=signed.subtract(raw)
    if missing.is_empty():
        result['failure']=None
    else:
        sample=missing.sample_point()
        result['failure']=[sample.get_coordinate_val(isl.dim_type.set,i).to_python()
                           for i in range(2+2*rank)]
    return result


def checks():
    # In each native prism orientation use the inverse label's native
    # prism and positive whiskering to go backwards across a crossing.
    for start, finish, sequence in [
            ('Rx','xL',[(2,'','lL'),(1,'xl','rx'),(0,'Rr','')]),
            ('xR','Lx',[(0,'','Ll'),(1,'lx','xr'),(2,'rR','')])]:
        w=start
        for i,l,r in sequence:
            assert w[i:i+len(l)] == l
            w=w[:i]+r+w[i+len(l):]
        assert w == finish
    # A neutral crossing-guarded addition can change either frame in the signed
    # group. In the raw system it needs at least one original crossing.
    rule=[2,[1,[[0],[0]]],[1,[[1],[0]]]]
    data=dict(rank=1,rules=[rule],query=[[0,[[0],[0]]],[0,[[1],[0]]]])
    out=decide(data)
    assert out['surface'] and not out['raw'] and out['failure'] is not None
    data['rules'].append([1,[0,[[0]]],[0,[[1]]]])
    assert decide(data)['failure'] is None
    # One unguarded crossing insertion transports arbitrary opposite frames.
    insertion=[2,[0,[[0],[0]]],[1,[[0],[0]]]]
    data=dict(rank=1,rules=[insertion],query=[[0,[[0],[0]]],[1,[[37],[-37]]]])
    assert decide(data)==dict(raw=True,surface=True,failure=None)
    # Independent oracle on bounded counts: all selected moves preserve or
    # increase both total frame and crossing count. Odd moves identify frames
    # of the same total, tracked by a flag instead of imposing a frame cutoff.
    total=0
    for rules in ([rule],[insertion],[rule,insertion],
                  [[2,[2,[[0],[0]]],[4,[[1],[2]]]],rule]):
        es=moves(1,rules)
        for signed in (False,True):
            rel=relation(1,es,signed)
            for k,h in product(range(4),repeat=2):
                seen={(k,0,0,False)}
                todo=list(seen)
                while todo:
                    c,l,r,free=todo.pop()
                    for a,b,(v,w) in es:
                        nxt=(c+b-a,l+v,r+w,free or (b-a)%2==1)
                        if (signed or c>=a) and nxt[0]<=h and nxt[1]+nxt[2]<=4 and nxt not in seen:
                            seen.add(nxt)
                            todo.append(nxt)
                for u,v in product(range(-1,4),repeat=2):
                    if u+v>4:
                        continue
                    actual=any(c==h and ((l,r)==(u,v) or free and l+r==u+v)
                               for c,l,r,free in seen)
                    assert actual == (not rel.is_disjoint(point((k,h,u,v))))
                    total+=1
    # Check the scalar scheduling theorem on all small mixed multisets against
    # every possible firing order directly, including drops followed by gains.
    from itertools import permutations
    schedules=0
    for edges in product(list(product(range(3),repeat=2)),repeat=3):
        ordered=sorted(edges,key=lambda e:(0,e[0]) if e[1]>=e[0] else (1,-e[1]))
        def fires(order,k):
            for a,b in order:
                if k<a:
                    return False
                k+=b-a
            return True
        for k in range(4):
            assert fires(ordered,k) == any(fires(p,k) for p in permutations(edges))
            schedules+=1
    print(f'{total} framed judgments, {schedules} mixed schedules and all-boundary decisions checked')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--presentation',type=Path)
    args=ap.parse_args()
    if args.presentation:
        print(json.dumps(decide(json.loads(args.presentation.read_text()))))
    else:
        checks()
