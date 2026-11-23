"""Signed pair windings at private updates; exact surface test through width two.

For --faces FILE (private_movies format) a negative winding test excludes a
surface filler at any width. A null answer leaves a larger comparison open.
"""
from argparse import ArgumentParser
from collections import Counter,defaultdict
from itertools import combinations,product
import json
from pathlib import Path

from semistrict_surface_acyclic_private_movies import Traces
from semistrict_surface_private_histories import closure,solve as validate


def signature(n,reading):
    order = list(range(n))
    count = Counter()
    marks = [[] for _ in order]
    for name,i in reading:
        if name in ('X','-X'):
            if not 0<=i<n-1:
                raise ValueError('crossing outside the temporal list')
            a,b = order[i:i+2]
            count[min(a,b),max(a,b)] += 1 if name=='X' else -1
            order[i:i+2] = b,a
        else:
            e = order[i]
            marks[e].append((name,tuple(count[min(e,x),max(e,x)] for x in range(n))))
    totals = tuple(count[pair] for pair in combinations(range(n),2))
    return tuple(order),totals,marks


def obstruction(a,b,changes):
    if a[:2]!=b[:2]:
        return 'total permutation or pair windings'
    for e,(left,right) in enumerate(zip(a[2],b[2])):
        if len(left)!=len(right):
            return 'number of updates on a named input'
        for j,((p,src),(q,dst)) in enumerate(zip(left,right)):
            if q not in closure(p,lambda name:changes.get(name,())):
                return 'private labels'
            for x,(s,t) in enumerate(zip(src,dst)):
                if s!=t and (abs(s-t)!=1 or (x<e) != bool(s%2)):
                    return ('marked winding',e,j,x,s,t)
    return None


def solve(data):
    h=tuple(map(tuple,data['history']))
    validate({**data,'source':h,'target':h})
    layers=data.get('higher',[])+[{},{}]
    if 'X' in layers[0]:
        raise ValueError('X is reserved for a native exchange')
    chart=Traces(data['marks'],*layers[:2])
    if chart.read(h,data['source'])[0]!=chart.read(h,data['target'])[0]:
        raise ValueError('nonparallel old readings')
    # Use signed tokens only inside signature; a private generator named -X
    # in the input is an ordinary update, never an inverse exchange.
    def old(steps):
        return [('X' if name=='X' else (name,),i) for name,i in steps]
    changes=defaultdict(set)
    for p,q in layers[1].values():
        changes[p,].add((q,))
    reason=obstruction(*(signature(len(h),old(data[k])) for k in ('source','target')),changes)
    return dict(surface_filler=False if reason else (True if len(h)<=2 else None),
                obstruction=reason)


def block_swap(left,right,positive):
    # The left temporal block becomes the right one. For inverse crossings
    # the reflected spelling undoes the positive shuffle in the other order.
    if not positive:
        return [('-X',i) for _,i in reversed(block_swap(right,left,True))]
    return [('X',j+k) for j in range(right) for k in reversed(range(left))]


def shift(movie,k):
    return [(op,i+k) for op,i in movie]


def checks():
    from semistrict_surface_positive_movies import moves
    tested=0
    # Generic directed prism carrying an arbitrary signed block movie with
    # marks, for either physical orientation and arbitrary stationary block.
    for n in range(1,4):
        alphabet = [('p',i) for i in range(n)] + [(s,i) for s in ('X','-X') for i in range(n-1)]
        for seq in product(alphabet,repeat=3):
            for m in (1,2,3):
                for positive in (True,False):
                    swap=block_swap(n,m,positive)
                    src=list(seq)+swap
                    dst=swap+shift(seq,m)
                    assert obstruction(signature(n+m,src),signature(n+m,dst),{}) is None
                    tested+=1
    # Check both directions of every raw comparison at width two, with
    # repeated scalar names, through a fourth crossing and two updates.
    pairs=0
    for k in range(5):
        readings=set()
        for ix in combinations(range(k+2),2):
            for i,j in product(range(2),repeat=2):
                w=[('X',0)]*(k+2)
                w[ix[0]],w[ix[1]]=('p',i),('p',j)
                readings.add(tuple(w))
        values={w:signature(2,w) for w in readings}
        for w in readings:
            reachable=closure(w,lambda v:(z for _,z in moves('ss',v,{'p':(('s',),('s',))})))
            for z in readings:
                assert (obstruction(values[w],values[z],{}) is None)==(z in reachable)
                pairs+=1
    d=dict(edges={},initial=[],start_vertex=0,scalar_at={'s':0},marks={'s':[[],[]]},
           higher=[{'p':['s','s']}],history=[(0,'s')]*2,
           source=[('p',0),('X',0),('X',0)],target=[('X',0),('X',0),('p',0)])
    assert solve(d)['obstruction']==('marked winding',0,0,1,0,2)
    assert not solve(dict(d,source=d['target'],target=d['source']))['surface_filler']
    print(f'{tested} signed block prisms and {pairs} old two-strand comparisons checked; '
          'the marked full winding is obstructed in both directions')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--faces',type=Path)
    args=p.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()))))
    else:
        checks()
