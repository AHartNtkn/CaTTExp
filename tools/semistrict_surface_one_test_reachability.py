"""One-tested-place reachability via Bonnet's separator on zero checkpoints."""
from collections import deque
from itertools import count, product

import islpy as isl

from semistrict_surface_positive_labels import decode_list, reachable


def ordinary(start,end,edges):
    names={s for a,b,_,_ in edges for s in (a,b)}|{start[0],end[0]}
    ids={v:i for i,v in enumerate(sorted(names,key=repr))}
    def row(state,mark):
        return tuple(int(j==ids[state]) for j in range(len(ids)))+tuple(mark)
    return dict(source=row(*start),target=row(*end),
                transitions=[(row(a,t),row(b,v)) for a,b,t,v in edges])


def guard_segments(n,g,states,edges,sources,targets):
    """Test a zero-to-zero segment containing at most one tested transition."""
    # Freeze the first copy of the tested place at the switch. The final exact
    # marking requires it to be empty, independently of operations on copy two.
    z=(0,)*(n+1)
    net=[]
    def phase(row,after):
        return tuple((0 if after and i==g else v) for i,v in enumerate(row))+(row[g] if after else 0,)
    for a,b,t,v,test in edges:
        if test:
            if not t[g]:
                net.append(((0,a),(1,b),phase(t,False),phase(v,True)))
        else:
            for p in (0,1):
                net.append(((p,a),(p,b),phase(t,p),phase(v,p)))
    for s in states:
        net.append(((0,s),(1,s),z,z))
    for direction,components in enumerate((sources,targets)):
        for j,(s,base,periods) in enumerate(components):
            choice=('choose',direction,j)
            def insert(v):
                return (*v[:g],0,*v[g:],0)
            if direction==0:
                net.extend([('start',choice,z,insert(base)),(choice,(0,s),z,z)])
                net.extend((choice,choice,z,insert(p)) for p in periods)
            else:
                net.extend([((1,s),choice,insert(base),z),(choice,'end',z,z)])
                net.extend((choice,choice,insert(p),z) for p in periods)
    return reachable(ordinary(('start',z),('end',z),net))


def decode_partition(code,d,states,s,t):
    entries=[[],[]]
    names=[f'x{i}' for i in range(d)]
    domain=isl.Set('{ ['+','.join(names)+']'+
                   (' : '+' and '.join(x+'>=0' for x in names) if d else '')+' }')
    empty=domain.subtract(domain)
    sets=[{},{}]
    for i in decode_list(code):
        v=decode_list(i)
        if not v or v[0]//2>=len(states):
            return None
        side=v[0]%2
        state=states[v[0]//2]
        values=v[1:]
        if (d and (len(values)<d or len(values)%d)) or (not d and values):
            return None
        base=tuple(values[:d])
        periods=[tuple(values[k:k+d]) for k in range(d,len(values),d)] if d else []
        entries[side].append((state,base,periods))
        if d:
            ks=[f'n{i}' for i in range(len(periods))]
            equations=[]
            for j,x in enumerate(names):
                expr=[str(base[j])]+[f'{p[j]}*{k}' for k,p in zip(ks,periods) if p[j]]
                equations.append(x+'='+'+'.join(expr))
            formula=' and '.join(equations+[k+'>=0' for k in ks])
            if ks:
                formula='exists '+','.join(ks)+': '+formula
            region=isl.Set('{ ['+','.join(names)+'] : '+formula+' }')
        else:
            region=domain
        sets[side][state]=sets[side].get(state,empty).union(region)
    point=isl.Set('{ ['+','.join('0' for _ in names)+'] }')
    if any(not point.is_subset(sets[i].get(q,empty)) for i,q in enumerate((s,t))):
        return None
    for q in states:
        a,b=(ss.get(q,empty) for ss in sets)
        if not a.is_disjoint(b) or not domain.is_subset(a.union(b)):
            return None
    return entries


def decide(net):
    from semistrict_surface_two_checkpoints import search
    fast=search(net,1000)
    if fast is not None:
        return fast
    if net['tested'] is None:
        return reachable(ordinary(net['source'],net['target'],
                                  [(a,b,t,v) for a,b,t,v,_ in net['edges']]))
    n=len(net['places'])
    g=net['places'].index(net['tested'])
    z=(0,)*n
    s,t='initial checkpoint','final checkpoint'
    edges=[(a,b,tuple(u),tuple(v),test) for a,b,u,v,test in net['edges']]
    edges.extend([(s,net['source'][0],z,tuple(net['source'][1]),False),
                  (net['target'][0],t,tuple(net['target'][1]),z,False)])
    states=sorted({q for a,b,_,_,_ in edges for q in (a,b)},key=repr)
    # One BFS expansion per separator code. Guarded branches can share this
    # tested place; a single common test instruction implements them in VAS_0.
    outgoing={q:[] for q in states}
    for a,b,u,v,test in edges:
        outgoing[a].append((b,u,v,test))
    todo=deque([(s,z)])
    seen={(s,z)}
    for code in count(1):
        if not todo:
            return False
        a,m=todo.popleft()
        if a==t and m==z:
            return True
        for b,u,v,test in outgoing[a]:
            if (not test or m[g]==0) and all(w>=i for w,i in zip(m,u)):
                nxt=b,tuple(w-i+j for w,i,j in zip(m,u,v))
                if nxt not in seen:
                    seen.add(nxt)
                    todo.append(nxt)
        certificate=decode_partition(code,n-1,states,s,t)
        if certificate and not guard_segments(n,g,states,edges,*certificate):
            return False


def checks():
    def encode(xs):
        v=0
        for k in reversed(xs):
            v=(2*v+1)<<k
        return v
    states=(0,1)
    code=encode([encode([0]),encode([3])])
    cert=decode_partition(code,0,states,0,1)
    assert cert==[[(0,(),[])],[(1,(),[])]]
    assert not decode_partition(code,0,states,1,0)
    # At the zero-test checkpoint, original tokens cannot become spendable in
    # the post-test phase. Either surplus would otherwise yield a false run.
    src=[(0,(0,),[(1,)])]
    dst=[(2,(0,),[])]
    for left,right in product((0,1),repeat=2):
        edges=[(0,1,(0,0),(left,0),False),(1,2,(0,0),(right,0),True),
               (2,2,(0,1),(0,0),False)]
        assert guard_segments(2,0,(0,1,2),edges,src,dst)==(not left and not right)
    assert guard_segments(2,0,(0,1),[(0,1,(0,3),(0,0),False)],src,[(1,(0,),[])])
    return dict(checkpoint_partition=True,guarded_segment_cases=5)


if __name__=='__main__':
    print(checks())
