"""Positive left-private and shared rules on two Gray columns, with arbitrary right arities."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from itertools import combinations
from graphlib import TopologicalSorter
import json
from pathlib import Path

from semistrict_surface_planar_cylinder import moves, negative_to_positive, parse
from semistrict_surface_planar_tensor import Column
from semistrict_surface_square_mutex import diagram


def read(columns,source,right,trace):
    starts=[iter(c.inputs) for c in columns]
    wires=[(int(x in right),next(starts[int(x in right)])) for x in source]
    vertices=[set(),set()]
    matching={}
    gaps={}
    crossings=defaultdict(list)
    for name,i,l,r in trace:
        if name=='swap':
            (_,f),(_,e)=wires[i:i+2]
            wires[i:i+2]=[(0,e),(1,f)]
            crossings[f].append(e)
            continue
        window=wires[i:i+len(l)]
        polygons=[]
        outputs=[]
        for side,c in enumerate(columns):
            ins=[e for s,e in window if s==side]
            if not ins:
                continue
            p,out=c.tile(name,ins,sum((a in right)==side for a in r))
            vertices[side].add(p)
            polygons.append(p)
            outputs.append(iter(out))
        if len(polygons)==2:
            matching[polygons[0]]=polygons[1]
        else:
            preceding=[e for side,e in wires[:i] if side==1]
            gaps[polygons[0]]=columns[1].endpoints[preceding[-1]][1] if preceding else 0
        wires[i:i+len(l)]=[(int(x in right),next(outputs[int(x in right)])) for x in r]
    return wires,vertices,matching,crossings,gaps


def compare(source,right,first,second,anchored=frozenset()):
    columns=[Column(sum((x in right)==s for x in source)) for s in (0,1)]
    a,b=[read(columns,source,right,trace) for trace in (first,second)]
    if a[:3]!=b[:3]:
        return None
    tiles=a[1][0]
    shared=set(a[2]) | {p for (name,_),(p,_) in columns[0].by_input.items() if name in anchored}
    if any(a[4][p]!=b[4][p] for p in shared if p in a[4]):
        return None
    cert=[]
    precedes=TopologicalSorter()
    for u,v in columns[1].endpoints.values():
        precedes.add(v,u)
    order={v:i for i,v in enumerate(precedes.static_order())}
    gaps=dict(a[4])
    wires=a[3].keys()|b[3].keys()
    regions={}
    for f in wires:
        delta=Counter(b[3].get(f,()))
        delta.subtract(a[3].get(f,()))
        region=columns[0].fill_cycle(delta,tiles)
        if any(n<0 or p in shared for p,n in region.items()):
            return None
        regions[f]=region
    for f in sorted(wires,key=lambda e:(order[columns[1].endpoints[e][0]],e)):
        start,end=columns[1].endpoints[f]
        path=list(a[3].get(f,()))
        remaining=regions[f].copy()
        while remaining:
            for p in sorted(remaining):
                before,after=columns[0].polygons[p]
                if before[0] not in path:
                    continue
                i=path.index(before[0])
                if tuple(path[i:i+len(before)])!=before:
                    continue
                assert remaining[p]==1 and gaps[p]==start
                path[i:i+len(before)]=after
                gaps[p]=end
                cert.append((p,f,1))
                del remaining[p]
                break
            else:
                raise AssertionError('a positive path filling must have an enabled polygon')
        assert path==b[3].get(f,[])
    assert gaps==b[4]
    return cert


def exhaustive(source,rules,right,budget,anchored=frozenset()):
    ids={}
    groups=defaultdict(dict)
    edges=defaultdict(set)
    simultaneous=defaultdict(set)
    queue=[(source,[],0)]
    readings=0
    while queue:
        w,path,n=queue.pop()
        u=diagram(source,path,False,ids)
        groups[w][u]=path
        readings+=1
        before=source
        windows=[]
        for k,(_,i,l,r) in enumerate(path):
            for alt in negative_to_positive(before,path,k):
                if right.intersection(alt[k][2]) or alt[k][0] in anchored:
                    continue
                other=diagram(source,alt,False,ids)
                edges[u].add(other)
                windows.append((k,k+len(alt[k][2])+1,other))
            before=before[:i]+r+before[i+len(l):]
        for (lo,hi,a),(j,end,b) in combinations(windows,2):
            if hi<=j or end<=lo:
                simultaneous[u].add(frozenset((a,b)))
        for name,i,l,r,out in moves(w,rules,right):
            count=n+(name!='swap')
            if count<=budget:
                queue.append((out,path+[(name,i,l,r)],count))
    pairs=diamonds=0
    for group in groups.values():
        for u,first in group.items():
            for a,b in combinations(edges[u],2):
                assert frozenset((a,b)) in simultaneous[u]
                assert edges[a]&edges[b]
                diamonds+=1
            reached={u}
            work=[u]
            while work:
                for v in edges[work.pop()]-reached:
                    reached.add(v)
                    work.append(v)
            for v,second in group.items():
                assert (compare(source,right,first,second,anchored) is not None)==(v in reached)
                pairs+=1
    return readings,pairs,diamonds


def agda_example(directory):
    from catt import arr, comp2, glue_tree, infer, maximal_vars, src, tgt, tree_ctx, v
    from emit_agda import Emitter
    from relative_coherence_exchange_faces import composite
    from semistrict_surface_scalar_cube import exchange
    ctx=tree_ctx(glue_tree(2,0,2))
    a,b=map(v,maximal_vars(ctx))
    def declare(ty):
        nonlocal ctx
        cell=v(len(ctx))
        ctx+=(ty,)
        return cell
    def between(u,v):
        assert infer(ctx,u)==infer(ctx,v)
        return arr(infer(ctx,u),u,v)
    def split(t):
        start,end=src(ctx,t),tgt(ctx,t)
        mid=declare(infer(ctx,start))
        return declare(between(start,mid)),declare(between(mid,end))
    x,y=split(a)
    c,d=split(b)
    declare(between(a,comp2(ctx,1,x,y)))
    def history(events):
        left,right=src(ctx,a),src(ctx,b)
        temporal=[]
        for side,t in events:
            if side==0:
                temporal.append(comp2(ctx,0,t,right))
                left=tgt(ctx,t)
            else:
                temporal.append(comp2(ctx,0,left,t))
                right=tgt(ctx,t)
        return composite(ctx,1,temporal)
    joint=declare(between(history([(0,a),(1,b)]),history([(1,c),(0,x),(1,d),(0,y)])))
    declare(between(history([(0,a)]),history([(0,x),(0,y)])))
    for l in (a,x,y):
        for r in (b,c,d):
            swap=exchange(ctx,l,r)
            declare(between(tgt(ctx,swap),src(ctx,swap)))
    emitter=Emitter()
    g=emitter.ctx(ctx)
    emitter.checks.append(f'context-ok : is-just (checkCtx {g}) ≡ true' + chr(10) + 'context-ok = refl' + chr(10))
    emitter.check_typed('shared-split',ctx,joint)
    name='SharedColumns'
    source=emitter.module(name,'Two-column shared split and all elementary returns.').replace(
        'open import CaTTExp.Pure','open import CaTTExp.Gray.Pure')
    (directory/(name+'.agda')).write_text(source)


def checks():
    cases=[('BBa',[('split','a','xy'),('shared','aB','Ba'),('join','xBy','aBB')],3),
           ('BaB',[('split','a','xx'),('join','xBx','aB'),('double','aB','BBa')],3),
           ('BaaB',[('update','a','a'),('branch','aB','MaN'),('join','MaN','aB')],3),
           ('BaM',[('left','a','xy'),('step','BaM','xNyB'),('merge','xyB','Ba')],3),
           ('BBa',[('update','a','a'),('return','aB','Ba')],3),
           ('Baa',[('s','a','xy'),('t','xy','a'),('both','aB','BNxy')],3)]
    total=[0,0,0]
    for w,r,b in cases:
        result=exhaustive(tuple(w),[(n,tuple(l),tuple(rr)) for n,l,rr in r],set('BMN'),b)
        total=[x+y for x,y in zip(total,result)]
    anchored_case=[('p',('a',),('x','y')),('fix',('x',),('x',)),('back',('y','B'),('B','y'))]
    extra=exhaustive(tuple('BBa'),anchored_case,{'B'},4,{'fix'})
    total=[x+y for x,y in zip(total,extra)]
    return dict(zip(('readings','ordered_pairs','joint_prism_checks'),total))


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    parser.add_argument('--agda-dir',type=Path)
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        source,right=tuple(q['source']),set(q['right_letters'])
        rules=[(n,tuple(l),tuple(r)) for n,(l,r) in q['rules'].items()]
        if any(n=='swap' or not(set(l)-right) or not(set(r)-right)
               or bool(right.intersection(l))!=bool(right.intersection(r)) for n,l,r in rules):
            raise ValueError('each rule must be left-positive and private or positive on the right')
        w,u=parse(source,rules,right,q['first'])
        vword,v=parse(source,rules,right,q['second'])
        if w!=vword:
            raise ValueError('expected parallel old readings')
        anchored=set(q.get('anchored',[]))
        if not anchored <= {n for n,l,r in rules if not right.intersection(l+r)}:
            raise ValueError('expected left-only named rules in anchored')
        cert=compare(source,right,u,v,anchored)
        result=dict(raw=cert is not None,surface=cert is not None,prisms=cert)
    else:
        result=checks()
    if args.agda_dir:
        agda_example(args.agda_dir)
    print(json.dumps(result))
