"""Compare positive-left Gray diagrams with shared births and deaths on the right."""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_planar_cylinder import moves, negative_to_positive, parse
from semistrict_surface_planar_tensor import Column
from semistrict_surface_square_mutex import diagram


def reading(column,source,right,trace,anchored):
    indices=[0,0]
    wires=[]
    for x in source:
        side=int(x in right)
        i=indices[side]
        wires.append((side,(-1,i) if side else i))
        indices[side]+=1
    tiles=set()
    ports={}
    crossings=defaultdict(list)
    for name,i,l,r in trace:
        window=wires[i:i+len(l)]
        if name=='swap':
            (_,f),(_,e)=window
            crossings[e].append(f)
            wires[i:i+2]=[(0,e),(1,f)]
            continue
        left=[e for s,e in window if not s]
        rin=tuple(f for s,f in window if s)
        p,outputs=column.tile(name,left,sum(x not in right for x in r))
        tiles.add(p)
        rout=tuple((p,k) for k in range(sum(x in right for x in r)))
        if rin or rout or name in anchored:
            ports[p]=(rin,rout)
        it=[iter(outputs),iter(rout)]
        wires[i:i+len(l)]=[(int(x in right),next(it[int(x in right)])) for x in r]
    return wires,tiles,ports,crossings


def compare(source,right,traces,anchored):
    column=Column(sum(x not in right for x in source))
    a,b=[reading(column,source,right,path,anchored) for path in traces]
    if a[:3]!=b[:3]:
        return None
    _,tiles,ports,initial=a
    final=b[3]
    current={e:list(initial.get(e,())) for e in column.endpoints}
    certificate=[]
    for p in sorted(tiles):
        ins,out=column.polygons[p]
        remainder=None
        for e in ins:
            target=final.get(e,[])
            word=current[e]
            if word[:len(target)]!=target:
                return None
            tail=word[len(target):]
            if remainder is None:
                remainder=tail
            elif remainder!=tail:
                return None
        if p in ports and remainder:
            return None
        for f in reversed(remainder):
            for e in ins:
                assert current[e].pop()==f
            for e in out:
                assert f not in current[e]
                current[e].insert(0,f)
            certificate.append((p,f))
    if any(current[e]!=final.get(e,[]) for e in column.endpoints):
        return None
    return certificate


def exhaustive(source,rules,right,budget,anchored,solver=compare):
    ids={}
    groups=defaultdict(dict)
    edges=defaultdict(set)
    joint=defaultdict(set)
    todo=[(source,[],0)]
    count=0
    while todo:
        w,path,n=todo.pop()
        u=diagram(source,path,False,ids)
        groups[w][u]=path
        count+=1
        windows=[]
        before=source
        for k,(_,i,l,r) in enumerate(path):
            for alt in negative_to_positive(before,path,k):
                name,_,left,output=alt[k]
                if name in anchored or right.intersection(left+output):
                    continue
                v=diagram(source,alt,False,ids)
                edges[u].add(v)
                windows.append((k,k+len(left)+1,v))
            before=before[:i]+r+before[i+len(l):]
        for (lo,hi,a),(j,end,b) in combinations(windows,2):
            if hi<=j or end<=lo:
                joint[u].add(frozenset((a,b)))
        for name,i,l,r,out in moves(w,rules,right):
            next_count=n+(name!='swap')
            if next_count<=budget:
                todo.append((out,path+[(name,i,l,r)],next_count))
    pairs=diamonds=0
    for group in groups.values():
        for u,first in group.items():
            for a,b in combinations(edges[u],2):
                assert frozenset((a,b)) in joint[u] and edges[a]&edges[b]
                diamonds+=1
            reached={u}
            work=[u]
            while work:
                for v in edges[work.pop()]-reached:
                    reached.add(v)
                    work.append(v)
            for v,second in group.items():
                assert (solver(source,right,(first,second),anchored) is not None)==(v in reached)
                pairs+=1
    return count,pairs,diamonds


def agda_example(directory,transfers=False):
    from catt import arr, comp2, glue_tree, infer, maximal_vars, src, tgt, tree_ctx, v
    from emit_agda import Emitter
    from semistrict_surface_scalar_cube import exchange
    ctx=tree_ctx(glue_tree(1,0,1))
    f,g=map(v,maximal_vars(ctx))
    def between(s,t):
        assert infer(ctx,s)==infer(ctx,t)
        return arr(infer(ctx,s),s,t)
    def declare(ty):
        nonlocal ctx
        x=v(len(ctx))
        ctx+=(ty,)
        return x
    a,x,y=(declare(between(f,f)) for _ in range(3))
    b=declare(between(g,g))
    declare(between(a,comp2(ctx,1,x,y)))
    crossing=exchange(ctx,a,b)
    stationary=comp2(ctx,0,a,g)
    birth=declare(between(stationary,src(ctx,crossing)))
    death=declare(between(tgt(ctx,crossing),stationary))
    if transfers:
        only_right=comp2(ctx,0,f,b)
        declare(between(stationary,only_right))
        declare(between(only_right,stationary))
    for e in (a,x,y):
        j=exchange(ctx,e,b)
        declare(between(tgt(ctx,j),src(ctx,j)))
    emitter=Emitter()
    name='SharedWireTransfers' if transfers else 'SharedWireBirths'
    whole=emitter.ctx(ctx)
    emitter.checks.append(f'context-ok : is-just (checkCtx {whole}) ≡ true' + chr(10) + 'context-ok = refl' + chr(10))
    emitter.check_typed('birth',ctx,birth)
    emitter.check_typed('death',ctx,death)
    source=emitter.module(name,'Right wire creation and consumption at shared rules.').replace(
        'open import CaTTExp.Pure','open import CaTTExp.Gray.Pure')
    (directory/(name+'.agda')).write_text(source)


def checks():
    cases=[('aa',[('split','a','xy'),('birth','a','Ba'),('death','aB','a')],3,()),
           ('Ba',[('update','a','a'),('birth','a','BaB'),('death','BaB','a')],3,()),
           ('aB',[('split','a','xy'),('birth','x','xM'),('death','yB','y'),('return','yM','My')],4,()),
           ('aBa',[('grow','a','aB'),('die','aB','a'),('private','a','a'),('fixed','a','a')],3,('fixed',)),
           ('Baa',[('born','aa','xMBy'),('die','xyM','a'),('p','x','xx'),('q','y','y')],3,())]
    totals=[0,0,0]
    for w,r,b,fixed in cases:
        value=exhaustive(tuple(w),[(n,tuple(l),tuple(t)) for n,l,t in r],set('BM'),b,fixed)
        totals=[x+y for x,y in zip(totals,value)]
    return dict(zip(('readings','ordered_pairs','simultaneous_prisms'),totals))


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    parser.add_argument('--agda-dir',type=Path)
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        source,right=tuple(q['source']),set(q['right_letters'])
        rules=[(n,tuple(l),tuple(r)) for n,(l,r) in q['rules'].items()]
        anchored=set(q.get('anchored',()))
        if any(n=='swap' or not set(l)-right or not set(r)-right for n,l,r in rules):
            raise ValueError('every rule needs at least one left wire on each side')
        if not anchored<={n for n,l,r in rules if not right.intersection(l+r)}:
            raise ValueError('anchored names must have two left-only sides')
        w,u=parse(source,rules,right,q['first'])
        vword,v=parse(source,rules,right,q['second'])
        if w!=vword:
            raise ValueError('expected parallel readings')
        cert=compare(source,right,(u,v),anchored)
        result=dict(raw=cert is not None,surface=cert is not None,prisms=cert)
    else:
        result=checks()
    if args.agda_dir:
        agda_example(args.agda_dir)
    print(json.dumps(result))
