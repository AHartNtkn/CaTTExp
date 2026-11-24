"""Compare old Gray diagrams with one right event and shared positive 3-rules."""
from argparse import ArgumentParser
from collections import Counter, defaultdict, deque
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_planar_cylinder import moves, negative_to_positive, parse
from semistrict_surface_planar_tensor import Column
from semistrict_surface_square_mutex import diagram


def annotated(column,source,observer,trace):
    inputs=iter(column.inputs)
    wires=[None if x==observer else next(inputs) for x in source]
    polygons=set()
    gates=[]
    segments=[[]]
    for name,i,l,r in trace:
        if name=='swap':
            _,e=wires[i:i+2]
            wires[i:i+2]=[e,None]
            segments[-1].append(e)
        else:
            inputs=[e for e in wires[i:i+len(l)] if e is not None]
            p,outputs=column.tile(name,inputs,len(r)-r.count(observer))
            fresh=iter(outputs)
            wires[i:i+len(l)]=[None if x==observer else next(fresh) for x in r]
            polygons.add(p)
            if observer in l:
                gates.append(p)
                segments.append([])
    return wires,polygons,gates,segments


def comparison(source,observer,first,second):
    column=Column(len(source)-source.count(observer))
    w,polygons,gates,before=annotated(column,source,observer,first)
    v,others,shared,after=annotated(column,source,observer,second)
    if w!=v or polygons!=others or gates!=shared:
        return None
    flips=[]
    for i,(old,new) in enumerate(zip(before,after,strict=True)):
        difference=Counter(new)
        difference.subtract(old)
        region=column.fill_cycle(difference,polygons)
        if any(p in gates or n<0 for p,n in region.items()):
            return None
        flips.extend((i,p,n) for p,n in sorted(region.items()))
    return flips


def exhaustive(source,observer,rules,budget):
    groups=defaultdict(dict)
    edges=defaultdict(set)
    ids={}
    simultaneous=defaultdict(set)
    readings=0
    todo=[(source,[],0)]
    while todo:
        w,path,n=todo.pop()
        u=diagram(source,path,False,ids)
        groups[w][u]=path
        readings+=1
        prev=source
        windows=[]
        for k,(_,i,l,r) in enumerate(path):
            for alt in negative_to_positive(prev,path,k):
                if observer in alt[k][2]:
                    continue
                v=diagram(source,alt,False,ids)
                edges[u].add(v)
                windows.append((k,k+len(alt[k][2])+1,v))
            prev=prev[:i]+r+prev[i+len(l):]
        for (lo,hi,a),(start,end,b) in combinations(windows,2):
            if hi<=start or end<=lo:
                simultaneous[u].add(frozenset((a,b)))
        for name,i,l,r,out in moves(w,rules,{observer}):
            count=n+(name!='swap')
            if count<=budget:
                todo.append((out,path+[(name,i,l,r)],count))
    pairs=commutations=0
    for group in groups.values():
        for u,first in group.items():
            for a,b in combinations(edges[u],2):
                assert frozenset((a,b)) in simultaneous[u]
                assert edges[a]&edges[b]
                commutations+=1
            reached={u}
            queue=[u]
            while queue:
                for v in edges[queue.pop()]-reached:
                    reached.add(v)
                    queue.append(v)
            for v,second in group.items():
                assert (comparison(source,observer,first,second) is not None)==(v in reached)
                pairs+=1
    return readings,pairs,commutations


def compiled_returns(machine):
    from semistrict_surface_prism_counters import state
    from semistrict_surface_square_mutex import compile_machine
    rules,_=compile_machine(machine)
    private=[rule for rule in rules if '/' in rule[0]]
    private.extend([('open',('S',),('L',state(machine['start']),'E')),
                    ('finish',('L','done','E'),('S',))])
    letters={x for _,l,r in private for x in l+r}
    shared=[('return/'+x,(x,'B'),('B',x)) for x in sorted(letters-{'S'})]
    return letters,private+shared


def elementary(letters,observer,rules,limit):
    def reach(x):
        start=(x,observer)
        queue=deque([start])
        seen={start}
        processed=0
        while queue:
            if processed>=limit:
                return None
            processed+=1
            for *_,out in moves(queue.popleft(),rules,{observer}):
                if out==(observer,x):
                    return True
                if out not in seen:
                    seen.add(out)
                    queue.append(out)
        return False
    return {x:reach(x) for x in sorted(letters)}


def agda_example(directory):
    from catt import arr, comp2, glue_tree, infer, maximal_vars, src, tgt, tree_ctx, v
    from emit_agda import Emitter
    from semistrict_surface_scalar_cube import exchange
    ctx=tree_ctx(glue_tree(2,0,2))
    a,b=map(v,maximal_vars(ctx))
    def declare(ty):
        nonlocal ctx
        cell=v(len(ctx))
        ctx+=(ty,)
        return cell
    def between(left,right):
        assert infer(ctx,left)==infer(ctx,right)
        return arr(infer(ctx,left),left,right)
    f,g=src(ctx,a),tgt(ctx,a)
    middle=declare(infer(ctx,f))
    x=declare(between(f,middle))
    y=declare(between(middle,g))
    xy=comp2(ctx,1,x,y)
    declare(between(a,xy))
    declare(between(xy,a))
    for cell in (a,x,y):
        crossing=exchange(ctx,cell,b)
        last=declare(between(tgt(ctx,crossing),src(ctx,crossing)))
    emitter=Emitter()
    g=emitter.ctx(ctx)
    emitter.checks.append(f'context-ok : is-just (checkCtx {g}) ≡ true' + chr(10) + 'context-ok = refl' + chr(10))
    emitter.check_typed('last-return',ctx,last)
    name='ObserverReturns'
    source=emitter.module(name,'A conservative positive split/merge context with shared returns.').replace(
        'open import CaTTExp.Pure','open import CaTTExp.Gray.Pure')
    (directory/(name+'.agda')).write_text(source)


def checks():
    rules=[('split','a','xy'),('merge','xy','a'),('return-a','aB','Ba'),
           ('return-x','xB','Bx'),('return-y','yB','By')]
    cases=[('Ba',rules,4),('Baa',rules,3),('aBa',rules,3),
           ('Baa',[('private','a','a'),('reopen','aB','Ba')],4),
           ('aB',[('long-split','aB','xBy'),('long-merge','xyB','Ba'),
                  ('split','a','xy'),('x','x','x')],4),
           ('Baa',[('left','a','xy'),('mid','xBy','aB'),('outer','aaB','Baa')],3)]
    counts=[0,0,0]
    for w,rr,b in cases:
        sample=exhaustive(tuple(w),'B',[(n,tuple(l),tuple(r)) for n,l,r in rr],b)
        counts=[a+c for a,c in zip(counts,sample)]
    for should_halt,program in [(True,{'s':['inc',0,'h']}),
                                (False,{'s':['inc',0,'d'],'d':['test',0,'h','s']})]:
        letters,machine_rules=compiled_returns(dict(start='s',halt='h',program=program))
        result=elementary(letters,'B',machine_rules,5000)
        assert result['S']==should_halt and all(result[a] for a in letters-{'S'})
    return dict(zip(('readings','parallel_comparisons','simultaneous_prism_pairs'),counts))


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group()
    group.add_argument('--query',type=Path)
    group.add_argument('--machine',type=Path)
    parser.add_argument('--limit',type=int,default=5000)
    parser.add_argument('--agda-dir',type=Path)
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        source,b=tuple(q['source']),q['observer']
        rules=[(n,tuple(l),tuple(r)) for n,(l,r) in q['rules'].items()]
        if source.count(b)>1 or any(n=='swap' or l.count(b)!=r.count(b) or l.count(b)>1
                                    or len(l)==l.count(b) or len(r)==r.count(b) for n,l,r in rules):
            raise ValueError('each side must be left-positive and preserve the optional observer')
        left,u=parse(source,rules,{b},q['first'])
        right,v=parse(source,rules,{b},q['second'])
        if left!=right:
            raise ValueError('expected parallel 3-readings')
        cert=comparison(source,b,u,v)
        result=dict(raw=cert is not None,surface=cert is not None,prisms=cert)
    elif args.machine:
        letters,rules=compiled_returns(json.loads(args.machine.read_text()))
        answers=elementary(letters,'B',rules,args.limit)
        reflection=False if False in answers.values() else (True if all(answers.values()) else None)
        result=dict(elementary_returns=answers,all_dimensional=reflection)
    else:
        result=checks()
    if args.agda_dir:
        agda_example(args.agda_dir)
    print(json.dumps(result))
