"""Degree-five faithfulness on the two-column square with positive long rules.

--machine FILE emits the finite square presentation of blank-input halting.
--run N searches for a collision for at most N rewriting steps per trace.
--compare FILE checks two finite traces at the same degree-five boundary.
--agda-dir DIR writes a raw Gray-CaTT check of a concrete halting boundary.
"""
from argparse import ArgumentParser
from collections import Counter
from itertools import product
import json
from pathlib import Path

from semistrict_surface_prism_counters import instructions_for, state
from semistrict_surface_square_machine import check_atom, erase, steps


def compile_machine(machine):
    ins=instructions_for(dict(machine,input=[0,0]))
    rules=[]
    def add(name,l,r):
        rules.append((name,tuple(l),tuple(r)))
    add('take',['K','j'],['L',state(machine['start']),'E','X'])
    add('release',['L','done','E','X'],['C','j'])
    add('observe',['j','B'],['j','D'])
    add('bare-observe',['B'],['D'])
    add('bare-close',['K'],['C'])
    for q,(op,k,*dest) in ins.items():
        if op=='inc':
            add('inc/'+q,[q],['a',dest[0]] if k==0 else [dest[0],'b'])
        elif k==0:
            add('zero/'+q,['L',q],['L',dest[0]])
            add('dec/'+q,['a',q],[dest[1]])
        else:
            add('zero/'+q,[q,'E'],[dest[0],'E'])
            add('dec/'+q,[q,'b'],[dest[1]])
    shapes={x:'UU' for _,l,r in rules for x in l+r}
    shapes.update(j='UV',X='UV',r='VU',B='VV',D='VV')
    for _,l,r in rules:
        assert any(end(shapes,b,l) is not None and end(shapes,b,l)==end(shapes,b,r) for b in 'UV')
    return rules,shapes


def end(shapes,start,w):
    b=start
    for x in w:
        a,c=shapes[x]
        if a!=b:
            return None
        b=c
    return b


def restore(shapes,start,w,target):
    b=start
    result=[]
    for x in (*w,None):
        a=target if x is None else shapes[x][0]
        if a!=b:
            if b=='V':
                return None
            result.append('j')
            b='V'
        if x is not None:
            result.append(x)
            b=shapes[x][1]
    return tuple(result)


def diagram(source,trace,project,identifiers):
    """Canonical incidence with named input wires and ordered ports."""
    w=source
    boundary=erase(w) if project else w
    wires=[(-1,i) for i in range(len(boundary))]
    nodes=set()
    for name,i,l,r in trace:
        assert w[i:i+len(l)]==l
        pos=len(erase(w[:i])) if project else i
        n=len(erase(l)) if project else len(l)
        m=len(erase(r)) if project else len(r)
        key=(name,tuple(wires[pos:pos+n]))
        node=identifiers.setdefault(key,len(identifiers))
        assert node not in nodes
        nodes.add(node)
        wires[pos:pos+n]=[(node,j) for j in range(m)]
        w=w[:i]+r+w[i+len(l):]
    return w,frozenset(nodes),tuple(wires)


def compare(shapes,rules,query):
    source=tuple(query['source'])
    if query['root'] not in ('U','V') or end(shapes,query['root'],source) is None:
        raise ValueError('ill-typed source')
    def read(trace):
        w=source
        vertices=[]
        for name,pos in trace:
            choice=next((step for step in steps(w,rules) if step[:2]==(name,pos)),None)
            if choice is None:
                raise ValueError(f'{name} at {pos} does not apply to {w}')
            _,_,l,r,w=choice
            vertices.append((name,pos,l,r))
        return w,vertices
    a,left=read(query['left'])
    b,right=read(query['right'])
    if a!=b:
        raise ValueError('expected parallel traces')
    def equal(project):
        identifiers={}
        return diagram(source,left,project,identifiers)==diagram(source,right,project,identifiers)
    return dict(raw=equal(False),surface=equal(True))


def collision_traces(rules,limit):
    start=('K','j','B')
    def path(first):
        w=start
        trace=[]
        for turn in range(limit+1):
            choices=list(steps(w,rules))
            if (turn==0 and first) or ('C' in w and 'B' in w):
                want='observe'
            elif 'K' in w:
                want='take'
            elif 'X' in w:
                want=next((n for n,_,_,_,_ in choices if n=='release' or '/' in n),None)
            else:
                return w,trace
            chosen=next((r for r in choices if r[0]==want),None)
            if chosen is None:
                return None,None
            n,i,l,r,w=chosen
            trace.append((n,i,l,r))
        return None,None
    a,first=path(True)
    b,second=path(False)
    if a is None or b is None:
        return None
    assert a==b==('C','j','D')
    return first,second


def witness(shapes,rules,limit):
    pair=collision_traces(rules,limit)
    if pair is None:
        return None
    first,second=pair
    query=dict(root='U',source=['K','j','B'],
               left=[(n,i) for n,i,_,_ in first],right=[(n,i) for n,i,_,_ in second])
    answer=compare(shapes,rules,query)
    assert answer==dict(raw=False,surface=True)
    return dict(vertices=len(first),**answer,query=query)


def lift(shapes,rules,root,start,trace):
    """Construct a positive raw route for each projected degree-four proof."""
    raw=start
    env=[(x,None) for x in erase(start)]
    logs={}
    def apply(name,pos):
        nonlocal raw
        outputs=[v for n,i,_,_,v in steps(raw,rules) if n==name and len(erase(raw[:i]))==pos]
        assert len(outputs)==1,(raw,name,pos)
        raw=outputs[0]
    for i,(name,pos,l,r) in enumerate(trace):
        assert tuple(x for x,_ in env[pos:pos+len(l)])==l
        pre=env[:pos]
        offset=sum(1 for j,(_,tag) in enumerate(pre) if tag is None or j==0 or pre[j-1][1]!=tag)
        tag=env[pos][1]
        if name=='take':
            logs[i]=[]
            env[pos:pos+len(l)]=[(x,i) for x in r]
        elif tag is None:
            assert all(k is None for _,k in env[pos:pos+len(l)])
            apply('bare-observe' if name=='observe' else name,offset)
            env[pos:pos+len(l)]=[(x,None) for x in r]
        else:
            assert all(k==tag for _,k in env[pos:pos+len(l)])
            if name=='release':
                apply('bare-close',offset)
                env[pos:pos+len(l)]=[(x,None) for x in r]
            else:
                first=next(j for j,(_,k) in enumerate(env) if k==tag)
                logs[tag].append((name,pos-first))
                env[pos:pos+len(l)]=[(x,tag) for x in r]
    pos=0
    while pos<len(env):
        _,tag=env[pos]
        if tag is None:
            pos+=1
        else:
            apply('take',pos)
            for name,i in logs[tag]:
                apply(name,pos+i)
            while pos<len(env) and env[pos][1]==tag:
                pos+=1
    assert erase(raw)==tuple(x for x,_ in env)
    return raw


def agda_boundary(directory):
    from catt import (arr, comp_tree, infer, maximal_vars, src, sub_from,
                      subst_tm, tgt, tree_ctx, v)
    from emit_agda import Emitter
    from relative_coherence_exchange_faces import composite, head, string_tree
    from semistrict_surface_square_machine import square_context
    rules,shapes=compile_machine(dict(start='s',halt='h',program={'s':['inc',0,'h']}))
    ctx,terms,vertices,word=square_context(rules,shapes)

    def adapter(w,pos,size,forward):
        # Compare the complete left bracketing to the bracketing of one rewrite window.
        ps=tree_ctx(string_tree(2,[3]*len(w)))
        slots=maximal_vars(ps)
        leaves=list(map(v,slots))
        canonical=composite(ps,2,leaves)
        window=composite(ps,2,leaves[pos:pos+size])
        parts=leaves[:pos]+[window]+leaves[pos+size:]
        grouped=comp_tree(string_tree(2,[3]*len(parts)),ps,parts)
        if grouped==canonical:
            return None
        source,target=(canonical,grouped) if forward else (grouped,canonical)
        sigma=sub_from(ps,ctx,dict(zip(slots,(terms[x] for x in w))))
        return subst_tm(head(ps,source,target),sigma)

    def realize(trace):
        current=('K','j','B')
        pieces=[]
        for name,pos,l,r in trace:
            rest=pos+len(l)
            sides=[terms[x] for x in current[:pos]]+[vertices[name]]+[terms[x] for x in current[rest:]]
            rewrite=comp_tree(string_tree(2,[3]*pos+[4]+[3]*(len(current)-rest)),ctx,sides)
            following=current[:pos]+r+current[rest:]
            parts=[t for t in (adapter(current,pos,len(l),True),rewrite,
                               adapter(following,pos,len(r),False)) if t is not None]
            assert src(ctx,parts[0])==word(current) and tgt(ctx,parts[-1])==word(following)
            assert all(tgt(ctx,a)==src(ctx,b) for a,b in zip(parts,parts[1:]))
            pieces.extend(parts)
            current=following
        return composite(ctx,3,pieces)

    first,second=map(realize,collision_traces(rules,20))
    assert infer(ctx,first)==infer(ctx,second)
    emitter=Emitter()
    boundary=ctx+(arr(infer(ctx,first),first,second),)
    g=emitter.ctx(boundary)
    emitter.checks.append(f'old-five-boundary : is-just (checkCtx {g}) ≡ true\nold-five-boundary = refl\n')
    name='SquareMutex'
    source=emitter.module(name,'Parallel raw four-pastes at the collision.').replace(
        'open import CaTTExp.Pure','open import CaTTExp.Gray.Pure')
    (directory/(name+'.agda')).write_text(source)


def checks():
    yes=dict(start='s',halt='h',program={'s':['inc',0,'h']})
    no=dict(start='s',halt='h',program={'s':['inc',0,'d'],'d':['test',0,'h','s']})
    counts=Counter()
    proof=None
    for machine in (yes,no):
        rules,shapes=compile_machine(machine)
        projected=[(n,erase(l),erase(r)) for n,l,r in rules]
        found=witness(shapes,rules,100)
        if machine==yes:
            proof=found
            assert proof
        else:
            assert found is None
        for _,l,r in rules:
            check_atom(len(l),len(r))
        for root,word in [('U','KjB'),('U','KKjBB'),('U','KXBrKjB'),
                          ('V','BrKjDD'),('U',('L','done','E','X','B'))]:
            start=tuple(word)
            target=end(shapes,root,start)
            assert target is not None
            todo=[(erase(start),[])]
            while todo:
                w,path=todo.pop()
                positive=restore(shapes,root,w,target)
                if positive is not None:
                    assert lift(shapes,rules,root,start,path)==positive
                    counts['lifted_degree_four_paths']+=1
                if len(path)<5:
                    for n,i,l,r,out in steps(w,projected):
                        todo.append((out,path+[(n,i,l,r)]))
    rules,shapes=compile_machine(no)
    def check_source(w):
        observed={}
        raw_ids,projected_ids={},{}
        todo=[(w,[])]
        while todo:
            cur,path=todo.pop()
            proj=diagram(w,path,True,projected_ids)
            actual=diagram(w,path,False,raw_ids)
            assert observed.setdefault(proj,actual)==actual
            counts['nonhalting_diagrams']+=1
            if len(path)<3:
                for n,i,l,r,out in steps(cur,rules):
                    todo.append((out,path+[(n,i,l,r)]))
        counts['tested_old_sources']+=1
    for root in 'UV':
        for k in range(5):
            for w in product(('j','r','K','X','B','C'),repeat=k):
                if end(shapes,root,w) is not None:
                    check_source(w)
    return dict(**counts,halting_collision=proof)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--machine',type=Path)
    parser.add_argument('--run',type=int)
    parser.add_argument('--compare',type=Path)
    parser.add_argument('--agda-dir',type=Path)
    args=parser.parse_args()
    if args.compare and not args.machine:
        parser.error('--compare requires --machine')
    if args.machine:
        rules,shapes=compile_machine(json.loads(args.machine.read_text()))
        if args.compare:
            result=compare(shapes,rules,json.loads(args.compare.read_text()))
        elif args.run is not None:
            result=dict(collision=witness(shapes,rules,args.run))
        else:
            result=dict(arrows=shapes,attachments=rules)
    else:
        result=checks()
    if args.agda_dir:
        agda_boundary(args.agda_dir)
    print(json.dumps(result))
