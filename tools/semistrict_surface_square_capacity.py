"""Finite degree-four queries and degree-five collisions on width-preserving squares."""
from argparse import ArgumentParser
from collections import deque
import json
from pathlib import Path

from semistrict_surface_prism_counters import instructions_for, state
from semistrict_surface_square_machine import erase, steps
from semistrict_surface_square_mutex import compare, end, restore


def compile_machine(machine):
    instructions_for(dict(machine,input=[0,0]))
    rules=[]
    def add(name,left,right):
        rules.append((name,tuple(left),tuple(right)))
    add('take',['K','j'],['H','X'])
    add('grow',['Z','H'],['H','T0'])
    add('launch',['H','T0'],['L',state(machine['start'])])
    add('release',['A','X'],['C','j'])
    add('observe',['j','B'],['j','D'])
    add('bare-observe',['B'],['D'])
    add('bare-close',['K'],['C'])
    for q,(op,k,*dest) in machine['program'].items():
        for mask in range(4):
            t=f'T{mask}'
            name=f'{op}/{q}/{mask}'
            if bool(mask & (1<<k))==(op=='inc'):
                add(name,[state(q),t],[t,state(q)])
            else:
                target=dest[0] if op=='inc' else dest[1]
                add(name,[state(q),t],['ret/'+target,f'T{mask^(1<<k)}'])
        if op=='test':
            add('zero/'+q,[state(q),'X'],['ret/'+dest[0],'X'])
    for q in sorted({*machine['program'],machine['halt']}):
        ret='ret/'+q
        for mask in range(4):
            t=f'T{mask}'
            add(f'return/{q}/{mask}',[t,ret],[ret,t])
        add('resume/'+q,['L',ret],['L',state(q)])
    h=state(machine['halt'])
    for mask in range(4):
        add(f'clear/{mask}',[h,f'T{mask}'],['T0',h])
    add('turn',[h,'X'],['back','X'])
    add('return-clean',['T0','back'],['back','T0'])
    add('shrink-start',['L','back'],['A','T0'])
    add('shrink',['A','T0'],['Z','A'])
    shapes={x:'UU' for _,l,r in rules for x in l+r}
    shapes.update(j='UV',X='UV',r='VU',B='VV',D='VV')
    for _,l,r in rules:
        assert len(l)==len(r) and 1<=len(l)<=2
        assert weight(erase(l))==weight(erase(r))
        assert any(end(shapes,b,l) is not None and end(shapes,b,l)==end(shapes,b,r) for b in 'UV')
    return rules,shapes


def weight(w):
    return sum(2 if x in ('K','C') else 1 for x in w)


def reachable(w,rules):
    queue=deque([w])
    seen={w}
    while queue:
        for *_,nxt in steps(queue.popleft(),rules):
            if nxt not in seen:
                queue.append(nxt)
                seen.add(nxt)
    return seen


def outcomes(shapes,rules,root,w):
    target=end(shapes,root,w)
    if target is None:
        raise ValueError('ill-typed source')
    raw=reachable(w,rules)
    projected=[(n,erase(l),erase(r)) for n,l,r in rules]
    signed={positive for out in reachable(erase(w),projected)
            if (positive:=restore(shapes,root,out,target)) is not None}
    return raw,signed


def collision(shapes,rules,capacity):
    if capacity<0:
        raise ValueError('negative capacity')
    source=('Z',)*(capacity+1)+('K','j','B')
    def run(first):
        w=source
        trace=[]
        def apply(name):
            nonlocal w
            step=next(s for s in steps(w,rules) if s[0]==name)
            trace.append(step[:2])
            w=step[-1]
        if first:
            apply('observe')
        apply('take')
        for _ in range(capacity+1):
            apply('grow')
        apply('launch')
        seen=set()
        while 'X' in w:
            choices=[n for n,_,_,_,_ in steps(w,rules) if n!='bare-observe']
            if not choices or w in seen:
                return None
            assert len(choices)==1,(w,choices)
            seen.add(w)
            apply(choices[0])
        if not first:
            apply('observe')
        return trace
    left=run(True)
    if left is None:
        return None
    query=dict(root='U',source=source,left=left,right=run(False))
    assert compare(shapes,rules,query)==dict(raw=False,surface=True)
    return query


def bounded_halts(machine,capacity):
    state_name=machine['start']
    counts=[0,0]
    seen=set()
    while state_name!=machine['halt']:
        key=(state_name,*counts)
        if key in seen:
            return False
        seen.add(key)
        op,k,*dest=machine['program'][state_name]
        if op=='inc':
            if counts[k]==capacity:
                return False
            counts[k]+=1
            state_name=dest[0]
        elif counts[k]:
            counts[k]-=1
            state_name=dest[1]
        else:
            state_name=dest[0]
    return True


def agda_context(directory,rules,shapes):
    from emit_agda import Emitter
    from semistrict_surface_square_machine import square_context
    ctx,*_=square_context(rules,shapes)
    emitter=Emitter()
    g=emitter.ctx(ctx)
    emitter.checks.append(f'bounded-rules : is-just (checkCtx {g}) ≡ true\nbounded-rules = refl\n')
    name='SquareCapacity'
    source=emitter.module(name,'Binary attachments of a width-preserving square.').replace(
        'open import CaTTExp.Pure','open import CaTTExp.Gray.Pure')
    (directory/(name+'.agda')).write_text(source)


def checks():
    yes=dict(start='s',halt='h',program={'s':['inc',0,'t'],'t':['inc',0,'v'],
             'v':['inc',1,'d'],'d':['test',0,'s','h']})
    no=dict(start='s',halt='h',program={'s':['inc',0,'d'],'d':['test',0,'h','s']})
    roots=[('U','KjB'),('U','ZKjB'),('U','ZZKjB'),('U','ZZZKjB'),
           ('U','ZKXBrKjB'),('U','KZKjBB'),('V','BrKjDD'),
           ('U',('L','back','X','B')),('U',('A','T0','X','B'))]
    totals=dict(old_sources=0,raw_endpoints=0,capacity_decisions=0)
    for machine in (yes,no):
        rules,shapes=compile_machine(machine)
        for root,source in roots:
            orig,projected=outcomes(shapes,rules,root,tuple(source))
            assert orig==projected,(source,orig^projected)
            totals['old_sources']+=1
            totals['raw_endpoints']+=len(orig)
        for capacity in range(5):
            query=collision(shapes,rules,capacity)
            assert bool(query)==(machine==yes and capacity>=2)
            if machine==yes and capacity==2:
                totals['collision_vertices']=len(query['left'])
            totals['capacity_decisions']+=1
    from itertools import product
    choices=[['inc',k,q] for k,q in product((0,1),('s','t','h'))]
    choices += [['test',k,a,b] for k,a,b in product((0,1),('s','t','h'),('s','t','h'))]
    for a,b in product(choices,repeat=2):
        machine=dict(start='s',halt='h',program={'s':a,'t':b})
        rules,shapes=compile_machine(machine)
        for capacity in (0,1,2):
            query=collision(shapes,rules,capacity)
            assert bool(query)==bounded_halts(machine,capacity),(machine,capacity)
            totals['capacity_decisions']+=1
    return totals


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--machine',type=Path)
    parser.add_argument('--agda-dir',type=Path)
    group=parser.add_mutually_exclusive_group()
    group.add_argument('--capacity',type=int)
    group.add_argument('--query',type=Path)
    group.add_argument('--compare',type=Path)
    args=parser.parse_args()
    if not args.machine and (args.capacity is not None or args.query or args.compare):
        parser.error('supply --machine for a query')
    if args.machine:
        rules,shapes=compile_machine(json.loads(args.machine.read_text()))
        if args.capacity is not None:
            result=dict(collision=collision(shapes,rules,args.capacity))
        elif args.compare:
            result=compare(shapes,rules,json.loads(args.compare.read_text()))
        elif args.query:
            q=json.loads(args.query.read_text())
            w,target=tuple(q['source']),tuple(q['target'])
            if end(shapes,q['root'],target)!=end(shapes,q['root'],w):
                raise ValueError('expected parallel paths')
            raw,sg=outcomes(shapes,rules,q['root'],w)
            result=dict(raw=target in raw,surface=target in sg)
        else:
            result=dict(arrows=shapes,attachments=rules)
    else:
        result=checks()
    if args.agda_dir:
        if not args.machine:
            rules,shapes=compile_machine(dict(start='s',halt='h',program={'s':['inc',0,'h']}))
        agda_context(args.agda_dir,rules,shapes)
    print(json.dumps(result))
