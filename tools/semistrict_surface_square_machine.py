"""Compile a unary-input two-counter machine to a finite Gray square.

--machine JSON gives start, halt, and instructions (inc/test) with 0-based
counters. --input N queries S A^N E -> T at V. --source/--target are JSON
word lists for other positive queries at --root U or V. Raw words use j:U->V,
r:V->U, F at U, and all remaining letters at V.
"""
from argparse import ArgumentParser
from collections import Counter, deque
from itertools import product
import json
from pathlib import Path

from semistrict_surface_prism_counters import instructions_for, state


def compile_machine(machine):
    ins=instructions_for(dict(machine,input=[0,0]))
    rules=[]
    def add(name,l,r):
        rules.append((name,tuple(l),tuple(r)))
    add('open',['j','S'],['F','j','Z'])
    add('scan',['Z','A'],['Z'])
    add('finish',['F','j','Z','E'],['j','T'])
    add('parse',['S'],['L','parse'])
    add('read',['parse','A'],['A','parse'])
    add('run',['parse','E'],[state(machine['start']),'E'])
    for q,(op,k,*dest) in ins.items():
        if op=='inc':
            add('inc/'+q,[q],['A',dest[0]] if k==0 else [dest[0],'B'])
        elif k==0:
            add('zero/'+q,['L',q],['L',dest[0]])
            add('dec/'+q,['A',q],[dest[1]])
        else:
            add('zero/'+q,[q,'E'],[dest[0],'E'])
            add('dec/'+q,[q,'B'],[dest[1]])
    add('accept',['L','done','E'],['T'])
    return rules


def erase(w):
    return tuple(x for x in w if x!='j')


def target(start,w):
    s=start
    for x in w:
        need,give={'j':('U','V'),'r':('V','U'),'F':('U','U')}.get(x,('V','V'))
        if need!=s:
            return None
        s=give
    return s


def steps(w,rules):
    for name,l,r in rules:
        for i in range(len(w)-len(l)+1):
            if w[i:i+len(l)]==l:
                yield name,i,l,r,w[:i]+r+w[i+len(l):]


class Square:
    def __init__(self,rules):
        self.raw=rules
        self.surface=[(n,erase(l),erase(r)) for n,l,r in rules]
        self.alphabet={'r','j'}|{x for _,l,r in rules for x in l+r}
        for _,l,r in rules:
            if not any(target(b,l) is not None and target(b,l)==target(b,r) for b in 'UV'):
                raise ValueError('rule faces must be parallel paths')

    def reach(self,b,u,v,signed,limit):
        if target(b,u) is None or target(b,u)!=target(b,v):
            raise ValueError('query must have parallel positive paths')
        if not set(u+v)<=self.alphabet:
            raise ValueError('unknown word letter')
        rules=self.surface if signed else self.raw
        if signed:
            u,v=erase(u),erase(v)
        todo=deque([u])
        seen={u}
        count=0
        while todo:
            w=todo.popleft()
            if w==v:
                return True
            if count==limit:
                return None
            count+=1
            for *_,out in steps(w,rules):
                if out not in seen:
                    seen.add(out)
                    todo.append(out)
        return False


def restore(root,word,end):
    """The only positive representative with these endpoints after erasing j."""
    actual=[]
    at=root
    for x in (*word,None):
        need=end if x is None else ('U' if x=='F' else 'V')
        if at!=need:
            if at!='U':
                return None
            actual.append('j')
            at='V'
        if x is not None:
            actual.append(x)
            at=target(at,(x,))
    return tuple(actual)


def lift_trace(square,root,source,trace,y_proofs):
    """Lift a signed derivation ending at a positive old face, using Y certificates."""
    current=source
    tags=[(x,None) for x in erase(source)]
    scans={}
    def width(tok):
        x,j=tok
        return 1 if j is None else (0 if x=='F' else 1+scans[j])
    def apply(name,offset):
        nonlocal current
        options=[w for n,i,_,_,w in steps(current,square.raw)
                 if n==name and len(erase(current[:i]))==offset]
        assert len(options)==1,(name,offset,current)
        current=options[0]
    for time,(name,i,l,r) in enumerate(trace):
        assert tuple(x for x,_ in tags[i:i+len(l)])==l
        pos=sum(width(tok) for tok in tags[:i])
        tag=tags[i][1]
        if name=='open':
            scans[time]=0
            tags[i:i+1]=[('F',time),('Z',time)]
        elif name=='scan' and tag is not None:
            scans[tag]+=1
            tags.pop(i+1)
        elif name=='finish' and tag is not None:
            assert tags[i+1]==('Z',tag)
            for step,j in y_proofs[scans[tag]]:
                apply(step,pos+j)
            tags[i:i+len(l)]=[('T',None)]
        else:
            assert all(tag is None for _,tag in tags[i:i+len(l)])
            apply(name,pos)
            tags[i:i+len(l)]=[(x,None) for x in r]
    pos=0
    while pos<len(tags):
        x,j=tags[pos]
        if j is not None:
            assert x=='F' and tags[pos+1]==('Z',j)
            apply('open',pos)
            for _ in range(scans[j]):
                apply('scan',pos+1)
            pos+=2
        else:
            pos+=1
    assert erase(current)==tuple(x for x,_ in tags)
    return current


def check_traces(square):
    # The test machine decrements the left counter until empty and halts.
    proofs={}
    for n in range(8):
        q=state('s')
        proofs[n]=([('parse',0)]+[('read',j+1) for j in range(n)]+[('run',n+1)]+
                   [('dec/'+q,j) for j in range(n,0,-1)]+[('zero/'+q,0),('zero/'+state('h'),0),
                                                           ('zero/drain1',1),('accept',0)])
    count=0
    def visit(root,src,end,w,path,depth):
        nonlocal count
        positive=restore(root,w,end)
        if positive is not None:
            assert lift_trace(square,root,src,path,proofs)==positive
            count+=1
        if depth:
            for name,i,l,r,out in steps(w,square.surface):
                visit(root,src,end,out,path+[(name,i,l,r)],depth-1)
    for root,w in [('V','SAE'),('U','FjZAE'),('V','SAErjSE'),('U','jSErFjZE'),
                   ('U','FFjZZE'),('V','ESASAE'),('U','jSAAE')]:
        src=tuple(w)
        visit(root,src,target(root,src),erase(src),[],5)
    return count


def check_interchanges(model):
    # Check lift of each adjacent diagram exchange after j-erasure, using
    # literal offsets rather than topological equality of the resulting words.
    totals=Counter()
    def visit(b,w,depth):
        totals['positive_paths']+=1
        for _,i,l,r,w1 in steps(w,model.raw):
            p=len(erase(w[:i]))
            for _,k,c,d,final in steps(w1,model.raw):
                q=len(erase(w1[:k]))
                if q+len(erase(c))<=p:
                    assert k+len(c)<=i
                    first=w[:k]+d+w[k+len(c):]
                    i2=i+len(d)-len(c)
                    assert first[i2:i2+len(l)]==l and first[:i2]+r+first[i2+len(l):]==final
                elif q>=p+len(erase(r)):
                    assert k>=i+len(r)
                    offset=k+len(l)-len(r)
                    assert w[offset:offset+len(c)]==c
                    first=w[:offset]+d+w[offset+len(c):]
                    assert first[i:i+len(l)]==l and first[:i]+r+first[i+len(l):]==final
                else:
                    continue
                totals['lifted_interchanges']+=1
        if depth:
            end=target(b,w)
            for x in ('F','j') if end=='U' else ('A','S','Z','E','r','T'):
                visit(b,w+(x,),depth-1)
    for b in 'UV':
        visit(b,(),5)
    return dict(totals)


def check_atom(m,n):
    """Two strips of quadrilaterals sharing their two boundary edge paths."""
    graph={}
    def arrow(u,v):
        graph.setdefault(u,set()).add(v)
        graph.setdefault(v,set())
    for side,size in enumerate((m,n)):
        prev='bottom'
        for k in range(size):
            nxt='top' if k+1==size else (side,k)
            cell=('tile',side,k)
            for row in (prev,nxt):
                arrow('left',('edgeL',row))
                arrow(('edgeL',row),('mid',row))
                arrow(('mid',row),('edgeR',row))
                arrow(('edgeR',row),'right')
            for edge in ('edgeL','edgeR'):
                arrow((edge,prev),cell)
                arrow(cell,(edge,nxt))
            if side:
                arrow('volume',cell)
            else:
                arrow(cell,'volume')
            prev=nxt
    indeg=Counter(v for vs in graph.values() for v in vs)
    todo=deque(x for x in graph if indeg[x]==0)
    count=0
    while todo:
        x=todo.popleft()
        count+=1
        for y in graph[x]:
            indeg[y]-=1
            if indeg[y]==0:
                todo.append(y)
    assert count==len(graph)


def agda_example(rules,directory):
    from catt import arr, comp2, glue_tree, infer, maximal_vars, src, tgt, tree_ctx, v
    from emit_agda import Emitter
    from semistrict_surface_scalar_cube import exchange
    ctx=tree_ctx(glue_tree(2,0,2))
    j=exchange(ctx,*map(v,maximal_vars(ctx)))
    u,vv=src(ctx,j),tgt(ctx,j)
    terms={'j':j}
    for x in sorted({'r'}|{x for _,l,r in rules for x in l+r}-{'j'}):
        a,b={'r':(vv,u),'F':(u,u)}.get(x,(vv,vv))
        terms[x]=v(len(ctx))
        ctx+=(arr(infer(ctx,a),a,b),)
    def word(w):
        cell=terms[w[0]]
        for x in w[1:]:
            cell=comp2(ctx,2,cell,terms[x])
        return cell
    for _,l,r in rules:
        left,right=word(l),word(r)
        assert infer(ctx,left)==infer(ctx,right)
        ctx+=(arr(infer(ctx,left),left,right),)
    emitter=Emitter()
    g=emitter.ctx(ctx)
    emitter.checks.append(f'all-rules : is-just (checkCtx {g}) ≡ true\nall-rules = refl\n')
    emitter.check_typed('old-source',ctx,word(('S','A','A','E')))
    emitter.check_typed('old-target',ctx,word(('T',)))
    emitter.check_typed('last-declaration',ctx,v(len(ctx)-1))
    name='SquareMachine'
    source=emitter.module(name,'Typed machine on the directed square.').replace(
        'open import CaTTExp.Pure','open import CaTTExp.Gray.Pure')
    (directory/(name+'.agda')).write_text(source)


def checks():
    yes=dict(start='s',halt='h',program={'s':['test',0,'h','s']})
    no=dict(start='s',halt='h',program={'s':['inc',0,'d'],'d':['test',0,'h','s']})
    total=0
    for m,expected in ((yes,True),(no,False)):
        model=Square(compile_machine(m))
        for n in range(9):
            w=('S',)+('A',)*n+('E',)
            assert model.reach('V',w,('T',),True,5000)
            assert model.reach('V',w,('T',),False,5000)==expected
            total+=1
        for _,l,r in model.raw:
            check_atom(len(l),len(r))
    # Swap a selected pair of disjoint projected vertices in actual raw paths.
    counts=check_interchanges(Square(compile_machine(yes)))
    # In mixed paths, F is a U-letter and r is an immutable separator.
    model=Square(compile_machine(yes))
    for n in range(4):
        block=('S',)+('A',)*n+('E',)
        for prefix,root in [((),'V'),(('F','j'),'U'),(('r','F','j'),'V')]:
            for suffix in [(),('r','F'),('r','j','S')]:
                assert model.reach(root,prefix+block+suffix,prefix+('T',)+suffix,False,5000)
    for m,n in product(range(1,9),repeat=2):
        check_atom(m,n)
    return dict(halting_queries=total,context_queries=36,atom_shapes=64,
                lifted_surface_derivations=check_traces(model),**counts)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--machine',type=Path)
    parser.add_argument('--input',type=int)
    parser.add_argument('--root',choices=('U','V'),default='V')
    parser.add_argument('--source',type=json.loads)
    parser.add_argument('--target',type=json.loads)
    parser.add_argument('--limit',type=int,default=10000)
    parser.add_argument('--agda-dir',type=Path)
    args=parser.parse_args()
    if args.machine:
        square=Square(compile_machine(json.loads(args.machine.read_text())))
        if args.input is not None:
            if args.input<0:
                raise ValueError('negative input')
            u,v=('S',)+('A',)*args.input+('E',),('T',)
            root='V'
        elif args.source is not None and args.target is not None:
            u,v=tuple(args.source),tuple(args.target)
            root=args.root
        else:
            u=None
        result=(dict(square='U -j-> V -r-> U',letters=sorted(square.alphabet),attachments=square.raw)
                if u is None else {k:square.reach(root,u,v,sg,args.limit)
                                  for k,sg in [('raw',False),('surface',True)]})
    else:
        result=checks()
    if args.agda_dir:
        rules=(square.raw if args.machine else compile_machine(
            dict(start='s',halt='h',program={'s':['test',0,'h','s']})))
        agda_example(rules,args.agda_dir)
    print(json.dumps(result))
