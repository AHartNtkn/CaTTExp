"""Signed-square reflection at old boundaries of a two-column strong Steiner hom."""
from argparse import ArgumentParser
from collections import defaultdict
from graphlib import CycleError, TopologicalSorter
from itertools import product
import json
from pathlib import Path

from steiner import Complex, ZERO, cells_upto, ch, ch_add, face, top


class BasedHom(Complex):
    """Explicit generator boundaries of a fixed hom, in declaration order."""
    def __init__(self,records):
        self.G=tuple(r[0] for r in records)
        self.deg=[]
        self.dm=[]
        self.dp=[]
        self.index={}
        for name,rank,neg,pos in records:
            if name in self.index or rank<0:
                raise ValueError('invalid generator')
            def chain(side):
                if any(v not in self.index or self.deg[self.index[v]]!=rank-1
                       or type(m)!=int or m<=0 for v,m in side.items()):
                    raise ValueError('invalid signed facet list')
                return ch({self.index[v]:n for v,n in side.items()})
            self.dm.append(chain(neg))
            self.dp.append(chain(pos))
            self.deg.append(rank)
            self.index[name]=len(self.deg)-1
        self.n=max(self.deg,default=0)
        predecessors={i:set() for i in range(len(records))}
        for a,b in self.strong_order():
            predecessors[b].add(a)
        self.order=list(TopologicalSorter(predecessors).static_order())
        if not self.is_unital() or any(self.d(self.d(((x,1),)))!=ZERO for x in self.order):
            raise ValueError('expected an augmented unital chain complex')

    def solve(self,rank,difference):
        rows=[x for x in reversed(self.order) if self.deg[x]==rank-1]
        if any(self.deg[x]!=rank-1 for x,_ in difference):
            raise ValueError('wrong boundary degree')
        priority={x:i for i,x in enumerate(rows)}
        groups=defaultdict(list)
        for x in self.order:
            if self.deg[x]==rank:
                boundary=self.d(((x,1),))
                pivot=min(dict(boundary),key=priority.__getitem__)
                coefficient=dict(boundary)[pivot]
                assert coefficient>0
                groups[pivot].append((x,coefficient,boundary))
        def complete(k,residual,terms):
            if k==len(rows):
                return terms if not residual else None
            row=rows[k]
            def allocate(j,delta,chosen):
                wanted=dict(delta).get(row,0)
                if wanted<0:
                    return None
                if j==len(groups[row]):
                    return complete(k+1,delta,chosen) if wanted==0 else None
                x,c,b=groups[row][j]
                for n in range(wanted//c+1):
                    ans=allocate(j+1,ch_add(delta,b,-n),chosen+(((x,n),) if n else ()))
                    if ans is not None:
                        return ans
                return None
            return allocate(0,residual,terms)
        return complete(0,difference,())


def triangulation():
    records=[]
    def cell(name,rank,before,after):
        records.append((name,rank,{a:1 for a in before},{a:1 for a in after}))
    for u in ('00','10','01','11'):
        cell(u,0,[],[])
    for name,a,b in [('l0','00','10'),('l1','01','11'),('b0','00','01'),('b1','10','11'),
                     ('diag','00','11')]:
        cell(name,1,[a],[b])
    cell('j',2,['b0','l1'],['l0','b1'])
    cell('p',2,['b0','l1'],['diag'])
    cell('q',2,['diag'],['l0','b1'])
    for name in ('z','w'):
        cell(name,3,['p','q'],['j'])
    cell('h',4,['z'],['w'])
    return records


def checks():
    hom=BasedHom(triangulation())
    old=cells_upto(hom,set(hom.order),4)
    crossing=hom.atom(hom.index['j'])
    down,up=face(crossing,'-'),face(crossing,'+')
    def transport(c):
        return top(crossing) if c==down else ZERO
    def normalized_top(c):
        source,target=face(c,'-'),face(c,'+')
        return ch_add(ch_add(top(c),transport(target)),transport(source),-1)
    normalized=0
    for c in old:
        if len(c)==3:
            def norm(v):
                return up if v==down else v
            expected=ch_add(top(norm(face(c,'+'))),top(norm(face(c,'-'))),-1)
            assert hom.d(normalized_top(c))==expected
            normalized+=1
    assert normalized_top(crossing)==ZERO
    queries=0
    for rank in range(1,5):
        lower=[c for c in old if len(c)==rank]
        arrows={(face(c,'-'),face(c,'+')) for c in old if len(c)==rank+1}
        for a,b in product(lower,repeat=2):
            if a[:-1]!=b[:-1]:
                continue
            delta=ch_add(top(b),top(a),-1)
            if rank==3:
                assert delta==ch_add(normalized_top(b),normalized_top(a),-1)
            sol=hom.solve(rank,delta)
            assert (sol is not None)==((a,b) in arrows)
            if sol is not None:
                assert hom.d(sol)==delta
            queries+=1
    try:
        BasedHom(triangulation()+[('return',2,{'l0':1,'b1':1},{'b0':1,'l1':1})])
    except CycleError:
        pass
    else:
        raise AssertionError('a directed return contradicts the strong order')
    return dict(tableaux=len(old),parallel_queries=queries,normalized_diagrams=normalized)


def agda_example(directory):
    from catt import arr, comp2, glue_tree, infer, maximal_vars, src, tgt, tree_ctx, v
    from emit_agda import Emitter
    from semistrict_surface_scalar_cube import exchange
    ctx=tree_ctx(glue_tree(2,0,2))
    j=exchange(ctx,*map(v,maximal_vars(ctx)))
    u,other=src(ctx,j),tgt(ctx,j)
    def declare(ty):
        nonlocal ctx
        name=v(len(ctx))
        ctx+=(ty,)
        return name
    def between(a,b):
        assert infer(ctx,a)==infer(ctx,b)
        return arr(infer(ctx,a),a,b)
    diagonal=declare(infer(ctx,u))
    p=declare(between(u,diagonal))
    q=declare(between(diagonal,other))
    subdivision=comp2(ctx,2,p,q)
    z=declare(between(subdivision,j))
    w=declare(between(subdivision,j))
    h=declare(between(z,w))
    emitter=Emitter()
    g=emitter.ctx(ctx)
    emitter.checks.append(f'triangulated : is-just (checkCtx {g}) ≡ true\ntriangulated = refl\n')
    emitter.check_typed('top',ctx,h)
    module='SteinerSquare'
    source=emitter.module(module,'Named triangulation and comparison of comparisons.').replace(
        'open import CaTTExp.Pure','open import CaTTExp.Gray.Pure')
    (directory/(module+'.agda')).write_text(source)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    parser.add_argument('--agda-dir',type=Path)
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        hom=BasedHom(q['basis'])
        d=ch({hom.index[a]:v for a,v in q['difference'].items()})
        cert=hom.solve(q['local_rank'],d)
        result=dict(chain=None if cert is None else {hom.G[i]:n for i,n in cert})
    else:
        result=checks()
    if args.agda_dir:
        agda_example(args.agda_dir)
    print(json.dumps(result))
