"""Positive private and shared 3-rules on two Gray columns, including directed 5-comparisons."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from graphlib import TopologicalSorter
import json
from pathlib import Path

from semistrict_surface_planar_cylinder import moves, parse
from semistrict_surface_planar_tensor import (Column, constraints, degree_five, neighbors, particular,
                                             positive_lift)
from semistrict_surface_square_mutex import diagram


def reading(columns,source,right,trace,anchored):
    starts=[iter(c.inputs) for c in columns]
    wires=[(int(x in right),next(starts[int(x in right)])) for x in source]
    marks=[{},{}]
    fixed=[set(),set()]
    matching={}
    squares=Counter()
    for name,i,l,r in trace:
        if name=='swap':
            (_,f),(_,e)=wires[i:i+2]
            squares[e,f]+=1
            wires[i:i+2]=[(0,e),(1,f)]
            continue
        window=wires[i:i+len(l)]
        present={s for s,e in window}
        occurrences={}
        outputs={}
        for side in sorted(present):
            ins=[e for s,e in window if s==side]
            p,out=columns[side].tile(name,ins,sum((x in right)==side for x in r))
            occurrences[side]=p
            outputs[side]=iter(out)
            prefix=[e for s,e in wires[:i] if s!=side]
            # Joint polygons have one joint boundary; equal dummy terms cancel in the difference.
            marks[side][p]=(columns[1-side].endpoints[prefix[-1]][1] if len(present)==1 and prefix else 0)
            if len(present)==2 or name in anchored:
                fixed[side].add(p)
        if len(present)==2:
            matching[occurrences[0]]=occurrences[1]
        wires[i:i+len(l)]=[(int(x in right),next(outputs[int(x in right)])) for x in r]
    return (tuple(wires),marks,squares),fixed,matching


def basis_order(column,tiles,reverse):
    graph=TopologicalSorter()
    edges=set(column.inputs)
    for p in tiles:
        l,r=column.polygons[p]
        edges.update(r)
        before,after=(r,l) if reverse else (l,r)
        graph.add(('p',p),*(('e',e) for e in before))
        for e in after:
            graph.add(('e',e),('p',p))
    for e in edges:
        u,v=column.endpoints[e]
        graph.add(('e',e),('v',u))
        graph.add(('v',v),('e',e))
    return {v:i for i,v in enumerate(graph.static_order())}


def problem(source,right,traces,anchored):
    cols=[Column(sum((x in right)==s for x in source)) for s in (0,1)]
    (a,fixed,m),(b,other,n)=[reading(cols,source,right,path,anchored) for path in traces]
    if (a[0]!=b[0] or fixed!=other or m!=n
            or any(a[1][i].keys()!=b[1][i].keys() for i in (0,1))
            or any(a[1][s][p]!=b[1][s][p] for s in (0,1) for p in fixed[s])):
        return None
    z=particular(cols,a,b)
    cond=constraints(cols,a[1],z)
    return (cols,a[1],z,cond),a,b,fixed


def stationary(key,fixed):
    side,e,f=key
    return e in fixed[0] if side==0 else f in fixed[1]


def solution(data):
    base,a,b,fixed=data
    cond=base[-1]
    upper=[(key,v,u,-slack) for key,u,v,slack in cond if stationary(key,fixed)]
    sol=positive_lift(cond+upper)
    if sol is not None:
        assert all(not stationary(key,fixed) for key in sol)
    return sol


def replay(data,z,blocks=()):
    (cols,tiles,_,_),a,b,fixed=data
    marks=[dict(x) for x in a[1]]
    squares=Counter(a[2])
    orders=[basis_order(cols[i],tiles[i],i==1) for i in (0,1)]
    todo=Counter(z)
    items=[]
    def priority(p,x,q,y):
        return orders[0][p,x],orders[1][q,y]
    for p,q in blocks:
        assert p not in fixed[0] and q not in fixed[1]
        ins,_=cols[0].polygons[p]
        inp,_=cols[1].polygons[q]
        for e in ins:
            todo[1,e,q]-=1
        for f in inp:
            todo[0,p,f]-=1
        items.append((priority('p',p,'p',q),2,p,q))
    for (k,e,f),n in todo.items():
        assert n>=0
        if n:
            assert n==1 and not stationary((k,e,f),fixed)
            order=priority('p' if k==0 else 'e',e,'e' if k==0 else 'p',f)
            items.append((order,k,e,f))
    schedule=[]
    def advance(side,p,edges):
        pos=marks[side][p]
        for e in edges:
            u,v=cols[1-side].endpoints[e]
            assert pos==u
            pos=v
        marks[side][p]=pos
    for _,k,e,f in sorted(items):
        if k==0:
            ins,out=cols[0].polygons[e]
            consume=[(i,f) for i in ins]
            produce=[(i,f) for i in out]
            advance(0,e,[f])
        elif k==1:
            ins,out=cols[1].polygons[f]
            consume=[(e,j) for j in out]
            produce=[(e,j) for j in ins]
            advance(1,f,[e])
        else:
            li,lo=cols[0].polygons[e]
            ri,ro=cols[1].polygons[f]
            consume=[(i,j) for i in li for j in ro]
            produce=[(i,j) for i in lo for j in ri]
            advance(0,e,ri)
            advance(1,f,li)
        assert all(squares[key]==1 for key in consume)
        squares.subtract(consume)
        assert all(squares[key]==0 for key in produce)
        squares.update(produce)
        schedule.append((k,e,f))
    assert marks==b[1] and +squares==+b[2]
    return schedule


def compare_five(data,first,second):
    base,_,_,fixed=data
    if any(stationary(k,fixed) and n for cell in (first,second) for k,n in cell.items()):
        raise ValueError('a shared or anchored polygon cannot supply a native prism')
    cert=degree_five(base,first,second)
    if cert is None:
        return None
    cols=base[0]
    z=Counter(first)
    schedule=[]
    for (p,q),n in sorted(cert.items()):
        assert p not in fixed[0] and q not in fixed[1]
        for _ in range(n):
            replay(data,z,[(p,q)])
            for i,tiles in enumerate((cols[0].polygons[p],cols[1].polygons[q])):
                for sign,edges in zip((-1,1),tiles):
                    for e in edges:
                        key=(1,e,q) if i==0 else (0,p,e)
                        z[key]+=sign
            schedule.append((p,q))
    assert +z==+Counter(second)
    return schedule


def exhaustive(source,rules,right,budget,anchored=()):
    ids={}
    groups=defaultdict(dict)
    edges=defaultdict(set)
    queue=[(source,[],0)]
    readings=pairs=0
    while queue:
        w,path,n=queue.pop()
        u=diagram(source,path,False,ids)
        groups[w][u]=path
        readings+=1
        before=source
        for k,(_,i,l,r) in enumerate(path):
            for other in neighbors(before,path,k,right):
                # Only an unchanged private rule can furnish the central polygon.
                index=k
                while other[index][0]=='swap':
                    index+=1
                name,_,ins,_=other[index]
                if name in anchored or len({x in right for x in ins})>1:
                    continue
                edges[u].add(diagram(source,other,False,ids))
            before=before[:i]+r+before[i+len(l):]
        for name,i,l,r,out in moves(w,rules,right):
            count=n+(name!='swap')
            if count<=budget:
                queue.append((out,path+[(name,i,l,r)],count))
    for group in groups.values():
        for u,first in group.items():
            reached={u}
            todo=[u]
            while todo:
                for v in edges[todo.pop()]-reached:
                    reached.add(v)
                    todo.append(v)
            for v,second in group.items():
                data=problem(source,right,(first,second),anchored)
                z=None if data is None else solution(data)
                assert (z is not None)==(v in reached),(first,second,z)
                if z is not None:
                    replay(data,z)
                pairs+=1
    return readings,pairs


def block_checks():
    from itertools import product
    count=0
    for m,n,i,j in product(range(1,3),repeat=4):
        # Two independent rectangles, each lying just after a shared backward return.
        source_one=('a','B')
        rules=[('gate',source_one,('M',)*i+('u',)*m),
               ('p',('u',)*m,('x',)*n),('q',('M',)*i,('N',)*j)]
        right={'B','M','N'}
        def local(first,last):
            w=source_one
            result=[]
            for name in ('gate',first,'swap',last):
                while True:
                    choice=next((s for s in moves(w,rules,right) if s[0]==name),None)
                    if choice is None:
                        break
                    result.append(choice[:4])
                    w=choice[-1]
                    if name!='swap':
                        break
            return result,w
        def twice(first,last):
            path,w=local(first,last)
            return path+[(a,k+len(w),l,r) for a,k,l,r in path]
        data=problem(source_one*2,right,(twice('q','p'),twice('p','q')),set())
        base,_,_,fixed=data
        left,right_column=base[0]
        pairs=list(zip(sorted(set(base[1][0])-fixed[0]),sorted(set(base[1][1])-fixed[1])))
        assert len(pairs)==2
        lower={}
        upper={}
        for p,q in pairs:
            li,lo=left.polygons[p]
            ri,ro=right_column.polygons[q]
            lower.update({(0,p,f):1 for f in ri}|{(1,e,q):1 for e in li})
            upper.update({(0,p,f):1 for f in ro}|{(1,e,q):1 for e in lo})
        replay(data,lower,blocks=pairs)
        assert compare_five(data,lower,upper)==pairs
        assert compare_five(data,upper,lower) is None
        mid=Counter(lower)
        p,q=pairs[1]
        for sign,edges in zip((-1,1),left.polygons[p]):
            mid.update({(1,e,q):sign for e in edges})
        for sign,edges in zip((-1,1),right_column.polygons[q]):
            mid.update({(0,p,f):sign for f in edges})
        assert compare_five(data,lower,mid)==[pairs[1]]
        assert compare_five(data,mid,upper)==[pairs[0]]
        count+=1
    return count


def checks():
    cases=[('Ba',[('p','a','xy'),('q','B','MN'),('return','aB','Ba')],3,()),
           ('Ba',[('p','a','xy'),('q','B','MN'),('gate','Ba','xMyN'),('close','yN','Na')],4,()),
           ('Baa',[('p','a','a'),('q','B','B'),('pin','aB','Ba')],3,()),
           ('BaB',[('p','a','a'),('q','B','B'),('lock','B','B'),('jump','aB','BBa')],3,('lock',))]
    totals=[0,0]
    for w,r,b,fixed in cases:
        results=exhaustive(tuple(w),[(name,tuple(l),tuple(r)) for name,l,r in r],set('BMN'),b,fixed)
        totals=[u+v for u,v in zip(totals,results)]
    return dict(zip(('readings','ordered_comparisons'),totals),joint_block_diamonds=block_checks())


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    parser.add_argument('--agda-dir',type=Path)
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        source,right=tuple(q['source']),set(q['right_letters'])
        rules=[(n,tuple(l),tuple(r)) for n,(l,r) in q['rules'].items()]
        if any(n=='swap' or not l or not r or {x in right for x in l}!={x in right for x in r}
               for n,l,r in rules):
            raise ValueError('each column present on either side must be present on both')
        fixed=set(q.get('anchored',[]))
        if not fixed<={n for n,l,r in rules if len({x in right for x in l})==1}:
            raise ValueError('expected private-shaped long rules in anchored')
        dest,u=parse(source,rules,right,q['first'])
        dest2,v=parse(source,rules,right,q['second'])
        if dest!=dest2:
            raise ValueError('expected parallel readings')
        data=problem(source,right,(u,v),fixed)
        if 'prism_faces' in q:
            if data is None:
                raise ValueError('expected compatible projected faces')
            cells=[{(k,e,f):n for k,e,f,n in face} for face in q['prism_faces']]
            schedule=compare_five(data,*cells)
        else:
            z=None if data is None else solution(data)
            schedule=None if z is None else replay(data,z)
        result=dict(raw=schedule is not None,surface=schedule is not None,schedule=schedule)
    else:
        result=checks()
    if args.agda_dir:
        from semistrict_surface_shared_columns import agda_example
        agda_example(args.agda_dir,right_private=True)
    print(json.dumps(result))
