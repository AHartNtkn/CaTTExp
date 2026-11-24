"""Compare two parallel old 3-readings on a positive planar column times a path."""
from argparse import ArgumentParser
from collections import defaultdict
import json
from pathlib import Path

from semistrict_surface_square_machine import steps
from semistrict_surface_square_mutex import diagram


def moves(w,rules,right):
    for i,(a,b) in enumerate(zip(w,w[1:])):
        if a in right and b not in right:
            yield 'swap',i,(a,b),(b,a),w[:i]+(b,a)+w[i+2:]
    yield from steps(w,rules)


def parse(source,rules,right,reading):
    w=source
    trace=[]
    for name,i in reading:
        move=next((s for s in moves(w,rules,right) if s[:2]==(name,i)),None)
        if move is None:
            raise ValueError(f'{name} at {i} does not apply to {w}')
        *step,w=move
        trace.append(tuple(step))
    return w,trace


def marked_diagram(source,trace,right,identifiers):
    w=source
    wires=[(-1,i) for i in range(sum(a not in right for a in w))]
    marks={}
    for name,i,l,r in trace:
        assert w[i:i+len(l)]==l
        if name!='swap':
            prefix=sum(a in right for a in w[:i])
            pos=i-prefix
            key=name,tuple(wires[pos:pos+len(l)])
            vertex=identifiers.setdefault(key,len(identifiers))
            assert vertex not in marks
            marks[vertex]=prefix
            wires[pos:pos+len(l)]=[(vertex,j) for j in range(len(r))]
        w=w[:i]+r+w[i+len(l):]
    return (w,tuple(wires),frozenset(marks)),marks


def compare(source,rules,right,left_trace,right_trace):
    identifiers={}
    left,a=marked_diagram(source,left_trace,right,identifiers)
    target,b=marked_diagram(source,right_trace,right,identifiers)
    if target[0]!=left[0]:
        raise ValueError('the two 3-readings do not have the same final history')
    if left!=target:
        return dict(raw=False,surface=False,same_planar_diagram=False)
    defects=[v for v in a if a[v]>b[v]]
    return dict(raw=not defects,surface=not defects,same_planar_diagram=True,
                right_prefixes=[[v,a[v],b[v]] for v in sorted(a)])


def negative_to_positive(w,trace,k):
    """Exchange one full crossing of the polygon input for its output crossing."""
    if trace[k][0]!='swap':
        return
    _,pos,_,_=trace[k]
    j=k
    while j<len(trace) and trace[j][:2]==('swap',pos+j-k):
        j+=1
    if j>=len(trace):
        return
    rule,i,l,r=trace[j]
    if rule=='swap' or i!=pos or j-k!=len(l):
        return
    b=w[pos]
    assert w[pos+1:pos+1+len(l)]==l
    yield trace[:k]+[(rule,pos+1,l,r)]+[
        ('swap',pos+h,(b,x),(x,b)) for h,x in enumerate(r)
    ]+trace[j+1:]


def exhaustive(source,rules,right,polygon_budget):
    # Enumerate all readings, then identify disjoint rewrites by raw incidence.
    ids,private_ids={},{}
    groups=defaultdict(dict)
    edges=defaultdict(set)
    todo=[(source,[],0)]
    readings=flips=0
    while todo:
        w,path,used=todo.pop()
        vertex=diagram(source,path,False,ids)
        shape,marks=marked_diagram(source,path,right,private_ids)
        groups[shape][vertex]=marks
        readings+=1
        previous=source
        for k,(_,i,l,r) in enumerate(path):
            for alternative in negative_to_positive(previous,path,k):
                other=diagram(source,alternative,False,ids)
                edges[vertex].add(other)
                flips+=1
            previous=previous[:i]+r+previous[i+len(l):]
        for n,i,l,r,out in moves(w,rules,right):
            count=used+(n!='swap')
            if count<=polygon_budget:
                todo.append((out,path+[(n,i,l,r)],count))
    pairs=incomparable=0
    for collection in groups.values():
        for u,marks in collection.items():
            reached={u}
            queue=[u]
            while queue:
                for v in edges[queue.pop()]-reached:
                    reached.add(v)
                    queue.append(v)
            assert reached<=collection.keys()
            for v,other in collection.items():
                test=all(marks[p]<=other[p] for p in marks)
                assert test==(v in reached),(marks,other)
                pairs+=1
                incomparable+=not test and any(marks[p]<other[p] for p in marks)
    return readings,flips,pairs,incomparable


def checks():
    cases=[('Baa',[('split','a','xy'),('merge','xy','a')],2),
           ('BBa',[('split','a','xy'),('merge','xy','a')],3),
           ('BaB',[('split','a','xy'),('change','x','u'),('join','uy','t')],3),
           ('Bab',[('left','a','xm'),('right','b','ny'),('meet','mn','z')],3),
           ('aBzB',[('split','z','zz'),('merge','zz','z')],2),
           ('Baa',[('repeat','a','a')],3)]
    # Vary repeated observer positions across a split, merge and independent changes.
    from itertools import combinations
    for observers in range(4):
        for positions in combinations(range(2+observers),observers):
            base=iter('aa')
            w=''.join('B' if i in positions else next(base) for i in range(2+observers))
            cases.append((w,[('split','a','xy'),('merge','xy','a')],2))
    total=[0]*4
    for source,rules,limit in cases:
        value=exhaustive(tuple(source),[(n,tuple(l),tuple(r)) for n,l,r in rules],{'B'},limit)
        total=[a+b for a,b in zip(total,value)]
    assert total[-1]>0
    return dict(zip(('readings','directed_flips','ordered_pairs','incomparable_pairs'),total))


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    args=parser.parse_args()
    if args.query:
        data=json.loads(args.query.read_text())
        source,right=tuple(data['source']),set(data['right_letters'])
        rules=[(n,tuple(l),tuple(r)) for n,(l,r) in data['rules'].items()]
        if any(not l or not r or n=='swap' or right.intersection(l+r) for n,l,r in rules):
            raise ValueError('expected private positive left rules, with swap reserved')
        _,u=parse(source,rules,right,data['first'])
        _,v=parse(source,rules,right,data['second'])
        result=compare(source,rules,right,u,v)
    else:
        result=checks()
    print(json.dumps(result))
