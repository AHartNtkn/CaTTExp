"""Decide positive two-column Gray comparisons by signed chains and difference constraints."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
import json
from pathlib import Path

from semistrict_surface_square_machine import steps
from semistrict_surface_square_mutex import diagram
from semistrict_surface_planar_cylinder import negative_to_positive


class Column:
    def __init__(self,n):
        self.endpoints={i:(i,i+1) for i in range(n)}
        self.inputs=tuple(range(n))
        self.vertices=n+1
        self.by_input={}
        self.polygons=[]

    def tile(self,name,inputs,size):
        key=(name,tuple(inputs))
        if key in self.by_input:
            return self.by_input[key]
        p=len(self.polygons)
        head,tail=self.endpoints[inputs[0]][0],self.endpoints[inputs[-1]][1]
        assert all(self.endpoints[a][1]==self.endpoints[b][0] for a,b in zip(inputs,inputs[1:]))
        mids=list(range(self.vertices,self.vertices+size-1))
        self.vertices+=size-1
        path=[head,*mids,tail]
        outputs=tuple(range(len(self.endpoints),len(self.endpoints)+size))
        for e,u,v in zip(outputs,path,path[1:]):
            self.endpoints[e]=(u,v)
        self.polygons.append((tuple(inputs),outputs))
        self.by_input[key]=p,outputs
        return p,outputs

    def parents(self,used):
        creator={}
        consumer={}
        for p in used:
            left,right=self.polygons[p]
            creator.update((e,p) for e in right)
            consumer.update((e,p) for e in left)
        return creator,consumer

    def tree_path(self,source,target,tiles):
        excluded={self.polygons[p][1][-1] for p in tiles}
        edges=set(self.inputs)
        for p in tiles:
            edges.update(self.polygons[p][1])
        graph=defaultdict(list)
        for e in sorted(edges-excluded):
            a,b=self.endpoints[e]
            graph[a].append((b,e,1))
            graph[b].append((a,e,-1))
        previous={source:None}
        todo=[source]
        while target not in previous:
            current=todo.pop()
            for v,e,sign in graph[current]:
                if v not in previous:
                    previous[v]=(current,e,sign)
                    todo.append(v)
        result={}
        while target!=source:
            parent,e,sign=previous[target]
            result[e]=sign
            target=parent
        return result

    def fill_cycle(self,chain,tiles):
        residual=Counter(chain)
        result={}
        for p in sorted(tiles,reverse=True):
            left,right=self.polygons[p]
            n=residual[right[-1]]
            if n:
                result[p]=n
                for e in left:
                    residual[e]+=n
                for e in right:
                    residual[e]-=n
        if any(residual.values()):
            raise ValueError('expected a cycle in the unfolded column')
        return result


def moves(w,rules,right):
    for i,(a,b) in enumerate(zip(w,w[1:])):
        if a in right and b not in right:
            yield 'swap',i,(a,b),(b,a),w[:i]+(b,a)+w[i+2:]
    yield from steps(w,rules)


def parse(source,rules,right,trace):
    w=source
    result=[]
    for name,pos in trace:
        movement=next((s for s in moves(w,rules,right) if s[:2]==(name,pos)),None)
        if movement is None:
            raise ValueError(f'{name} at {pos} is unavailable in {w}')
        *s,w=movement
        result.append(tuple(s))
    return result


def unfold(columns,source,right,trace):
    inputs=[iter(c.inputs) for c in columns]
    w=[(int(a in right),next(inputs[int(a in right)])) for a in source]
    positions=[{},{}]
    squares=Counter()
    for name,i,l,r in trace:
        if name=='swap':
            (_,f),(_,e)=w[i:i+2]
            w[i:i+2]=[(0,e),(1,f)]
            squares[e,f]+=1
        else:
            side=int(l[0] in right)
            previous=[e for s,e in w[:i] if s!=side]
            pos=columns[1-side].endpoints[previous[-1]][1] if previous else 0
            redex=w[i:i+len(l)]
            assert all(s==side for s,e in redex)
            p,new=columns[side].tile(name,[e for s,e in redex],len(r))
            positions[side][p]=pos
            w[i:i+len(l)]=[(side,e) for e in new]
    return tuple(w),positions,squares


def particular(columns,first,second):
    _,a,s=first
    _,b,t=second
    left,right=columns
    ptiles,qtiles=a
    z={}
    residual=Counter(t)
    residual.subtract(s)
    for p in ptiles:
        before,after=left.polygons[p]
        for f,n in right.tree_path(a[0][p],b[0][p],qtiles).items():
            z[0,p,f]=n
            for e in before:
                residual[e,f]+=n
            for e in after:
                residual[e,f]-=n
    for q in qtiles:
        before,after=right.polygons[q]
        for e,n in left.tree_path(a[1][q],b[1][q],ptiles).items():
            z[1,e,q]=n
            for f in before:
                residual[e,f]-=n
            for f in after:
                residual[e,f]+=n
    rows=defaultdict(dict)
    for (e,f),n in residual.items():
        if n:
            rows[e][f]=n
    for e,row in rows.items():
        for q,n in right.fill_cycle(row,qtiles).items():
            z[1,e,q]=z.get((1,e,q),0)-n
    return z


def constraints(columns,tiles,z):
    result=[]
    for side,column in enumerate(columns):
        born,spent=column.parents(tiles[side])
        edges=set(column.inputs)|set(born)
        for opposite in tiles[1-side]:
            def index(event):
                if event is None:
                    return None
                return (event,opposite) if side==0 else (opposite,event)
            for e in edges:
                key=(1,e,opposite) if side==0 else (0,opposite,e)
                result.append((key,index(born.get(e)),index(spent.get(e)),z.get(key,0)))
    return result


def positive_lift(conditions):
    potential={v:0 for _,a,b,_ in conditions for v in (a,b)}
    for _ in range(len(potential)):
        changed=False
        for _,a,b,slack in conditions:
            upper=potential[a]+slack
            if potential[b]>upper:
                potential[b]=upper
                changed=True
        if not changed:
            break
    else:
        if potential:
            return None
    return {key:slack+potential[a]-potential[b] for key,a,b,slack in conditions
            if slack+potential[a]-potential[b]}


def comparison_data(source,right,trace1,trace2):
    columns=[Column(sum((a in right)==side for a in source)) for side in (0,1)]
    a,b=[unfold(columns,source,right,tr) for tr in (trace1,trace2)]
    if a[0]!=b[0] or any(m.keys()!=n.keys() for m,n in zip(a[1],b[1])):
        return None
    z=particular(columns,a,b)
    conditions=constraints(columns,a[1],z)
    return columns,a[1],z,conditions


def query(source,right,trace1,trace2):
    data=comparison_data(source,right,trace1,trace2)
    return None if data is None else positive_lift(data[-1])


def degree_five(data,first,second):
    if data is None:
        raise ValueError('the two readings must project to identical column diagrams')
    columns,tiles,z,conditions=data
    def coordinates(cell):
        if any(n<0 or type(n)!=int for n in cell.values()):
            raise ValueError('a positive prism chain is required')
        params={None:0}
        for p in tiles[0]:
            row={}
            for key,_,_,_ in conditions:
                side,event,wire=key
                if side==0 and event==p:
                    row[wire]=cell.get(key,0)-z.get(key,0)
            params.update(((p,q),x) for q,x in columns[1].fill_cycle(row,tiles[1]).items())
        expected={key:base+params.get(u,0)-params.get(v,0) for key,u,v,base in conditions}
        if {k:n for k,n in expected.items() if n}!={k:n for k,n in cell.items() if n}:
            raise ValueError('the prism chain does not have the specified boundary')
        return params
    a,b=coordinates(first),coordinates(second)
    result={k:b.get(k,0)-a.get(k,0) for k in a.keys()|b.keys() if k is not None}
    return None if any(v<0 for v in result.values()) else {k:n for k,n in result.items() if n}


def neighbors(w,path,k,right):
    yield from negative_to_positive(w,path,k)
    name,i,l,r=path[k]
    if name=='swap' or l[0] not in right or i+len(l)>=len(w):
        return
    a=w[i+len(l)]
    if a in right:
        return
    # A right polygon acts before the left event, then its outputs cross it.
    required=[('swap',i+h,(r[h],a),(a,r[h])) for h in reversed(range(len(r)))]
    if path[k+1:k+1+len(r)]!=required:
        return
    swaps=[('swap',i+h,(l[h],a),(a,l[h])) for h in reversed(range(len(l)))]
    yield path[:k]+swaps+[(name,i+1,l,r)]+path[k+1+len(r):]


def exhaustive(source,rules,right,budget):
    groups=defaultdict(dict)
    edges=defaultdict(set)
    ids={}
    total=0
    todo=[(source,[],0)]
    while todo:
        w,path,n=todo.pop()
        key=diagram(source,path,False,ids)
        groups[w][key]=path
        total+=1
        prev=source
        for k,(_,i,l,r) in enumerate(path):
            for other in neighbors(prev,path,k,right):
                edges[key].add(diagram(source,other,False,ids))
            prev=prev[:i]+r+prev[i+len(l):]
        for name,i,l,r,out in moves(w,rules,right):
            m=n+(name!='swap')
            if m<=budget:
                todo.append((out,path+[(name,i,l,r)],m))
    pairs=0
    for group in groups.values():
        for key,first in group.items():
            reached={key}
            queue=[key]
            while queue:
                for nxt in edges[queue.pop()]-reached:
                    reached.add(nxt)
                    queue.append(nxt)
            for target,second in group.items():
                cert=query(source,right,first,second)
                assert (cert is not None)==(target in reached),(source,first,second,cert)
                pairs+=1
    return total,pairs


def checks():
    cases=[('Ba',[('p','a','xy'),('q','B','MN')],2),
           ('Ba',[('p','a','xy'),('p2','xy','a'),('q','B','MN'),('q2','MN','B')],3),
           ('BBa',[('p','a','xy'),('q','BB','M')],2),
           ('BaB',[('p','a','a'),('q','B','B')],3),
           ('Baa',[('p','aa','xy'),('q','B','MN')],2),
           ('Ba',[('p','a','aa'),('q','B','BB')],4)]
    totals=[0,0]
    for w,rules,budget in cases:
        values=exhaustive(tuple(w),[(n,tuple(l),tuple(r)) for n,l,r in rules],set('BMN'),budget)
        totals=[a+b for a,b in zip(totals,values)]
    from itertools import product
    atoms=0
    for m,n,i,j in product(range(1,5),repeat=4):
        rules=[('p',('a',)*m,('x',)*n),('q',('B',)*i,('M',)*j)]
        right={'B','M'}
        source=('B',)*i+('a',)*m
        def extremal(first,last):
            w=source
            trace=[]
            for name in (first,'sort',last):
                while True:
                    step=next((s for s in moves(w,rules,right)
                               if s[0]==('swap' if name=='sort' else name)),None)
                    if step is None:
                        break
                    trace.append(step[:4])
                    w=step[-1]
                    if name!='sort':
                        break
            return trace
        data=comparison_data(source,right,extremal('q','p'),extremal('p','q'))
        lower={(0,0,e):1 for e in range(i)}|{(1,e,0):1 for e in range(m)}
        upper={(0,0,e):1 for e in range(i,i+j)}|{(1,e,0):1 for e in range(m,m+n)}
        assert degree_five(data,lower,upper)=={(0,0):1}
        assert degree_five(data,upper,lower) is None
        assert degree_five(data,lower,lower)=={}
        atoms+=1
    return dict(zip(('raw_readings','ordered_comparisons'),totals),polygon_pairs=atoms)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        source,right=tuple(q['source']),set(q['right_letters'])
        rules=[(n,tuple(l),tuple(r)) for n,(l,r) in q['rules'].items()]
        if any(not l or not r or n=='swap' or len({x in right for x in l+r})!=1 for n,l,r in rules):
            raise ValueError('each rule must have two positive sides in the same column')
        tr=[parse(source,rules,right,q[k]) for k in ('first','second')]
        def finish(path):
            w=source
            for _,i,l,r in path:
                w=w[:i]+r+w[i+len(l):]
            return w
        if finish(tr[0])!=finish(tr[1]):
            raise ValueError('expected parallel old readings')
        data=comparison_data(source,right,*tr)
        if 'prism_faces' in q:
            def chain(items):
                counts=Counter()
                for side,e,f,n in items:
                    counts[side,e,f]+=n
                return counts
            cert=degree_five(data,*map(chain,q['prism_faces']))
            label='polygon_pairs'
        else:
            cert=None if data is None else positive_lift(data[-1])
            label='prisms'
        result=dict(raw=cert is not None,surface=cert is not None)
        result[label]=None if cert is None else [[*k,n] for k,n in sorted(cert.items())]
    else:
        result=checks()
    print(json.dumps(result))
