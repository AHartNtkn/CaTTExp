"""Positive commuting unary loops with raw returns for every mixed prism.

At the Gray point, colours maps scalar names to their lists of unary 3-loops.
Both unary commutations and both mixed-prism directions are supplied as finite
raw 4-comparisons. A face pair is [input_colours, left, right]. Each side is
[positive_crossing_word, rows_of_nonnegative_counts_on_input_occurrences].
--presentation FILE decides all old 4-types, or both judgments if query exists.
--nets emits Petri reachability instances; --encode-net FILE gives the reverse
reduction from {source,target,transitions}, with consumption/production pairs.
"""
from argparse import ArgumentParser
from collections import deque
from itertools import permutations, product
import json
from pathlib import Path

import islpy as isl

from semistrict_surface_joint_labels import positive_normal
from semistrict_surface_scalar_sites import coefficients


def succ(x,a,b):
    if any(i<j for i,j in zip(x,a)):
        return None
    return tuple(i-j+k for i,j,k in zip(x,a,b))


def decode_list(n):
    out=[]
    while n:
        k=(n & -n).bit_length()-1
        out.append(k)
        n >>= k+1
    return out


def linear_union(code,d,names):
    pieces=[]
    for i in decode_list(code):
        data=decode_list(i)
        if not data or len(data)%d:
            return None
        periods=[data[j:j+d] for j in range(d,len(data),d)]
        ks=[f'k{j}' for j in range(len(periods))]
        eqs=[]
        for j,x in enumerate(names):
            terms=[str(data[j])]+[f'{v[j]}*{k}' for v,k in zip(periods,ks) if v[j]]
            eqs.append(x+'='+'+'.join(terms))
        clause=' and '.join(eqs+[k+'>=0' for k in ks])
        pieces.append('(exists '+','.join(ks)+': '+clause+')' if ks else '('+clause+')')
    if not pieces:
        return None
    return isl.Set('{ ['+','.join(names)+'] : '+' or '.join(pieces)+' }')


def reachable(net):
    start,end=map(tuple,(net['source'],net['target']))
    edges=[(tuple(a),tuple(b)) for a,b in net['transitions']]
    if start==end:
        return True
    change=tuple(y-x for x,y in zip(start,end))
    if coefficients([tuple(y-x for x,y in zip(a,b)) for a,b in edges],change) is None:
        return False
    names=[f'x{i}' for i in range(len(start))]
    def point(v):
        return isl.Set('{ ['+','.join(map(str,v))+'] }')
    def relation(a,b):
        ins=','.join(names)
        outs=','.join(f'{x}+({v-u})' for x,u,v in zip(names,a,b))
        guard=' and '.join(f'{x}>={u}' for x,u in zip(names,a))
        return isl.Map('{ ['+ins+'] -> ['+outs+'] : '+guard+' }')
    rels=[relation(a,b) for a,b in edges]
    s,t=point(start),point(end)
    def separates(inv):
        return (s.is_subset(inv) and t.is_disjoint(inv) and
                all(inv.apply(rel).is_subset(inv) for rel in rels))
    orthant=' and '.join(f'{x}>=0' for x in names)
    for i,(u,v) in enumerate(zip(start,end)):
        if u!=v:
            op='<=' if u<v else '>='
            bounds=orthant+' and '+names[i]+op+str(u)
            if separates(isl.Set('{ ['+','.join(names)+'] : '+bounds+' }')):
                return False
    forwards,backwards={start},{end}
    fq,bq=deque([start]),deque([end])
    code=0
    while fq and bq:
        for queue,seen,other,moves in ((fq,forwards,backwards,edges),(bq,backwards,forwards,((b,a) for a,b in edges))):
            x=queue.popleft()
            for a,b in moves:
                y=succ(x,a,b)
                if y in other:
                    return True
                if y is not None and y not in seen:
                    seen.add(y)
                    queue.append(y)
        # Fairly interleave both searches with Leroux's complete enumeration
        # of semilinear separating invariants, one finite code per iteration.
        code+=1
        inv=linear_union(code,len(start),names)
        if inv is not None and separates(inv):
            return False
    return False


def reorder(n,w):
    p=list(range(n))
    for g in w:
        if not 1<=g<n:
            raise ValueError('crossing outside the history')
        p[g-1],p[g]=p[g],p[g-1]
    return tuple(p)


class Pair:
    def __init__(self,entry,colours):
        h,left,right=entry
        self.h=tuple(h)
        self.cross,self.rows=[],[]
        for word,counts in (left,right):
            reorder(len(h),word)
            if len(counts)!=len(h) or any(len(v)!=len(colours[c]) or any(type(k)!=int or k<0 for k in v)
                                         for c,v in zip(h,counts)):
                raise ValueError('invalid positive label tuple')
            self.cross.append(tuple(word))
            self.rows.append(tuple(map(tuple,counts)))
        if any(tuple(h[i] for i in reorder(len(h),w))!=tuple(h[i] for i in reorder(len(h),self.cross[0]))
               for w in self.cross[1:]):
            raise ValueError('nonparallel colour histories')


class Positive:
    def __init__(self,data):
        self.colours=data['colours']
        labs=[x for cs in self.colours.values() for x in cs]
        if len(set(labs))!=len(labs):
            raise ValueError('expected distinct unary generators')
        self.rules=[Pair(r,self.colours) for r in data['attachments']]
        for r in self.rules:
            if positive_normal(len(r.h),r.cross[0])!=positive_normal(len(r.h),r.cross[1]):
                raise ValueError('attachment changes its structural braid')

    def empty(self,h):
        return tuple((0,)*len(self.colours[c]) for c in h)

    def place(self,h,positions,rows):
        v=list(self.empty(h))
        for i,row in zip(positions,rows):
            v[i]=row
        return tuple(x for row in v for x in row)

    def net(self,q,signed):
        h=q.h
        inputs=tuple(range(len(h)))
        a,b=q.cross
        initial,final=(self.place(h,inputs,v) for v in q.rows)
        if positive_normal(len(h),a)!=positive_normal(len(h),b):
            return dict(source=(1,),target=(0,),transitions=[])
        if signed:
            transitions=set()
            for r in self.rules:
                for p in permutations(inputs,len(r.h)):
                    if tuple(h[i] for i in p)==r.h:
                        transitions.add(tuple(self.place(h,p,rows) for rows in r.rows))
            return dict(source=initial,target=final,transitions=sorted(transitions))
        words,ids,edges=[a],{a:0},set()
        zero=(0,)*len(initial)
        for i,w in enumerate(words):
            def edge(new,x,y):
                if new not in ids:
                    ids[new]=len(words)
                    words.append(new)
                edges.add((i,ids[new],x,y))
            loc=list(inputs)
            for j in range(len(w)+1):
                for r in self.rules:
                    for k in range(len(h)-len(r.h)+1):
                        p=loc[k:k+len(r.h)]
                        if tuple(h[e] for e in p)!=r.h:
                            continue
                        l,t=(tuple(k+g for g in path) for path in r.cross)
                        if w[j:j+len(l)]==l:
                            edge(w[:j]+t+w[j+len(l):],*(self.place(h,p,v) for v in r.rows))
                if j==len(w):
                    break
                g=w[j]
                if j+1<len(w) and abs(g-w[j+1])>=2:
                    edge(w[:j]+(w[j+1],g)+w[j+2:],zero,zero)
                if w[j:j+3]==(g,g+1,g):
                    edge(w[:j]+(g+1,g,g+1)+w[j+3:],zero,zero)
                loc[g-1],loc[g]=loc[g],loc[g-1]
        if b not in ids:
            return dict(source=(1,),target=(0,),transitions=[])
        def state(i):
            return tuple(int(j==i) for j in range(len(words)))
        return dict(source=state(0)+initial,target=state(ids[b])+final,
                    transitions=[(state(i)+x,state(j)+y) for i,j,x,y in sorted(edges)])

    def obligations(self):
        def at_zero(h,x,y):
            return [h,[[],x],[[],y]]
        for r in self.rules:
            x,y=r.rows
            if r.cross[0]:
                yield at_zero(r.h,x,y)
                continue
            if not r.h or x==y:
                continue
            tests=[(r.h,x,y,j) for j in range(len(r.h)-1)]
            for c in self.colours:
                z=self.empty((c,))
                tests.extend([((c,)+r.h,z+x,z+y,0),(r.h+(c,),x+z,y+z,len(r.h)-1)])
            for h,u,v,j in tests:
                p=reorder(len(h),(j+1,))
                yield at_zero(tuple(h[i] for i in p),tuple(u[i] for i in p),tuple(v[i] for i in p))
        for h in product(self.colours,repeat=3):
            zeros=self.empty(h)
            yield [h,[(2,1,2),zeros],[(1,2,1),zeros]]

    def all(self):
        count=0
        for entry in self.obligations():
            count+=1
            if not reachable(self.net(Pair(entry,self.colours),False)):
                return dict(reflects=False,witness=entry,checks=count)
        return dict(reflects=True,checks=count)


def encode(net):
    a,b=net['source'],net['target']
    n=len(a)
    colours={'s':[f'p{i}' for i in range(n)]}
    empty=[0]*n
    def rule(h,l,rows,r,other):
        return [['s']*h,[l,rows],[r,other]]
    extra=[rule(1,[],[u],[],[v]) for u,v in net['transitions']]
    extra.extend([rule(3,[2,1,2],[empty]*3,[1,2,1],[empty]*3),
                  rule(2,[1],[a,empty],[1],[b,empty])])
    return dict(colours=colours,attachments=extra,query=rule(2,[],[a,empty],[],[b,empty]))


def combine(nets):
    """Disjoint place blocks make one reachability query express a conjunction."""
    nets=list(nets)
    start=tuple(x for net in nets for x in net['source'])
    end=tuple(x for net in nets for x in net['target'])
    edges=[]
    offset=0
    for net in nets:
        width=len(net['source'])
        pre=(0,)*offset
        post=(0,)*(len(start)-offset-width)
        edges.extend((pre+tuple(a)+post,pre+tuple(b)+post) for a,b in net['transitions'])
        offset+=width
    return dict(source=start,target=end,transitions=edges)


def validate(net):
    size=len(net['source'])
    def marking(row):
        if len(row)!=size or any(type(k)!=int or k<0 for k in row):
            raise ValueError('invalid Petri marking or arc')
    marking(net['source'])
    marking(net['target'])
    for take,give in net['transitions']:
        marking(take)
        marking(give)


def self_check():
    from random import Random
    rng=Random(175)

    def literal(net):
        start=tuple(net['source'])
        seen={start}
        queue=deque([start])
        while queue:
            x=queue.popleft()
            for a,b in net['transitions']:
                y=succ(x,a,b)
                if y is not None and y not in seen:
                    seen.add(y)
                    queue.append(y)
        return tuple(net['target']) in seen

    samples=0
    answers=set()
    for d in (2,3):
        markings=[m for m in product(range(4),repeat=d) if sum(m)==3]
        for _ in range(24):
            s,t=rng.sample(markings,2)
            edges=[]
            for _ in range(4):
                weight=rng.choice((1,2,3))
                arcs=[m for m in product(range(weight+1),repeat=d) if sum(m)==weight]
                edges.append((rng.choice(arcs),rng.choice(arcs)))
            net=dict(source=s,target=t,transitions=edges)
            expected=literal(net)
            data=encode(net)
            model=Positive(data)
            q=Pair(data['query'],model.colours)
            assert reachable(net)==reachable(model.net(q,False))==model.all()['reflects']==expected
            assert reachable(model.net(q,True))
            answers.add(expected)
            samples+=1
    assert len(answers)==2
    net=dict(source=[1,0],target=[0,1],transitions=[([1,1],[0,2])])
    data=encode(net)
    model=Positive(data)
    assert not reachable(net) and not model.all()['reflects']
    assert reachable(model.net(Pair(data['query'],model.colours),True))
    configs=0
    for create,consume in product((False,True),repeat=2):
        z,o=[[0]],[[1]]
        decorated=o+z+z
        rules=[[['s']*3,[[2,1,2],decorated],[[1,2,1],decorated]]]
        for enabled,source,target in ((create,z,o),(consume,o,z)):
            if enabled:
                rules.append([['s'],[[],source],[[],target]])
        m=Positive(dict(colours={'s':['p']},attachments=rules))
        assert m.all()['reflects']==(create and consume)
        nets=[m.net(Pair(r,m.colours),False) for r in m.obligations()]
        assert reachable(combine(nets))==(create and consume)
        configs+=1
    # The coordinate half-space z=0 separates these unbounded searches.
    assert not reachable(dict(source=[0,1],target=[1,1],transitions=[
        ([1,0],[2,0]),([0,1],[0,2]),([0,2],[0,1])]))
    model=Positive(dict(colours={'a':['p'],'b':['q','r']},attachments=[
        [['b','a'],[[],[[0,1],[2]]],[[],[[1,0],[0]]]]]))
    for word in ([],[1]):
        q=Pair([['a','b'],[word,[[2],[0,1]]],[word,[[0],[1,0]]]],model.colours)
        assert reachable(model.net(q,True))
        assert reachable(model.net(q,False))==bool(word)
    return dict(bounded_net_encodings=samples,cube_bootstrap_configurations=configs,
                catalytic_obstruction=True,unbounded_separator=True,colour_transport_queries=2)


def main():
    parser=ArgumentParser(description=__doc__)
    action=parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--presentation',type=Path)
    action.add_argument('--encode-net',type=Path)
    action.add_argument('--self-check',action='store_true')
    parser.add_argument('--nets',action='store_true')
    parser.add_argument('--global',dest='all_types',action='store_true')
    args=parser.parse_args()
    if args.self_check:
        result=self_check()
    elif args.encode_net:
        net=json.loads(args.encode_net.read_text())
        validate(net)
        result=encode(net)
    else:
        data=json.loads(args.presentation.read_text())
        model=Positive(data)
        if args.all_types or 'query' not in data:
            result=(combine(model.net(Pair(r,model.colours),False) for r in model.obligations())
                    if args.nets else model.all())
        else:
            q=Pair(data['query'],model.colours)
            jobs={name:model.net(q,signed) for name,signed in [('raw',False),('surface',True)]}
            result=jobs if args.nets else {name:reachable(job) for name,job in jobs.items()}
    print(json.dumps(result))


if __name__=='__main__':
    main()
