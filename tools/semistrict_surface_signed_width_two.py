"""Decide degree-four Gray comparisons with positive temporal faces and nonempty spatial inputs."""
from argparse import ArgumentParser
from collections import Counter, deque
import json
from itertools import permutations
from pathlib import Path

from semistrict_surface_return_gaps import Presentation, Rule, exchange_at


class Movies:
    def __init__(self,pres,start):
        self.pres=pres
        self.start=start
        self.patch_ends=[pres.walk(r.path,r.source)[-1] for r in pres.rules]
        # Pure signed transports between histories are unique up to the cube
        # comparisons. Nonempty spatial inputs orient every adjacent exchange.

    def swap(self,h,k):
        if k<0 or k+1>=len(h):
            return None
        native=exchange_at(h,k,self.pres.marks)
        if native is not None:
            return native,True
        (i,a),(j,b)=h[k:k+2]
        source,target=self.pres.marks[a]
        if i+len(target)>j:
            return None
        out=h[:k]+((j+len(source)-len(target),b),(i,a))+h[k+2:]
        assert exchange_at(out,k,self.pres.marks)==h
        return out,False

    def named(self,h,rid,i):
        rule=self.pres.rules[rid]
        if i<0 or i+len(rule.source)>len(h):
            return None
        off=h[i][0]-rule.source[0][0]
        if off<0 or not self.pres.walk(self.start,h[:i])[-1].startswith(rule.path,off):
            return None
        left=tuple((p+off,n) for p,n in rule.source)
        if h[i:i+len(left)]!=left:
            return None
        right=tuple((p+off,n) for p,n in rule.target)
        return h[:i]+right+h[i+len(left):],off

    def parse(self,source,actions):
        h=source
        records=[]
        for name,i in actions:
            if name=='swap':
                out=self.swap(h,i)
                if out is None or not out[1]:
                    raise ValueError('expected a native positive swap')
                h=out[0]
            else:
                if not isinstance(name, int) or not 0 <= name < len(self.pres.rules):
                    raise ValueError('expected a zero-based rule index')
                result=self.named(h,name,i)
                if result is None:
                    raise ValueError('unavailable declared rule')
                records.append((h,name,i))
                h=result[0]
        return tuple(records),h

    def updates(self,state):
        for k,(h,rid,i) in enumerate(state):
            r=self.pres.rules[rid]
            size=len(r.source)
            out,off=self.named(h,rid,i)
            for j in range(len(h)-1):
                if j+2<=i or j>=i+size:
                    sw=self.swap(h,j)
                    if sw is not None:
                        yield state[:k]+((sw[0],rid,i),)+state[k+1:],'disjoint square'
            # Native prism in either spatial order: the polygon moves later in temporal order.
            if i+size<len(h):
                pos,event=h[i+size]
                disjoint=(pos+len(self.pres.marks[event][0])<=off or pos>=off+len(self.patch_ends[rid]))
                if disjoint:
                    new=h
                    for j in reversed(range(i,i+size)):
                        new=self.swap(new,j)[0]
                    assert self.named(new,rid,i+1) is not None
                    yield state[:k]+((new,rid,i+1),)+state[k+1:],'prism'
            if k+1>=len(state):
                continue
            before,second,j=state[k+1]
            if out!=before:
                continue
            other=self.pres.rules[second]
            if j+len(other.source)<=i:
                j0=j
                i1=i+len(other.target)-len(other.source)
            elif j>=i+len(r.target):
                j0=j+size-len(r.target)
                i1=i
            else:
                continue
            after,_=self.named(h,second,j0)
            assert self.named(after,rid,i1)[0]==self.named(before,second,j)[0]
            yield state[:k]+((h,second,j0),(after,rid,i1))+state[k+2:],'disjoint rules'

    def compare(self,source,first,second):
        self.pres.walk(self.start,source)
        u,a=self.parse(source,first)
        v,b=self.parse(source,second)
        if a!=b:
            raise ValueError('expected parallel old readings')
        if Counter(r for _,r,_ in u)!=Counter(r for _,r,_ in v):
            return dict(surface=False,states=0)
        previous={u:None}
        queue=deque([u])
        while queue:
            current=queue.popleft()
            if current==v:
                labels=[]
                while previous[current] is not None:
                    current,label=previous[current]
                    labels.append(label)
                return dict(surface=True,states=len(previous),moves=labels[::-1])
            for nxt,label in self.updates(current):
                if nxt not in previous:
                    previous[nxt]=current,label
                    queue.append(nxt)
        return dict(surface=False,states=len(previous))


def wider_checks():
    # With a single polygon in a fixed window, a disjoint spectator can move
    # from after to before it. A spectator inside its window cannot pass it.
    # This subset order provides an oracle independent of diagram search.
    path = 'fghi'
    edges = {e: (i,i+1) for i,e in enumerate(path)}
    marks = {e: (e,e) for e in path}
    marks.update(x=('g','g'), y=('g','g'))
    histories = tuple(permutations(tuple(enumerate(path))))
    initial = histories[-1]

    def sorting_steps(word):
        steps = []
        word = list(word)
        while any(a[0] > b[0] for a,b in zip(word,word[1:])):
            k = next(i for i,(a,b) in enumerate(zip(word,word[1:])) if a[0] > b[0])
            word[k:k+2] = reversed(word[k:k+2])
            steps.append(('swap',k))
        return steps

    comparisons = 0
    for left,right in [(1,2),(0,2),(1,4),(0,4)]:
        offset = 1-left
        rule = Rule(path[left:right], ((offset,'g'),), ((offset,'x'),(offset,'y')))
        model = Movies(Presentation(edges,marks,[rule]),path)
        movies = []
        for history in histories:
            index = history.index((1,'g'))
            # Sort the reverse initial word into the selected intermediate order.
            ranks = {event:i for i,event in enumerate(history)}
            before = sorting_steps([(ranks[e],e) for e in initial])
            out,_ = model.named(history,0,index)
            actions = before + [(0,index)] + sorting_steps(out)
            prefix = {p for p,_ in history[:index]}
            movies.append((actions,prefix))
        inside = set(range(left,right))
        for first,src in movies:
            for second,dst in movies:
                expected = src <= dst and (src & inside) == (dst & inside)
                assert model.compare(initial,first,second)['surface'] == expected
                comparisons += 1

    # Enumerate the forward cube faces with unequal spatial lengths. Distinct
    # readings have the same signed endpoints, including each reverse cube query.
    for i,e in enumerate(path):
        u,v = e.upper(),str(i)
        edges[u],edges[v] = (i,5+i),(5+i,i+1)
        marks[e] = (e,u+v)
    model = Movies(Presentation(edges,marks,[]),path)
    sorts = []
    pending = [(initial,[])]
    while pending:
        h,actions = pending.pop()
        successors = [(s[0],actions+[('swap',j)]) for j in range(len(h)-1)
                      if (s:=model.swap(h,j)) is not None and s[1]]
        if successors:
            pending.extend(successors)
        else:
            sorts.append(actions)
    assert len(sorts) == 16
    for first in sorts:
        for second in sorts:
            assert model.compare(initial,first,second)['surface']
    # Repeated occurrences of the same deletion have distinct spatial inputs.
    # The polygon and the spectator both leave an empty spatial path.
    deleting = Presentation({'f': (0,0)}, {'d': ('f',''), 'l': ('f','f')},
                            [Rule('f',((0,'d'),),((0,'l'),(0,'d')))])
    model = Movies(deleting,'fff')
    initial = ((2,'d'),(1,'d'),(0,'d'))
    movies = []
    for order in permutations(range(3)):
        ranks = {event:i for i,event in enumerate(order)}
        actions = sorting_steps([(ranks[e],e) for e in reversed(range(3))])
        _,history = model.parse(initial,actions)
        i = order.index(1)
        actions.append((0,i))
        after,_ = model.named(history,0,i)
        while True:
            step = next(((j,s[0]) for j in range(len(after)-1)
                         if (s:=model.swap(after,j)) is not None and s[1]), None)
            if step is None:
                break
            j,after = step
            actions.append(('swap',j))
        movies.append((actions,set(order[:i])))
    for first,src in movies:
        for second,dst in movies:
            assert model.compare(initial,first,second)['surface'] == (src <= dst)
    return dict(four_column_polygon_queries=comparisons, changing_path_cube_queries=len(sorts)**2,
                empty_spatial_output_queries=len(movies)**2)


def checks():
    edges={'f':(0,1),'u':(0,2),'v':(2,1),'g':(1,3),'h':(1,4),'k':(4,3)}
    marks={'a':('f','uv'),'x':('f','f'),'y':('f','uv'),
           'b':('g','hk'),'m':('g','g'),'n':('g','hk'),'T':('fg','uvg')}
    rules=[Rule('f',((0,'a'),),((0,'x'),(0,'y'))),
           Rule('g',((0,'b'),),((0,'m'),(0,'n'))),
           Rule('fg',((0,'T'),),((0,'a'),)),
           Rule('fg',((0,'a'),(2,'b')),((1,'b'),(0,'a'))),
           Rule('fg',((0,'a'),),((0,'x'),(0,'y')))]
    pres=Presentation(edges,marks,rules)
    model=Movies(pres,'fg')
    source=((1,'b'),(0,'a'))
    early=[('swap',0),(0,0)]
    late=[(0,1),('swap',0),('swap',1)]
    assert model.compare(source,early,late)['surface']
    assert not model.compare(source,late,early)['surface']
    long_start=((0,'T'),(2,'b'))
    gate=[(2,0),(3,0)]
    assert model.compare(long_start,gate+early,gate+late)['surface']
    assert not model.compare(long_start,gate+late,gate+early)['surface']
    # Same internal split as rule 0. Its declared spatial window includes m.
    overlap=((1,'m'),(0,'a'))
    long_early=[('swap',0),(4,0)]
    long_late=[(4,1),('swap',0),('swap',1)]
    assert not model.compare(overlap,long_early,long_late)['surface']
    assert not model.compare(overlap,long_late,long_early)['surface']
    assert model.compare(overlap,early,late)['surface']
    # Compare against the independent incidence solver inside the two-column subsystem.
    from semistrict_surface_joint_polygons import problem,solution
    from semistrict_surface_planar_cylinder import moves
    words=[('p',('a',),('x','y')),('q',('b',),('m','n')),('gate',('a','b'),('b','a'))]
    rr={'p':0,'q':1,'gate':3,'swap':'swap'}
    pairs=0
    state_count=0
    for original in ['ba','ab']:
        groups={}
        history=source if original=='ba' else ((0,'a'),(2,'b'))
        work=[(tuple(original),[],[],0)]
        while work:
            w,raw,trace,count=work.pop()
            groups.setdefault(w,[]).append((raw,trace))
            for n,i,l,r,out in moves(w,words,{'b','m','n'}):
                used=count+(n!='swap')
                if used<=3:
                    work.append((out,raw+[(rr[n],i)],trace+[(n,i,l,r)],used))
        for group in groups.values():
            for actions,path in group:
                for more,other in group:
                    data=problem(tuple(original),{'b','m','n'},(path,other),())
                    expected=data is not None and solution(data) is not None
                    answer=model.compare(history,actions,more)
                    assert answer['surface']==expected
                    pairs+=1
                    state_count+=answer['states']
    return dict(comparisons=pairs,visited_descriptions=state_count,changing_spatial_queries=7, **wider_checks())


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        rules=[Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        pres=Presentation(q['edges'],q['marks'],rules)
        result=Movies(pres,q['start']).compare(tuple(map(tuple,q['source'])),q['first'],q['second'])
    else:
        result=checks()
    print(json.dumps(result))
