"""Decide degree-four reflection with private unary phase changes on both spatial sides."""
from argparse import ArgumentParser
from collections import defaultdict
import json
from pathlib import Path

from semistrict_surface_signed_width_two import Movies, Presentation, Rule


class CrossingMarks:
    def __init__(self, model):
        self.model = model
        pres = model.pres
        if model.attachments:
            raise ValueError('this criterion is for 3-computads')
        if any(not s or not t for s,t in pres.marks.values()):
            raise ValueError('an event at a loop with an empty port gives a spatial triple')
        graph = defaultdict(set)
        for u,v in pres.edges.values():
            graph[u].add(v)
        def reaches(u):
            seen = {u}
            todo = [u]
            while todo:
                for v in graph[todo.pop()]-seen:
                    seen.add(v)
                    todo.append(v)
            return seen
        intervals = [pres.poles(s) for s,_ in pres.marks.values()]
        def role(path):
            u,v = pres.poles(path)
            left = any(a in reaches(v) for a,_ in intervals)
            right = any(u in reaches(b) for _,b in intervals)
            if left and right:
                raise ValueError('three 2-events can compose spatially')
            return 'left' if left else 'right' if right else None
        for s,_ in pres.marks.values():
            role(s)
        self.roles = {}
        for i,r in enumerate(pres.rules):
            side = role(r.path)
            if side is None:
                continue
            if len(r.source)!=1 or len(r.target)!=1:
                raise ValueError('a movable rule must be unary')
            (j,a), = r.source
            (k,b), = r.target
            if j or k or pres.marks[a]!=pres.marks[b] or pres.marks[a][0]!=r.path:
                raise ValueError('a movable rule must change only the phase at its own spatial site')
            self.roles[i] = side

    def describe(self,source,actions,ids):
        # A skeleton edge ends at every crossing. A segment follows the same
        # occurrence through crossings and ends only at an immobile polygon.
        edges = [(-1,j) for j in range(len(source))]
        segments = list(edges)
        heights = defaultdict(int)
        marks = defaultdict(list)
        nodes = set()
        h = source
        for name,i in actions:
            if name in self.roles:
                seg = segments[i]
                marks[seg].append((name,heights[seg]))
                h,_ = self.model.named(h,name,i)
                continue
            if name=='swap':
                left = right = 2
                follow = self.model.swap(h,i,True)
            else:
                r = self.model.pres.rules[name]
                left,right = len(r.source),len(r.target)
                follow,_ = self.model.named(h,name,i)
            inputs = tuple(edges[i:i+left])
            key = (name,inputs)
            vertex = ids.setdefault(key,len(ids))
            assert vertex not in nodes
            nodes.add(vertex)
            outputs = [(vertex,k) for k in range(right)]
            edges[i:i+left] = outputs
            if name=='swap':
                a,b = segments[i:i+2]
                heights[a] += 1
                heights[b] += 1
                segments[i:i+2] = [b,a]
            else:
                segments[i:i+left] = outputs
            h = follow
        return (nodes,edges),dict(marks)

    def compare(self,source,first,second):
        self.model.pres.walk(self.model.start,source)
        if self.model.parse(source,first)[1]!=self.model.parse(source,second)[1]:
            raise ValueError('expected parallel old faces')
        ids = {}
        a,u = self.describe(source,first,ids)
        b,v = self.describe(source,second,ids)
        if a!=b or u.keys()!=v.keys():
            return None
        distance = 0
        for seg,x in u.items():
            y = v[seg]
            if len(x)!=len(y):
                return None
            for (p,i),(q,j) in zip(x,y):
                if p!=q or (j>i if self.roles[p]=='left' else j<i):
                    return None
                distance += abs(i-j)
        return distance


def checks():
    from semistrict_surface_planar_cylinder import moves
    from semistrict_surface_raw_movie_graph import raw_compare
    from itertools import product
    edges = {'f':(0,1),'g':(1,2)}
    marks = {x: ('f','f') if x.islower() else ('g','g') for x in 'abAB'}
    def positioned(w):
        return tuple((int(x.isupper()),x) for x in w)
    named = [('p','a','b'),('q','A','B'),('transfer','b','AA'),('back','B','aa'),
             ('gate','aA','Aa')]
    private = [Rule('f', ((0,'a'),), ((0,'b'),)), Rule('g', ((0,'A'),), ((0,'B'),))]
    rules = private+[Rule('fg',positioned(l),positioned(r)) for _,l,r in named[2:]]
    words = [(name,tuple(l),tuple(r)) for name,l,r in named]
    names = {n:i for i,(n,_,_) in enumerate(named)}
    model = Movies(Presentation(edges,marks,rules),'fg')
    solver = CrossingMarks(model)
    comparisons = accepted = nontrivial = 0
    for initial in ('Aa','aA','Ba','Ab','Aaa','AaA'):
        source = positioned(initial)
        groups = defaultdict(list)
        todo = [(tuple(initial),(),0)]
        while todo:
            w,path,n = todo.pop()
            signature = tuple(sorted(r for r,_ in path if r!='swap'))
            groups[w,signature].append(path)
            for name,i,_,_,out in moves(w,words,{'A','B'}):
                count = n+(name!='swap')
                if count <= (3 if len(initial)==2 else 2):
                    action = (names.get(name,name),i)
                    todo.append((out,path+(action,),count))
        for paths in groups.values():
            for first,second in product(paths,repeat=2):
                length = solver.compare(source,first,second)
                expected = length is not None
                assert raw_compare(model,source,first,second)['raw']==expected
                assert model.compare(source,first,second)['surface']==expected
                comparisons += 1
                accepted += expected
                nontrivial += bool(length)
    # Different spatial lengths before and after each crossing, both phases mobile.
    edges = {'f':(0,1),'u':(0,2),'v':(2,1),'g':(1,3),'h':(1,4),'k':(4,3)}
    marks = {'a':('f','uv'),'b':('f','uv'),'A':('g','hk'),'B':('g','hk')}
    model = Movies(Presentation(edges,marks,private),'fg')
    solver = CrossingMarks(model)
    source = ((1,'A'),(0,'a'))
    cases = [
        ([('swap',0),(0,0)],[(0,1),('swap',0)]),
        ([(1,0),('swap',0)],[('swap',0),(1,1)]),
        ([(1,0),('swap',0),(0,0)],[(0,1),('swap',0),(1,1)]),
    ]
    for i,(first,second) in enumerate(cases):
        assert solver.compare(source,first,second)==(2 if i==2 else 1)
        assert solver.compare(source,second,first) is None
        assert raw_compare(model,source,first,second)['raw']
        assert not raw_compare(model,source,second,first)['raw']
    return dict(comparisons=comparisons,positive=accepted,positive_prism_distance=nontrivial,
                changing_path_phase_queries=2*len(cases))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    qfile = parser.parse_args().query
    if qfile:
        q = json.loads(qfile.read_text())
        rules = [Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        if q.get('attachments'):
            raise ValueError('this criterion requires a 3-computad')
        model = Movies(Presentation(q['edges'],q['marks'],rules),q['start'])
        dist = CrossingMarks(model).compare(tuple(map(tuple,q['source'])),q['first'],q['second'])
        result = dict(raw=dist is not None,surface=dist is not None,prisms=dist)
    else:
        result = checks()
    print(json.dumps(result))
