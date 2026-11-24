"""Compare parallel prism schedules by their directed polygon-pair increments."""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import product
import json
from pathlib import Path

from semistrict_surface_planar_cylinder import parse
from semistrict_surface_total_ports import incidence
from semistrict_surface_transfer_cables import slot, transition


class Rectangles:
    def __init__(self,source,right,traces,anchored):
        ids = {}
        a,b = [incidence(source,right,t,ids) for t in traces]
        if a[:3]!=b[:3]:
            raise ValueError('old prism boundaries have different named incidence')
        _,self.sides,self.graph,_ = a
        self.ends = [{e:tuple(data[3].get(e,())) for e in self.sides} for data in (a,b)]
        self.private = {}
        self.producer = {}
        for p,(n,ins,outs) in self.graph.items():
            colours = {self.sides[e] for e in ins+outs}
            if len(colours)==1 and n not in anchored:
                self.private[p] = next(iter(colours))
                self.producer.update((e,p) for e in outs)

    def validate(self,face,fits):
        words = self.ends[0]
        routes = {p:() for p in self.private}
        schedule = []
        for side,p,f in face:
            f = tuple(f)
            if self.private.get(p)!=side or self.sides.get(f)!=1-side or f in routes[p]:
                raise ValueError('invalid prism occurrence')
            words = transition(words,side,p,f,self.graph)
            if words is None:
                raise ValueError('unavailable prism redex')
            routes[p] += (f,)
            schedule.append((side,p,f))
        if words!=self.ends[1] or (fits and not fits(schedule)):
            raise ValueError('expected a prism paste at the actual old ends')
        return routes

    def compare(self,faces,fits=None,placement=None):
        if len(faces)!=2:
            raise ValueError('expected two prism schedules')
        a,b = [self.validate(face,fits) for face in faces]
        w = {}
        order = []
        left = sorted(p for p,side in self.private.items() if side==0)
        right = sorted(q for q,side in self.private.items() if side==1)
        for p in left:
            for q in right:
                f = self.graph[q][1][0]
                count = w.get((p,self.producer.get(f)),0)+int(f in a[p])-int(f in b[p])
                if count not in (0,1):
                    return None
                w[p,q] = count
                if count:
                    order.append((p,q))
        current = a.copy()
        for p,q in order:
            _,ins,outs = self.graph[p]
            _,inputs,outputs = self.graph[q]
            i,j = slot(current[p],inputs),slot(current[q],ins)
            if i is None or j is None:
                return None
            if placement and not placement(p,q,current[p][:i],current[q][:j]):
                return None
            current[p] = current[p][:i]+outputs+current[p][i+len(inputs):]
            current[q] = current[q][:j]+outs+current[q][j+len(ins):]
        return order if current==b else None


def checks():
    rules = [(n,tuple(l),tuple(r)) for n,l,r in
             [('birth','w','Ba'),('p','a','xx'),('r','xx','a'),
              ('q','B','YY'),('s','YY','B'),('finish','aB','X')]]
    source,right = ('w',),set('BYX')
    begin = [('birth',0),('q',0),('s',0),('swap',0),('p',0),('r',0),('finish',0)]
    end = [('birth',0),('p',1),('r',1),('swap',0),('q',1),('s',1),('finish',0)]
    traces = [parse(source,rules,right,path)[1] for path in (begin,end)]
    model = Rectangles(source,right,traces,set())
    moves = [(side,p,f) for p,side in model.private.items() for f,s in model.sides.items() if side!=s]
    paths = set()
    todo = [(model.ends[0],())]
    while todo:
        words,path = todo.pop()
        if words==model.ends[1]:
            paths.add(path)
            continue
        for move in moves:
            nxt = transition(words,*move,model.graph)
            if nxt is not None:
                assert move not in path
                todo.append((nxt,path+(move,)))
    classes = {}
    for path in paths:
        if path in classes:
            continue
        classes[path] = path
        todo = [path]
        while todo:
            u = todo.pop()
            for j in range(len(u)-1):
                v = u[:j]+(u[j+1],u[j])+u[j+2:]
                if v in paths and v not in classes:
                    classes[v] = path
                    todo.append(v)
    edges = defaultdict(set)
    for p,side in model.private.items():
        if side!=0:
            continue
        for q,side in model.private.items():
            if side!=1:
                continue
            _,ins,outs = model.graph[p]
            _,inputs,outputs = model.graph[q]
            neg = tuple((1,q,e) for e in ins)+tuple((0,p,f) for f in inputs)
            pos = tuple((0,p,f) for f in outputs)+tuple((1,q,e) for e in outs)
            for path in paths:
                for j in range(len(path)-len(neg)+1):
                    if path[j:j+len(neg)]==neg:
                        v = path[:j]+pos+path[j+len(neg):]
                        assert v in paths
                        edges[classes[path]].add(classes[v])
    reps = set(classes.values())
    positive = 0
    for a in reps:
        seen = {a}
        todo = [a]
        while todo:
            for nxt in edges[todo.pop()]-seen:
                seen.add(nxt)
                todo.append(nxt)
        for b in reps:
            result = model.compare((a,b))
            assert (result is not None)==(b in seen)
            positive += result is not None
    # Three independent mixed rectangles after a single support-changing rule.
    rules[0] = ('birth',('w',),tuple('BaBaBa'))
    begin,end = [('birth',0)],[('birth',0)]
    for k in (0,4,8):
        begin += [('q',k),('swap',k+1),('swap',k),('p',k)]
        end += [('p',k+1),('swap',k),('swap',k+1),('q',k+2)]
    traces = [parse(source,rules,right,path)[1] for path in (begin,end)]
    separate = Rectangles(source,right,traces,set())
    alternatives = []
    for p,side in separate.private.items():
        if side!=0:
            continue
        q = p-1
        _,ins,outs = separate.graph[p]
        _,inputs,outputs = separate.graph[q]
        neg = tuple((1,q,e) for e in ins)+tuple((0,p,f) for f in inputs)
        pos = tuple((0,p,f) for f in outputs)+tuple((1,q,e) for e in outs)
        alternatives.append((neg,pos))
    faces = {v:sum((alt[i] for alt,i in zip(alternatives,v)),()) for v in product((0,1),repeat=3)}
    independent = 0
    for u,v in product(faces,repeat=2):
        result = separate.compare((faces[u],faces[v]))
        assert (result is not None)==all(i<=j for i,j in zip(u,v))
        independent += result is not None
    return dict(prism_schedules=len(paths),strict_classes=len(reps),rectangle_queries=len(reps)**2,
                positives=positive,three_rectangle_queries=len(faces)**2,three_rectangle_positive=independent)


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    args = parser.parse_args()
    if args.query:
        q = json.loads(args.query.read_text())
        source,right = tuple(q['source']),set(q['right_letters'])
        rules = [(n,tuple(l),tuple(r)) for n,l,r in q['rules']]
        if any(n=='swap' or not l or not r for n,l,r in rules):
            raise ValueError('expected named rules with nonempty total sides')
        (a,x),(b,y) = [parse(source,rules,right,q[k]) for k in ('first','second')]
        if a!=b:
            raise ValueError('expected parallel readings')
        model = Rectangles(source,right,(x,y),set(q.get('anchored',())))
        result = model.compare(q['prism_faces'])
        result = dict(raw=result is not None,surface=result is not None,rectangles=result)
    else:
        result = checks()
    print(json.dumps(result))
