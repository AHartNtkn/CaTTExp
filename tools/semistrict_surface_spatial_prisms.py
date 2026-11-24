"""Decide old degree-four comparisons on every finite positive Gray 3-computad without a spatial triple."""
from argparse import ArgumentParser
from collections import defaultdict
from functools import lru_cache
import json
from pathlib import Path

from semistrict_surface_signed_width_two import Movies, Presentation, Rule
from semistrict_surface_transfer_cables import compare


def neighbours(pres):
    graph = defaultdict(set)
    for u,v in pres.edges.values():
        graph[u].add(v)
    @lru_cache(None)
    def reaches(u):
        seen = {u}
        todo = [u]
        while todo:
            for v in graph[todo.pop()]-seen:
                seen.add(v)
                todo.append(v)
        return seen
    intervals = {n:(pres.poles(s or t) if s or t else (pres.mark_roots[n],)*2)
                 for n,(s,t) in pres.marks.items()}
    def adjacent(u,v):
        before = next((n for n,(_,b) in intervals.items() if u in reaches(b)),None)
        after = next((n for n,(a,_) in intervals.items() if a in reaches(v)),None)
        return before,after
    return intervals,adjacent


def spatial_triple(pres):
    intervals,adjacent = neighbours(pres)
    for n,(u,v) in intervals.items():
        before,after = adjacent(u,v)
        if before is not None and after is not None:
            return before,n,after
    return None


def spatial_roles(pres):
    if spatial_triple(pres) is not None:
        raise ValueError('three 2-events can compose spatially')
    _,adjacent = neighbours(pres)
    def role(path):
        before,after = adjacent(*pres.poles(path))
        return 'left' if after is not None else 'right' if before is not None else None
    return ({n:role(s) for n,(s,_) in pres.marks.items()},
            {i:role(r.path) for i,r in enumerate(pres.rules)})


def read(model,source,actions,roles,ids):
    h = source
    wires = [(-1,i) for i in range(len(h))]
    anchors,frames,trace = {},{},[]
    pres = model.pres
    def anchor(e,path,pos,n):
        s,t = pres.marks[n]
        value = (n,path[pos+len(s):] if roles[n]=='right' else path[:pos])
        assert anchors.setdefault(e,value)==value
    for e,path,(pos,n) in zip(wires,pres.walk(model.start,h),h):
        anchor(e,path,pos,n)
    for n,i in actions:
        if n=='swap':
            follow = model.swap(h,i,True)
            if follow is None:
                raise ValueError('expected a native swap')
            wires[i:i+2] = wires[i:i+2][::-1]
            l,r = h[i:i+2],follow[i:i+2]
        else:
            rule = pres.rules[n]
            follow,off = model.named(h,n,i)
            l,r = h[i:i+len(rule.source)],follow[i:i+len(rule.target)]
            path = pres.walk(model.start,h[:i])[-1]
            node = ids.setdefault((n,tuple(wires[i:i+len(l)])),len(ids))
            frames[node] = path[:off],path[off+len(rule.path):]
            outputs = [(node,k) for k in range(len(r))]
            wires[i:i+len(l)] = outputs
            for e,w,(pos,event) in zip(outputs,pres.walk(path,r),r):
                anchor(e,w,pos,event)
        trace.append((n,i,tuple(x for _,x in l),tuple(x for _,x in r)))
        h = follow
    return h,anchors,frames,trace


def decide(model,source,first,second):
    if model.attachments:
        raise ValueError('expected a 3-computad')
    roles,rules = spatial_roles(model.pres)
    right = {n for n,s in roles.items() if s=='right'}
    anchored = {i for i,s in rules.items() if s is None}
    ids = {}
    a,b = [read(model,source,path,roles,ids) for path in (first,second)]
    if a[0]!=b[0]:
        raise ValueError('expected parallel readings')
    if a[1]!=b[1] or a[2].keys()!=b[2].keys():
        return None
    def fits(moves):
        frames = a[2].copy()
        for side,p,e in moves:
            label,outer = a[1][e]
            incoming,outgoing = model.pres.marks[label]
            left,right = frames[p]
            if side==0:
                tail = incoming+outer
                if not right.endswith(tail):
                    return False
                frames[p] = left,right[:-len(tail)]+outgoing+outer
            else:
                head = outer+incoming
                if not left.startswith(head):
                    return False
                frames[p] = outer+outgoing+left[len(head):],right
        return frames==b[2]
    return compare(tuple(x for _,x in source),right,(a[3],b[3]),anchored,fits)


def checks():
    from itertools import product
    from semistrict_surface_raw_movie_graph import raw_compare
    # b and c overlap one another. Only c is disjoint from the entire p window.
    edges = {'f':(0,1),'k':(1,2),'g':(2,3),'u':(2,4),'v':(4,3)}
    marks = {'a':('f','f'),'x':('f','f'),'b':('kg','kg'),'c':('g','uv'),'d':('g','g')}
    rules = [Rule('fk',((0,'a'),),((0,'x'),(0,'x'))),
             Rule('g',((0,'d'),),((0,'d'),(0,'d'))),
             Rule('fkg',((1,'b'),),((2,'d'),(0,'a'))),
             Rule('fkg',((0,'a'),(2,'d')),((1,'b'),))]
    model = Movies(Presentation(edges,marks,rules),'fkg')
    tests = 0
    positives = 0
    for source in [((1,'b'),(0,'a')),((2,'c'),(0,'a')),((2,'d'),(0,'a')),((1,'b'),)]:
        groups = defaultdict(list)
        todo = [(source,(),0)]
        while todo:
            h,path,n = todo.pop()
            names = tuple(sorted(r for r,_ in path if r!='swap'))
            groups[h,names].append(path)
            for i in range(len(h)):
                out = model.swap(h,i,True)
                if out is not None:
                    todo.append((out,path+(('swap',i),),n))
                if n==2:
                    continue
                for rid in range(len(rules)):
                    result = model.named(h,rid,i)
                    if result is not None:
                        todo.append((result[0],path+((rid,i),),n+1))
        for group in groups.values():
            for a,b in product(group,repeat=2):
                ok = decide(model,source,a,b) is not None
                assert raw_compare(model,source,a,b)['raw']==ok
                assert model.compare(source,a,b)['surface']==ok
                tests += 1
                positives += ok
    early = [('swap',0),(0,0)]
    late = [(0,1),('swap',0),('swap',1)]
    assert decide(model,((1,'b'),(0,'a')),early,late) is None
    assert decide(model,((2,'c'),(0,'a')),early,late)
    # Encode DAG reachability as the gap between the first two possible sites.
    links = [(i,j) for i in range(4) for j in range(i+1,4)]
    for mask in range(1<<len(links)):
        graph = {'a':(-1,0),'b':(3,4),'c':(4,5)}
        reachable = {0}
        for n,(i,j) in enumerate(links):
            if mask & (1<<n):
                graph[str(n)] = i,j
                if i in reachable:
                    reachable.add(j)
        pres = Presentation(graph,{n:(n,n) for n in 'abc'},[])
        assert spatial_triple(pres)==(('a','b','c') if 3 in reachable else None)
    return dict(comparisons=tests,positive=positives,overlapping_window_rejected=True,
                changing_exterior_accepted=True,degree_four_context_queries=1<<len(links))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--query',type=Path)
    modes.add_argument('--context',type=Path,help='decide reflection at every old degree-four type')
    args = parser.parse_args()
    if args.query or args.context:
        q = json.loads((args.query or args.context).read_text())
        if q.get('attachments'):
            raise ValueError('expected a 3-computad')
        rules = [Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        pres = Presentation(q['edges'],q['marks'],rules,q.get('mark_roots'))
        if args.context:
            triple = spatial_triple(pres)
            result = dict(every_degree_four_judgment_reflects=triple is None,spatial_triple=triple)
        else:
            model = Movies(pres,q['start'])
            cert = decide(model,tuple(map(tuple,q['source'])),q['first'],q['second'])
            result = dict(raw=cert is not None,surface=cert is not None,schedule=cert)
    else:
        result = checks()
    print(json.dumps(result))
