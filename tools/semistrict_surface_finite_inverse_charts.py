"""Finite raw realization test, with bare inverse/cube charts or a pumpable gap.

JSON input has edges and rules as for semistrict_surface_history_group.
"""
import argparse
import json
from collections import defaultdict, deque
from itertools import product
from pathlib import Path

from semistrict_surface_braid_reflection import end_vertex, follow
from semistrict_surface_history_group import exchange
from semistrict_surface_three_axis_paths import Chart


def routes(graph, start):
    out = {start: ''}
    todo = deque(out)
    while todo:
        s = todo.popleft()
        for e,t in graph[s]:
            if t not in out:
                out[t] = out[s]+e
                todo.append(t)
    return out


def dictionary(data):
    edges, rules = data['edges'],data['rules']
    graph = defaultdict(list)
    if any(len(e)!=1 for e in edges):
        raise ValueError('edge names must be single characters')
    for e,(s,t) in edges.items():
        graph[s].append((e,t))
    poles = {}
    for name,(s,l,r) in rules.items():
        t = end_vertex(edges,s,l)
        if t != end_vertex(edges,s,r):
            raise ValueError('nonparallel rewrite rule')
        poles[name] = s,t
    vertices = set(v for pair in [*edges.values(),*poles.values()] for v in pair)
    paths = {s:routes(graph,s) for s in vertices}
    pairs = []
    for a,b in product(rules,repeat=2):
        start,end = poles[a][1],poles[b][0]
        if end not in paths[start]:
            continue
        live = {s for s in paths[start] if end in paths[s]}
        for x in sorted(live):
            for e,y in graph[x]:
                if x in paths[y]:
                    return None, dict(left=a,right=b,prefix=paths[start][x],
                                      cycle=e+paths[y][x],suffix=paths[x][end])
        todo = [(start,'')]
        while todo:
            s,g = todo.pop()
            if s == end:
                pairs.append((a,g,b))
            todo.extend((t,g+e) for e,t in graph[s] if t in live)
    return pairs,None


def compile_charts(data):
    pairs, gap = dictionary(data)
    if gap:
        return dict(finite=False,pumped_gap=gap)
    rules=data['rules']
    marks={name:(l,r) for name,(_,l,r) in rules.items()}
    inverses = []
    for a,g,b in pairs:
        root,l,_ = rules[a]
        right = rules[b][1]
        path = l+g+right
        h = ((len(l+g),b),(0,a))
        dest = follow(h,(1,),marks)
        assert exchange(dest,-1,marks) == h
        inverses.append(dict(root=root,path=path,positive_input=h,inverse_input=dest))
    cubes = []
    for a,g,b in pairs:
        for middle,h,c in pairs:
            if middle != b:
                continue
            chart = Chart(tuple((name,*marks[name]) for name in (a,b,c)),(g,h))
            origin = chart.reading((2,1,0))
            assert follow(origin,(2,1,2),marks) == follow(origin,(1,2,1),marks)
            cubes.append(dict(root=rules[a][0],path=chart.start_word(),history=origin,
                              left=(2,1,2),right=(1,2,1)))
    return dict(finite=True,inverse_charts=inverses,reverse_cubes=cubes)


def checks():
    finite = infinite = pairs = triples = 0
    for flags in product((False,True),repeat=6):
        # Include an isolated cycle, a cycle on an active route, parallel edges,
        # and changing-length 2-rewrites.
        edges = {c:e for c,e,use in zip('abcdef',[(0,0),(0,1),(0,1),(1,2),(2,1),(3,3)],flags) if use}
        rules = {'L':(0,'',''),'R':(2,'','')}
        if 'b' in edges and 'c' in edges:
            rules['C']=(0,'b','c')
        if 'a' in edges:
            rules['D']=(0,'','a')
        data=dict(edges=edges,rules=rules)
        result=compile_charts(data)
        if not result['finite']:
            gap=result['pumped_gap']
            a,b=gap['left'],gap['right']
            start=end_vertex(edges,rules[a][0],rules[a][1])
            for k in (1,2,8):
                g=gap['prefix']+gap['cycle']*k+gap['suffix']
                assert end_vertex(edges,start,g) == rules[b][0]
                before=((len(rules[a][1]+g),b),(0,a))
                marks={n:(l,r) for n,(_,l,r) in rules.items()}
                after=follow(before,(1,),marks)
                assert exchange(after,1,marks) is None and exchange(before,-1,marks) is None
            infinite+=1
        else:
            finite+=1
            pairs+=len(result['inverse_charts'])
            triples+=len(result['reverse_cubes'])
            # An independent length-bounded enumeration is exhaustive on a
            # finite-path corridor, whose simple paths visit each vertex once.
            all_pairs=set()
            for a,b in product(rules,repeat=2):
                start=end_vertex(edges,rules[a][0],rules[a][1])
                todo=[(start,'')]
                for _ in range(4):
                    for s,g in todo:
                        if s==rules[b][0]:
                            all_pairs.add((a,g,b))
                    todo=[(t,g+e) for s,g in todo for e,(u,t) in edges.items() if u==s]
            got,_=dictionary(data)
            assert set(got)==all_pairs
    print(f'{finite} finite and {infinite} infinite base graphs, {pairs} inverse charts '
          f'and {triples} contextual reverse cubes checked')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--base',type=Path)
    args=ap.parse_args()
    if args.base:
        print(json.dumps(compile_charts(json.loads(args.base.read_text()))))
    else:
        checks()
