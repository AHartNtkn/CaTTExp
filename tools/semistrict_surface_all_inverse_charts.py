"""Compile bare cube charts and finite prefixes of their two-sided inverse data."""
import argparse
from collections import Counter, defaultdict
from itertools import product
import json

from semistrict_surface_finite_inverse_charts import dictionary
from semistrict_surface_scalar_lift import cube
from semistrict_surface_three_axis_paths import Chart


def tower(rank, ceiling):
    """Refs are chart-local. Composition lists the first arrow first."""
    frontier = [('atom', 'negative-face', 'positive-face')]
    declarations = []
    while frontier:
        upcoming = []
        for f,s,t in frontier:
            left, right = f+'/L', f+'/R'
            declarations.extend([(rank,left,t,s),(rank,right,t,s)])
            if rank < ceiling:
                for tag, chain, pole in [('u',(f,right),s),('v',(left,f),t)]:
                    g = f+'/'+tag
                    source = ('compose',rank-1,*chain)
                    target = ('identity',pole)
                    declarations.append((rank+1,g,source,target))
                    upcoming.append((g,source,target))
        frontier = upcoming
        rank += 1
    return declarations


def compile_base(data, ceiling=None):
    if ceiling is not None and ceiling < 3:
        raise ValueError('requested degree must be at least three')
    pairs,pump = dictionary(data)
    if pump:
        return {'finite':False,'unbounded_gap':pump}
    rules = data['rules']
    links = defaultdict(list)
    repeated = None
    for a,g,b in pairs:
        links[a].append((g,b))
        if a == b:
            repeated = a,g
    if repeated and ceiling is None:
        return {'finite':False,'repeated_slot_and_return_path':repeated}
    if not repeated:
        # Distinct slots in any chain; reachability includes every transitive join.
        longest = {}
        def depth(a):
            if a not in longest:
                longest[a] = 1+max((depth(b) for _,b in links[a]),default=0)
            return longest[a]
        height = max(map(depth,rules),default=0)
        ceiling = min(ceiling,height+1) if ceiling is not None else height+1
    charts = []
    marks = {x:(l,r) for x,(_,l,r) in rules.items()}
    todo = [((a,),()) for a in rules]
    while todo:
        slots,gaps = todo.pop()
        k = len(slots)
        if k >= 2:
            chart = Chart(tuple((a,*marks[a]) for a in slots),gaps)
            source = chart.reading(range(k-1,-1,-1))
            target = chart.reading(range(k))
            assert cube(source,marks,0,k) == target
            charts.append({'axes':slots,'gaps':gaps,'edge_path':chart.start_word(),
                           'descending_history':source,'ascending_history':target,
                           'declarations':tower(k+1,ceiling)})
        if k < ceiling-1:
            todo.extend((slots+(b,),gaps+(g,)) for g,b in links[slots[-1]])
    return {'finite':True, 'auxiliary_ceiling':ceiling if charts else None, 'charts':charts}


def verify_tower(declarations, rank):
    faces = {'atom':(rank,'negative-face','positive-face')}
    for d,g,s,t in declarations:
        if g.endswith(('/L','/R')):
            assert faces[g[:-2]] == (d,t,s)
        else:
            _,cut,a,b = s
            da,sa,ta = faces[a]
            db,sb,tb = faces[b]
            assert da == db == d-1 and cut == d-2 and ta == sb and sa == tb == t[1]
        faces[g] = (d,s,t)


def checks():
    total = declarations = 0
    for n in range(1,6):
        data = {'edges':{str(i):(i,i+1) for i in range(n)},
                'rules':{str(i):(i,str(i),str(i)) for i in range(n)}}
        output = compile_base(data)
        assert output['finite'] and len(output['charts']) == 2**n-1-n
        assert output['auxiliary_ceiling'] == (n+1 if n>=2 else None)
        for chart in output['charts']:
            k = len(chart['axes'])
            decls = chart['declarations']
            verify_tower(decls,k+1)
            counts = Counter(d for d,*_ in decls)
            assert counts[k+1] == 2
            assert all(counts[k+1+i] == 3*2**i for i in range(1,n-k+1))
            declarations += len(decls)
            total += 1
    scalar = {'edges':{},'rules':{'s':('x','','')}}
    assert not compile_base(scalar)['finite']
    for d in range(3,9):
        ans = compile_base(scalar,d)
        assert ans['finite'] and len(ans['charts']) == d-2
        for chart in ans['charts']:
            verify_tower(chart['declarations'],len(chart['axes'])+1)
            declarations += len(chart['declarations'])
            total += 1
    gapped = {'edges':{'a':(0,1),'b':(1,1),'c':(1,2)},
              'rules':{'A':(0,'a','a'),'C':(1,'c','c')}}
    assert 'unbounded_gap' in compile_base(gapped,3)
    disconnected = {'edges':{'a':(0,1),'b':(2,2)},'rules':{'A':(0,'a','a')}}
    assert compile_base(disconnected)['finite']
    print(f'{total} fitted cube charts, {declarations} inverse-tower boundary checks, '
          'pumped gap and unbounded ranks distinguished')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',help='JSON with edges and rewrite rules, as in Response 81')
    parser.add_argument('--through',type=int)
    args = parser.parse_args()
    if args.base:
        with open(args.base) as handle:
            print(json.dumps(compile_base(json.load(handle),args.through)))
    else:
        checks()
