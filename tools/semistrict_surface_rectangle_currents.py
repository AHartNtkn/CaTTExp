"""Detect degree-five surface obstructions using placed polygon-pair coefficients."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from itertools import combinations, product
from pathlib import Path
import json

from semistrict_surface_signed_width_two import Movies, Presentation, Rule
from semistrict_surface_two_slot_polygons import advance_crossing, segments
from semistrict_surface_two_slot_rectangles import compare as raw, routes


def priced(model,weights):
    if weights is None:
        unit = all(len(a)==len(b) for a,b in model.pres.marks.values())
        weights = dict.fromkeys(model.pres.edges,int(unit))
    if set(weights)!=set(model.pres.edges) or any(type(v)!=int or v<0 for v in weights.values()):
        raise ValueError('expected a nonnegative integer weight per spatial edge')
    def mass(path):
        return sum(weights[e] for e in path)
    if any(mass(a)!=mass(b) for a,b in model.pres.marks.values()):
        raise ValueError('each spatial event must conserve the supplied weight')
    return weights,mass


def placed_graph(model,mass):
    length = mass(model.start)
    graph = {}
    for p,r in enumerate(model.pres.rules):
        if len(r.source)!=1 or len(r.target)!=1:
            raise ValueError('expected unary polygons')
        i,e = r.source[0]
        j,f = r.target[0]
        for off in range(length-mass(r.path)+1):
            graph[p,off] = (e,off+mass(r.path[:i])),(f,off+mass(r.path[:j]))
    return graph


def bridge_cuts(graph):
    adj = defaultdict(list)
    for p,(a,b) in graph.items():
        adj[a].append((p,b))
        adj[b].append((p,a))
    cuts = {}
    for p,(a,b) in graph.items():
        seen,todo = {b},[b]
        while todo and a not in seen:
            for q,v in adj[todo.pop()]:
                if q!=p and v not in seen:
                    seen.add(v)
                    todo.append(v)
        if a not in seen:
            cuts[p] = seen
    return cuts


def totals(model,source,first,second,schedule,mass,blocks):
    result = Counter()
    for (g,c),steps in routes(model,source,first,second,schedule,blocks).items():
        rows,crossings,_ = blocks[g]
        h = crossings[c][0]
        for sign,strand,r in steps:
            p = rows[strand][r]
            after = advance_crossing(model,h,p,sign==1)
            assert after is not None
            if sign==1:
                _,off = model.named(after,p,0)
                i,e = h[1]
                path = model.pres.walk(model.start,h)[1]
            else:
                _,off = model.named(model.swap(h,0,True),p,0)
                i,e = h[0]
                path = model.start
            result[sign,(p,mass(model.start[:off])),(e,mass(path[:i]))] += 1
            h = after
    return result


def decide(model,source,first,second,faces,weights=None):
    rectangles = raw(model,source,first,second,faces)
    weights,mass = priced(model,weights)
    graph = placed_graph(model,mass)
    cuts = bridge_cuts(graph)
    blocks,_ = segments(model,source,first)
    a,b = [totals(model,source,first,second,s,mass,blocks) for s in faces]
    b.subtract(a)
    # Reads of one bridge column give the exact coefficient of that pair.
    # Right and left prism labels independently give its two boundary equations.
    fixed = {}
    for side in (1,-1):
        others = {q for d,q,e in b if side==d}
        for p,vertices in cuts.items():
            for q in others:
                pair = (p,q) if side==1 else (q,p)
                value = sum(b[side,q,e] for e in vertices)
                if fixed.setdefault(pair,value)!=value:
                    assert rectangles is None
                    return dict(surface=False,raw=False,obstruction='inconsistent pair coefficient',pair=pair)
    forest = len(cuts)==len(graph)
    info = dict(forest=forest,bridges=len(cuts),placements=len(graph))
    for (p,q),value in fixed.items():
        blocked = p[1]+mass(model.pres.rules[p[0]].path)>q[1]
        if value<0 or (value and blocked):
            assert rectangles is None
            return dict(info,surface=False,raw=False,pair=(p,q),coefficient=value,
                        obstruction='negative pair coefficient' if value<0 else 'overlapping placed windows')
    if rectangles is not None:
        return dict(info,surface=True,raw=True,rectangles=rectangles)
    if forest and all(weights.values()):
        raise AssertionError('a raw-empty forest comparison must have a coefficient obstruction')
    return dict(info,surface=None,raw=False)


def shuffles(first,right,left):
    n,m = len(right),len(left)
    all_paths = []
    for indices in combinations(range(n+m),n):
        word = first.copy()
        schedule = []
        def change(j,step,new):
            word[j:j+2] = new
            schedule.append(step)
        for k in range(n+m):
            c = word.index(('swap',0))
            if k in indices:
                i = max(j for j in range(c) if word[j] in right)
                for j in range(i,c-1):
                    change(j,('commute',j),word[j:j+2][::-1])
                p = word[c-1][0]
                change(c-1,('prism',c-1,1),[('swap',0),(p,1)])
            else:
                i = next(j for j in range(c+1,len(word)) if word[j] in left)
                for j in reversed(range(c+1,i)):
                    change(j,('commute',j),word[j:j+2][::-1])
                p = word[c+1][0]
                change(c,('prism',c,-1),[(p,1),('swap',0)])
        all_paths.append(schedule)
    return word,all_paths


def checks():
    edges = {'f':(0,1),'k':(1,1),'g':(1,2)}
    marks = {n:(edge,edge) for n,edge in zip('abcxyz','fffggg')}
    rules = [Rule('fk',((0,a),),((0,b),)) for a,b in zip('ab','bc')]
    rules += [Rule('kg',((1,a),),((1,b),)) for a,b in zip('xy','yz')]
    left,right = [(0,0),(1,0)],[(2,0),(3,0)]
    first = right+[('swap',0)]+left
    second,faces = shuffles(first,right,left)
    counts = Counter()
    for length in (1,2,3):
        model = Movies(Presentation(edges,marks,rules),'f'+'k'*length+'g')
        src = ((length+1,'x'),(0,'a'))
        for a,b in product(faces,repeat=2):
            result = decide(model,src,first,second,(a,b))
            assert result['forest'] and result['surface']==result['raw']
            counts[result.get('obstruction','raw')] += 1
    # Both windings involve two uses of exactly the same placed declaration.
    s = ((0,'a'),(0,'a'))
    rules = [Rule('',((0,e),),((0,f),)) for e,f in zip('ab','bc')]
    marks = dict.fromkeys('abc',('',''))
    model = Movies(Presentation({},marks,rules,dict.fromkeys(marks,0)),'')
    first = [(0,0),('swap',0),(0,0),(1,0),('swap',0),(1,0)]
    second = [(0,1),('swap',0),(0,1),(1,1),('swap',0),(1,1)]
    def block(i,bit):
        if bit: return [('prism',i+1,-1),('commute',i),('prism',i+1,1)]
        return [('prism',i,1),('commute',i+1),('prism',i,-1)]
    paths = [block(0,i)+block(3,j) for i,j in product(range(2),repeat=2)]
    for a,b in product(paths,repeat=2):
        result = decide(model,s,first,second,(a,b))
        assert result['forest'] and result['surface']==result['raw']
        counts['winding'] += 1
    # A shared unary chain labels both strands. Consecutive winding edges
    # have interleaved phase ranges and can involve the same rule on either strand.
    marks = {str(i):('','') for i in range(8)}
    chain = [Rule('',((0,str(i)),),((0,str(i+1)),)) for i in range(7)]
    model = Movies(Presentation({},marks,chain,dict.fromkeys(marks,0)),'')
    for bands in (((2,1),(1,2),(1,1)),((1,2),(2,1)),((1,1),(1,2),(1,1))):
        phases,first,second,choices = [0,0],[],[],[[]]
        for c,(nr,nl) in enumerate(bands):
            right,left = [],[]
            for strand,amount,part in ((c%2,nr,right),(1-c%2,nl,left)):
                part.extend((p,0) for p in range(phases[strand],phases[strand]+amount))
                phases[strand] += amount
            start = right+[('swap',0)]+left
            end,steps = shuffles(start,right,left)
            shifted = [[(op,i+len(first),*sign) for op,i,*sign in w] for w in steps]
            choices = [a+b for a,b in product(choices,shifted)]
            first.extend(start)
            second.extend(end)
        src = ((0,'0'),)*2
        for a,b in product(choices,repeat=2):
            result = decide(model,src,first,second,(a,b))
            assert result['forest'] and result['surface']==result['raw']
            counts['shared_chain'] += 1
    # The input f expands to gg during a 2-event, and the right mark changes
    # offset in letters. Its conserved coordinate remains 2.
    marks = {'a':('f','gg'),'A':('f','gg'),'b':('h','h'),'B':('h','h')}
    rules = [Rule('f',((0,'a'),),((0,'A'),)),Rule('h',((0,'b'),),((0,'B'),))]
    model = Movies(Presentation(dict.fromkeys('fgh',(0,0)),marks,rules),'fh')
    first = [(1,0),('swap',0),(0,0)]
    second,paths = shuffles(first,[(1,0)],[(0,0)])
    for a,b in product(paths,repeat=2):
        result = decide(model,((1,'b'),(0,'a')),first,second,(a,b),{'f':2,'g':1,'h':1})
        assert result['forest'] and result['surface']==result['raw']
        counts['changing_path'] += 1
    # A loop makes the bridge test inconclusive on an old reverse.
    marks = {'s':('','')}
    r = ((0,'s'),)
    loop = Movies(Presentation({},marks,[Rule('',r,r)],{'s':0}),'')
    first = [(0,0),('swap',0),(0,0)]
    second = [(0,1),('swap',0),(0,1)]
    result = decide(loop,r*2,first,second,(block(0,1),block(0,0)))
    assert not result['forest'] and result['surface'] is None
    return counts


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    args = parser.parse_args()
    if args.query:
        q = json.loads(args.query.read_text())
        if q.get('attachments'): raise ValueError('expected a 3-computad')
        rules = [Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        model = Movies(Presentation(q['edges'],q['marks'],rules,q.get('mark_roots')),q['start'])
        source = tuple(map(tuple,q['source']))
        model.pres.walk(model.start,source,q.get('vertex'))
        result = decide(model,source,q['first'],q['second'],q['prism_faces'],q.get('spatial_weights'))
    else:
        result = checks()
    print(json.dumps(result))
