"""Bound and, when the bounds meet, decide the private planar failure spectrum.

--base FILE uses edges {name:[source,target]} and marks {name:[input,output]}
with nonempty edge-name lists. 'higher' is an ordered list of dictionaries,
starting with degree three, mapping a fresh name to two parallel names of the
previous rank. The search minimizes the bound over all ordered antichain layers.
"""
from argparse import ArgumentParser
from functools import cache
from itertools import combinations, product
import json
from pathlib import Path

from semistrict_surface_tree_spectra import context_spectrum


def profile(weights):
    if len(weights)<2:
        return 0
    return sum(weights)+2-min(a+b for a,b in zip(weights,weights[1:]))


def optimize(before,weights):
    n = len(weights)
    full = (1<<n)-1
    @cache
    def best(done,last,minimum):
        if done==full:
            return (2-minimum if minimum else -last),()
        enabled = sum(1<<i for i in range(n) if not done&(1<<i) and not before[i]&~done)
        best_value = None
        group = enabled
        while group:
            weight = max(weights[i] for i in range(n) if group&(1<<i))
            bound = min(minimum,last+weight) if minimum else (last+weight if last else 0)
            value,tail = best(done|group,weight,bound)
            candidate = weight+value
            if best_value is None or candidate<best_value:
                best_value,partition = candidate,(group,)+tail
            group = (group-1)&enabled
        return best_value,partition
    value,masks = best(0,0,0)
    layers = [[i for i in range(n) if mask&(1<<i)] for mask in masks]
    assert value==profile([max(weights[i] for i in g) for g in layers])
    return value,layers


def bounds(data):
    edges,marks = data['edges'],data['marks']
    def poles(path):
        if not path or any(edges[a][1]!=edges[b][0] for a,b in zip(path,path[1:])):
            raise ValueError('expected a positive path')
        return edges[path[0]][0],edges[path[-1]][1]
    pole = {}
    faces = {}
    for name,(a,b) in marks.items():
        pole[name] = poles(a)
        if pole[name]!=poles(b):
            raise ValueError('nonparallel planar mark')
        faces[name] = (tuple(a),tuple(b))
    heights = dict.fromkeys(pole.values(),1)
    used = set(marks)|set(edges)
    for d,decl in enumerate(data.get('higher',[]),2):
        fresh = {}
        for name,(a,b) in decl.items():
            if name in used or a not in faces or b not in faces or faces[a]!=faces[b]:
                raise ValueError('expected fresh private generators at parallel variables')
            fresh[name] = pole[a]
            heights[pole[a]] = d
        used.update(fresh)
        pole = fresh
        faces = {name:tuple(pair) for name,pair in decl.items()}

    # Adding a shortcut across an existing nonempty path preserves graph reachability.
    slots = list(heights)
    arrows = list(edges.values())+slots
    lower = context_spectrum(dict(edges=arrows,slots=[(*s,heights[s]) for s in slots]))
    if 'failing_from' in lower:
        return lower
    vertices = {v for e in arrows for v in e}
    reach = {a:{a} for a in vertices}
    for a,b in arrows:
        reach[a].add(b)
    for b in vertices:
        for a in vertices:
            if b in reach[a]:
                reach[a].update(reach[b])
    before = [sum(1<<j for j,(_,y) in enumerate(slots) if x in reach[y]) for x,_ in slots]
    upper,layers = optimize(before,[heights[s] for s in slots])
    lower_degrees = lower['failing_degrees']
    if all(h<=2 for h in heights.values()):
        upper = max(lower_degrees,default=1)-1  # Response 112 gives equality on this subclass.
    return dict(failing_degrees=lower_degrees,
                undecided_by_bounds=[d for d in range(3,upper+2) if d not in lower_degrees],
                layers=[[slots[i] for i in g] for g in layers])


def checks():
    from semistrict_surface_planar_event_projection import cuts
    from semistrict_surface_planar_columns import Column
    def generate(n):
        return [(i,j) for i in range(n) for j in range(i+1,n)]
    comparisons = gaps = 0
    for n in range(1,5):
        pairs = generate(n)
        for code in range(1<<len(pairs)):
            before = [0]*n
            for bit,(i,j) in enumerate(pairs):
                if code&(1<<bit):
                    before[j] |= (1<<i)|before[i]
            for weights in ([1]*n,[3]*n, list(range(1,n+1)),list(reversed(range(1,n+1)))):
                upper,layers = optimize(before,weights)
                lower = max((profile([weights[i] for i in subset]) for k in range(n+1)
                    for subset in combinations(range(n),k)
                    if all(before[b]&(1<<a) for a,b in zip(subset,subset[1:]))),default=0)
                best = None
                for assignment in product(range(n),repeat=n):
                    if set(assignment)!=set(range(max(assignment)+1)):
                        continue
                    if any(assignment[a]>=assignment[b] for a,b in pairs if before[b]&(1<<a)):
                        continue
                    v = profile([max(w for w,j in zip(weights,assignment) if j==k)
                                 for k in range(max(assignment)+1)])
                    best = v if best is None else min(v,best)
                assert lower<=upper==best
                if len(set(weights))==1:
                    assert lower==upper
                comparisons += 1
                gaps += lower<upper
    # A split, repeated steps at its first layer, a separate layer, and a
    # merge. The same token names a temporal sequence of different events.
    col = Column(3,[(0,1,2),(1,1,1),(3,1,1),(0,2,1),(0,1,1)])
    # Vertex levels for the original and the fresh inner vertex of the split.
    height = [0,1,1,2,0]
    level = [1,1,2,1,1]
    frontier,sites = cuts(col)
    def carried(w):
        a,b = col.wires[w]
        return range(height[a]+1,height[b]+1)
    groups = [[i for i,k in enumerate(level) if k==j] for j in (1,2)]
    def word(w):
        return [(k,sum(e<=col.producer.get(w,-1) for e in groups[k-1])) for k in carried(w)]
    for i,(ins,outs) in enumerate(col.boxes):
        s = sum((word(w) for w in ins),[])
        t = sum((word(w) for w in outs),[])
        assert any(k==level[i] for k,_ in s)
        assert t==[(k,p+int(k==level[i])) for k,p in s]
    for done,live in frontier.items():
        assert sum((word(w) for w in live),[])==[(k+1,len(done.intersection(g))) for k,g in enumerate(groups)]
        assert len({level[i] for i in sites[done]})==len(sites[done])
    def base(h):
        edges,marks,higher = {},{},[{} for _ in range(max(h)-1)]
        for i,d in enumerate(h):
            a,b,c = (f'{s}{i}' for s in 'abc')
            edges.update({a:(i,i+1),b:(i,f'z{i}'),c:(f'z{i}',i+1)})
            names = [f'm{i}a',f'm{i}b']
            for name in names:
                marks[name] = [[a],[b,c]]
            for j in range(d-1):
                next_names = [f'q{i}_{j}a',f'q{i}_{j}b']
                for name in next_names:
                    higher[j][name] = names
                names = next_names
        return dict(edges=edges,marks=marks,higher=higher)
    for heights in ([4],[2,6],[2,4,2],[2,3,4,5],[3,3,3,3]):
        result = bounds(base(heights))
        assert result['failing_degrees']==list(range(3,profile(heights)+2)) and not result['undecided_by_bounds']
    mixed = base([1,1,1,1])
    extra = base([7])
    edge_map = {'a0':'long','b0':'enter','c0':'leave'}
    mixed['edges'].update(long=(1,4),enter=(1,'inner'),leave=('inner',4))
    for name,(s,t) in extra['marks'].items():
        mixed['marks']['high'+name] = [[edge_map[e] for e in w] for w in (s,t)]
    mixed['higher'] = [{'high'+name:['high'+a,'high'+b] for name,(a,b) in layer.items()}
                       for layer in extra['higher']]
    result = bounds(mixed)
    assert result['failing_degrees']==[3,4,5] and result['undecided_by_bounds']==list(range(6,12))
    loop = base([4])
    loop['edges']['back'] = (1,0)
    assert bounds(loop)=={'failing_from':3}
    print(f'{comparisons} weighted posets versus exhaustive layer and chain choices, '
          f'{gaps} strict gaps at up to four slots; {len(frontier)} grouped wire cuts; '
          'seven planar presentations including a connected five-slot gap')


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('--base',type=Path)
    args = p.parse_args()
    if args.base:
        print(json.dumps(bounds(json.loads(args.base.read_text()))))
    else:
        checks()
