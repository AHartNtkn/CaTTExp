"""Recognize positive point-rule histories at empty two-dimensional ends.

JSON has point_gates and rules mapping each name to [inputs,outputs], both
lists of point colours. --witness returns an executable signed movie. The
decision uses the structurally cyclic transition filter with exact rational
circuits. Witness expansion may be much larger than the input.
"""
from argparse import ArgumentParser
from collections import Counter,deque
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_serial_gate_tracks import read_track


def markable(rules,side):
    colours = set()
    while True:
        more = set(colours)
        for ports in rules.values():
            if colours.issuperset(ports[side]):
                more.update(ports[1-side])
        if more==colours:
            return colours
        colours = more


def positive_circuit(columns):
    """Does this set of columns have a 1-D kernel with a positive basis?"""
    n = len(columns)
    rows = [list(map(Fraction,r)) for r in zip(*columns)]
    pivots = []
    for j in range(n):
        i = len(pivots)
        pivot = next((k for k in range(i,len(rows)) if rows[k][j]),None)
        if pivot is None:
            continue
        rows[i],rows[pivot] = rows[pivot],rows[i]
        unit = rows[i][j]
        rows[i] = [v/unit for v in rows[i]]
        for k,r in enumerate(rows):
            if k!=i and r[j]:
                factor = r[j]
                rows[k] = [a-factor*b for a,b in zip(r,rows[i])]
        pivots.append(j)
    if len(pivots)!=n-1:
        return False
    free, = set(range(n))-set(pivots)
    return all(rows[i][free]<0 for i in range(len(pivots)))


def return_rules(data):
    places = data['point_gates']
    rules = data['rules'].copy()
    if len(set(places))!=len(places) or any(len(ports)!=2 or any(g not in places for p in ports for g in p)
                                            for ports in rules.values()):
        raise ValueError('expected distinct point colours and two ports on known colours per rule')
    delta = {name:tuple(b.count(p)-a.count(p) for p in places) for name,(a,b) in rules.items()}
    while rules:
        accessible = markable(rules,0)&markable(rules,1)
        allowed = [name for name,(a,b) in rules.items() if accessible.issuperset(a+b)]
        balanced = set()
        for size in range(1,min(len(places)+1,len(allowed))+1):
            for support in combinations(allowed,size):
                if not balanced.issuperset(support) and positive_circuit([delta[g] for g in support]):
                    balanced.update(support)
        if len(balanced)==len(rules):
            break
        rules = {g:rules[g] for g in allowed if g in balanced}
    return list(rules)


def find_return(data,allowed,required=None):
    """Find a positive return containing at least one of the required rules."""
    places = data['point_gates']
    def vector(port):
        c = Counter(port)
        return tuple(c[p] for p in places)
    changes = [(g,*map(vector,data['rules'][g])) for g in allowed]
    zero = (0,)*len(places)
    start = (zero,False)
    parent = {start:None}
    pending = deque([start])
    while pending:
        state = pending.popleft()
        at,seen = state
        for name,a,b in changes:
            if any(x<y for x,y in zip(at,a)):
                continue
            dest = tuple(x-y+z for x,y,z in zip(at,a,b))
            nxt = dest,seen or required is None or name in required
            if nxt==(zero,True):
                path = [name]
                while state!=start:
                    state,step = parent[state]
                    path.append(step)
                return path[::-1]
            if nxt not in parent:
                parent[nxt] = state,name
                pending.append(nxt)
    raise AssertionError('a certified zero cycle must have a finite run')


def movie(data,path):
    live,charts,seams = [],[],[]
    gates = {}
    for i,name in enumerate(path):
        a,b = data['rules'][name]
        word = []
        for j,colour in enumerate(a):
            k = next(k for k in range(j,len(live)) if live[k][1]==colour)
            while k>j:
                live[k-1],live[k] = live[k],live[k-1]
                word.append(k)
                k -= 1
        if i:
            seams.append(word)
        marker = 's'+str(i)
        new = [(f'w{i}_{j}',g) for j,g in enumerate(b)]
        gates[marker] = ['x','','']
        gates.update({g:['x','',''] for g,_ in new})
        rows = lambda block:[(0,g) for g,_ in block]
        charts.append(dict(diagram=[(0,marker),*rows(live[len(a):])],slot=0,
                           input=rows(live[:len(a)]),output=rows(new)))
        live[:len(a)] = new
    assert not live
    result = dict(vertex='x',path='',edges={},gates=gates,charts=charts,seams=seams)
    read_track(dict(result,charts=[dict(c,loop=()) for c in charts]),require_shared_gate=False)
    return result


def analyze(data,witness=False):
    allowed = return_rules(data)
    result = dict(return_rules=allowed,raw_degree_six_nonfilling_at_empty_ends=bool(allowed))
    if witness and allowed:
        path = find_return(data,allowed)
        result.update(program=path,movie=movie(data,path))
    return result


def audit():
    from semistrict_surface_scalar_leaves import classify
    from semistrict_surface_spherical_relations import analyze as spheres
    options = [(a,b) for a in (None,'a','b') for b in (None,'a','b')]
    checked = 0
    for size in range(len(options)+1):
        for subset in combinations(options,size):
            unary = {str(i):pair for i,pair in enumerate(subset)}
            net = {g:([a] if a else [],[b] if b else []) for g,(a,b) in unary.items()}
            data = dict(point_gates=['a','b'],rules=net)
            assert bool(return_rules(data))!=classify(dict(data,rules=unary))['all_degree_six_boundaries_fill']
            checked += 1
    # Balanced but never initially enabled, and enabled on both sweeps
    # with no positive balance (surplus token paired in the wrong ratio).
    for rules in ({'copy':(['a'],['a'])},{'birth':([],['a','b']),'death':(['a','b','b'],[])}):
        assert not return_rules(dict(point_gates=['a','b'],rules=rules))
    # Removing the only producer of b makes the formerly balanced b-cycle
    # inaccessible. One support-filter pass would incorrectly retain it.
    stages = [('','aa'),('b','bb'),('','ab'),('b',''),('bb','bb')]
    assert not return_rules(dict(point_gates=['a','b'],rules={
        str(i):(list(a),list(b)) for i,(a,b) in enumerate(stages)}))
    data = dict(point_gates=['a','b'],rules={'birth':([],['a','b']),'consume_b':(['b','b'],[]),
                'consume_a':(['a','a'],[]),'stuck':(['z'],['z'])})
    data['point_gates'].append('z')
    r = analyze(data,True)
    assert set(r['return_rules'])=={'birth','consume_a','consume_b'} and len(r['program'])==4
    assert any(r['movie']['seams'])
    # This program contains a genuine cycle in its incidence graph.
    answer = spheres(r['movie'])
    assert answer['betti']==[1,1,1]
    assert analyze(dict(point_gates=[],rules={'free':([],[])}),True)['program']==['free']
    print(f'{checked} unary decisions agree; exact support and a signed four-event branching return checked')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--witness',action='store_true')
    args = parser.parse_args()
    if args.input:
        print(json.dumps(analyze(json.loads(args.input.read_text()),args.witness),indent=2))
    else:
        audit()
