"""Maximal number of through children beside a probe over all one-root histories.

Input is the closed-port presentation format, with optional initial and final
closed positioned forests at vertex (default empty). Null maximum means that
no free local trajectory is possible in any reachable face.
"""
from argparse import ArgumentParser
from collections import defaultdict
from functools import lru_cache
import json
from pathlib import Path

from semistrict_surface_closed_returns import Templates, matching_size
from semistrict_surface_gate_forests import Presentation


class Trajectories:
    def __init__(self,rules,pairs):
        self.graph = defaultdict(set)
        self.births,self.deaths = set(),set()
        self.isolated = False
        # Even is the new core, odd is the same core ready for consumption.
        for a,b in pairs:
            self.graph[2*a].add(2*b+1)
        for a,b in rules:
            if a and b:
                self.graph[2*a[0]+1].add(2*b[0])
            elif b:
                self.births.add(2*b[0])
            elif a:
                self.deaths.add(2*a[0]+1)
            else:
                self.isolated = True
        self.reaches = lru_cache(None)(self._reaches)
        self.feasible = lru_cache(None)(self._feasible)
        self.created = set().union(*(self.reaches(b) for b in self.births))
        self.returns = self.isolated or bool(self.deaths & self.created)

    def _reaches(self,s):
        seen,todo = {s},[s]
        while todo:
            for t in self.graph[todo.pop()]:
                if t not in seen:
                    seen.add(t)
                    todo.append(t)
        return seen

    def can(self,s,t):
        if s is None:
            return t is None or t in self.created
        choices = self.reaches(s)
        return bool(choices & self.deaths) if t is None else t in choices

    def _feasible(self,left,right):
        a = [2*i for i in left]+[None]*len(right)
        b = [2*j+1 for j in right]+[None]*len(left)
        return matching_size([[j for j,t in enumerate(b) if self.can(s,t)] for s in a])==len(a)

    def through(self,left,right):
        return matching_size([[j for j,t in enumerate(right) if self.can(2*s,2*t+1)]
                              for s in left])

    def uses(self,left,right,pair):
        a,b = pair
        for i in range(len(left)+1):
            s = 2*left[i] if i<len(left) else None
            if not self.can(s,2*a):
                continue
            for j in range(len(right)+1):
                t = 2*right[j]+1 if j<len(right) else None
                if self.can(2*b+1,t) and self.feasible(left[:i]+left[i+1:],right[:j]+right[j+1:]):
                    return True
        return False


def profile(data):
    lib = Templates(data)
    rules = defaultdict(list)
    def forest(x,row):
        model = Presentation(dict(data,vertex=x,path='',rules={},diagram=row))
        if model.sweep(x,'',row):
            raise ValueError('expected a closed positioned forest')
        return lib.forest(x,row)
    for x,a,b in data['rules'].values():
        start,end = forest(x,a),forest(x,b)
        if max(len(start),len(end))>1:
            raise ValueError('expected at most one outer component per rule side')
        rules[x].append((start,end))
    x = data['vertex']
    exterior = (x,forest(x,data.get('initial',[])),forest(x,data.get('final',[])))
    children = {}
    for i,(x,core,slots) in enumerate(lib.node):
        for j,(y,other,ends) in enumerate(lib.node):
            if (x,core)==(y,other):
                assert [(k,t) for k,t,_ in slots]==[(k,t) for k,t,_ in ends]
                children[i,j] = [(t,a,b) for (_,t,a),(_,_,b) in zip(slots,ends)]
    enabled = {(i,i) for i in range(len(lib.node))}
    while True:
        by_object = defaultdict(list)
        for pair in enabled:
            by_object[lib.node[pair[0]][0]].append(pair)
        networks = {}
        def net(x):
            if x not in networks:
                networks[x] = Trajectories(rules[x],by_object[x])
            return networks[x]
        more = {p for p,faces in children.items() if p not in enabled
                and all(net(t).feasible(a,b) for t,a,b in faces)}
        if not more:
            break
        enabled.update(more)

    x,a,b = exterior
    possible = net(x).feasible(a,b)
    pending = [exterior] if possible else []
    visited,active = set(),[]
    while pending:
        local = pending.pop()
        if local in visited:
            continue
        visited.add(local)
        x,a,b = local
        n = net(x)
        if n.returns:
            active.append(dict(object=x,initial_roots=len(a),final_roots=len(b),
                               max_through=n.through(a,b)))
        for pair in by_object[x]:
            if children[pair] and n.uses(a,b,pair):
                pending.extend(children[pair])
    maximum = max((r['max_through'] for r in active),default=None)
    return dict(reachable=possible,max_punctures_beside_probe=maximum,
                named_degree_five_nonfilling=bool(maximum),degree_six_nonfilling=bool(active),
                probe_face_profiles=sorted(active,key=lambda r:tuple(r.values())))


def audit():
    from semistrict_surface_port_arity import circuit_ports
    # Explicit token runs record provenance and a distinguished internal
    # change. Compare the matching and outside tests at every final cut.
    from collections import deque
    ends = [(),(0,),(1,),(0,1)]
    trials = 0
    for mask in range(16):
        rules = [r for i,r in enumerate([((),(0,)),((1,),()),((0,),(1,)),((1,),(0,))]) if mask & (1<<i)]
        pairs = [(0,0),(0,1),(1,1)]
        n = Trajectories(rules,pairs)
        transitions = [(2*a,2*b+1,(a,b)==(0,1)) for a,b in pairs]
        transitions.extend((2*a[0]+1 if a else None,2*b[0] if b else None,False) for a,b in rules)
        for left in ends:
            initial = (tuple((2*i,True) for i in left),False)
            seen,todo = {initial},deque([initial])
            observed = {}
            while todo:
                tokens,used = todo.popleft()
                if all(i%2 for i,_ in tokens):
                    end = tuple(i//2 for i,_ in tokens)
                    rank,hit = observed.get(end,(-1,False))
                    observed[end] = max(rank,sum(tag for _,tag in tokens)),hit or used
                for a,b,mark in transitions:
                    choices = [j for j,(t,_) in enumerate(tokens) if t==a] if a is not None else [len(tokens)]
                    for j in choices:
                        row = list(tokens)
                        tag = row.pop(j)[1] if j<len(row) else False
                        if b is not None:
                            row.append((b,tag))
                        child = tuple(sorted(row)),used or mark
                        if len(row)<=len(left)+3 and child not in seen:
                            seen.add(child)
                            todo.append(child)
            for right in ends:
                rank,hit = observed.get(right,(-1,False))
                assert n.feasible(left,right)==(rank>=0)
                if rank>=0:
                    assert n.through(left,right)==rank
                assert n.uses(left,right,(0,1))==hit
                trials += 1
    print(f'{trials} layered endpoint queries agree with explicit marked token runs.')
    for value in (False,True):
        d = circuit_ports([value,['and',0,0]])
        d['gates']['p'] = ['y','','']
        for name,side in [('open',2),('close',1)]:
            d['rules'][name][side].insert(1,(1,'p'))
        d['rules'].update(exterior=['x',[],[]],probe=['y',[],[]])
        ans = profile(d)
        assert ans['degree_six_nonfilling'] and ans['max_punctures_beside_probe']==(2 if value else 0)
    # A template may be present at an intermediate cut without ever being
    # the shape at either endpoint of a reachable enclosing lifetime.
    d = dict(vertex='x',edges={'f':['x','y'],'g':['y','x']},
             gates=dict(B=['x','','fg'],D=['x','fg',''],z=['x','',''],p=['y','',''],q=['y','','']))
    def lens(contents):
        return [(0,'B')]+[(1,g) for g in contents]+[(0,'D')]
    blank,full = lens([]),lens('ppp')
    d['rules'] = dict(open=['x',[],blank],close=['x',blank,[]],dummy=['x',[(0,'z')],full],
                      birth=['y',[],[(0,'p')]],death=['y',[(0,'p')],[]])
    assert profile(d)['max_punctures_beside_probe']==0
    d['rules']['close'][1] = full
    # All final points are births; the length of the two lists differs.
    assert profile(d)['max_punctures_beside_probe']==0
    d['rules']['open'][2] = lens('ppq')
    # The q has no death and is trapped. A change to the other colour
    # makes all three positions persist despite their distinct end colours.
    assert profile(d)['max_punctures_beside_probe'] is None
    d['rules']['colour'] = ['y',[(0,'q')],[(0,'p')]]
    assert profile(d)['max_punctures_beside_probe']==3
    d['rules']['colour'] = ['y',[(0,'q')],[]]
    assert profile(d)['max_punctures_beside_probe']==2
    # Exterior forests use the same maximum matching and an actual
    # surviving child inside the initial/final lens can dominate its rank.
    d['initial'],d['final'] = lens('qqq'),lens('ppp')
    assert profile(d)['max_punctures_beside_probe']==2  # newly born lens is eligible
    del d['rules']['open']
    assert profile(d)['max_punctures_beside_probe']==0  # outer x has no return
    d['rules']['colour'] = ['y',[(0,'q')],[(0,'p')]]
    assert profile(d)['max_punctures_beside_probe']==3
    # Check the maximum against the actual positioned nested history from
    # Response 143. Its two persistent interior lists have different sizes.
    from semistrict_surface_face_obstructions import obstructions, pockets
    movie = pockets()
    actual = obstructions(movie)
    d = dict(movie,rules={str(i):['x',c['input'],c['output']] for i,c in enumerate(movie['charts'])})
    expected = max(r['punctures'] for r in actual['faces'] if r.get('probes'))
    assert profile(d)['max_punctures_beside_probe']==expected==3
    print('Circuit outcomes separate degree five under a positive return promise.')
    print('Whole-lifetime tests give no probe, rank zero, two or three at occupied ports and fixed ends.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(profile(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
