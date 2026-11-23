"""Factor positioned private movies into simple braid windows at common pure gaps.

--faces FILE uses private_movies format. A null surface answer leaves the
comparison open. Windows list the mark offsets and common braid lengths.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from semistrict_surface_acyclic_private_movies import Traces
from semistrict_surface_braid_reflection import follow
from semistrict_surface_history_group import inv
from semistrict_surface_one_step_reflection import quotient,reverse_signed
from semistrict_surface_private_braid_transport import connectors
from semistrict_surface_private_histories import closure,solve as validate
from semistrict_surface_private_simple_braid import read,solve as simple_test
from semistrict_surface_single_power import coprime_parts,output_order,spellings


def join(a,b):
    turned = reverse_signed(inv(a)+b)
    split = next((i for i,x in enumerate(turned) if x<0),len(turned))
    extra,_,_ = coprime_parts(turned[:split],inv(turned[split:]))
    return a+extra


def meet(a,b):
    return coprime_parts(a[::-1],b[::-1])[2][::-1]


def factor(a,b):
    result = quotient(a,b)
    assert result is not None
    return result


class Reading:
    def __init__(self,steps,word):
        self.gaps = connectors(steps)
        self.marks = [tuple(step) for step in steps if step[0]!='X']
        self.keys = [m[:2] for m in word]
        self.before,self.after = [],[]
        at = ()
        for gap in self.gaps:
            self.before.append(at)
            at += gap
            self.after.append(at)

    def piece(self,i,j,left,right):
        result = [('X',g-1) for g in factor(left,self.after[i])]
        for k in range(i,j):
            result.append(self.marks[k])
            gap = self.gaps[k+1] if k+1<j else factor(self.before[j],right)
            result.extend(('X',g-1) for g in gap)
        return result


def seams(a,b):
    used_a,used_b = set(),set()
    for j in range(len(a.keys)+1):
        if used_a==used_b:
            lo = join(a.before[j],b.before[j])
            hi = meet(a.after[j],b.after[j])
            if quotient(lo,hi) is not None:
                yield j,lo,hi
        if j<len(a.keys):
            used_a.add(a.keys[j])
            used_b.add(b.keys[j])


def solve(data):
    h = tuple(map(tuple,data['history']))
    validate({**data,'source':h,'target':h})
    layers = data.get('higher',[])+[{},{}]
    if 'X' in layers[0]:
        raise ValueError('reserved exchange label')
    chart = Traces(data['marks'],*layers[:2])
    a,u,w,old,braid,_ = read(chart,h,data['source'])
    b,v,z,new,other,_ = read(chart,h,data['target'])
    if a!=b:
        raise ValueError('nonparallel old readings')
    braid,other = tuple(braid),tuple(other)
    if u!=v or len(braid)!=len(other) or quotient(braid,other)!=():
        return dict(surface_filler=False,obstruction='unequal erased braids')
    changes = {}
    for p,q in layers[1].values():
        changes.setdefault(p,set()).add(q)
    if old.keys()!=new.keys() or any(new[k] not in closure(p,lambda x:changes.get(x,())) for k,p in old.items()):
        return dict(surface_filler=False,obstruction='private labels')
    a,b = Reading(data['source'],w),Reading(data['target'],z)
    cuts = list(seams(a,b))
    windows = []
    exact = True
    for (i,_,left),(j,right,_) in zip(cuts,cuts[1:]):
        segment = factor(left,right)
        order = output_order(tuple(range(len(h))),segment)
        inversions = sum(x>y for k,x in enumerate(order) for y in order[k+1:])
        if inversions!=len(segment):
            windows.append(dict(marks=[i,j],simple=False))
            exact = False
            continue
        permutation = output_order(tuple(range(len(h))),left)
        phases = [label for _,label in h]
        for key in a.keys[:i]:
            phases[key[0]] = chart.updates[old[key]][1]
        start = tuple((pos,phases[e]) for (pos,_),e in zip(follow(h,left,chart.marks),permutation))
        pieces = [r.piece(i,j,left,right) for r in (a,b)]
        comparison = simple_test(dict(data,history=start,source=pieces[0],target=pieces[1]))
        if comparison['surface_filler'] is not True:
            if comparison['surface_filler'] is False:
                return dict(surface_filler=False,obstruction='projected window',marks=[i,j])
            exact = False
        windows.append(dict(marks=[i,j],simple=True,trace_moves=comparison.get('trace_moves')))
    return dict(surface_filler=True if exact else None,
                seams=[(j,len(lo),len(hi)) for j,lo,hi in cuts],windows=windows)


def checks():
    # Exhaustively compare the lattice calculation with all common prefix
    # elements in pairs of pure gaps (including divisors absent as substrings).
    from semistrict_surface_shared_edge import braid_image
    def prefixes(p):
        return {braid_image(3,q[:i]) for q in spellings(p) for i in range(len(q)+1)}
    braid = (1,2,1,1,2,1)
    reps = spellings(braid)
    seen = {}
    def pref(p):
        if p not in seen:
            seen[p] = prefixes(p)
        return seen[p]
    trials = 0
    for a,b in product(reps,repeat=2):
        for i,j in product(range(4),repeat=2):
            x,y = a[:i],b[:j]
            p,q = a[:i+2],b[:j+2]
            low,high = join(x,y),meet(p,q)
            # Enumerate both intervals by spelling each gap independently.
            def interval(head,tail):
                return {braid_image(3,head+w[:k]) for w in spellings(tail) for k in range(len(w)+1)}
            common = interval(x,a[i:i+2]) & interval(y,b[j:j+2])
            actual = set() if quotient(low,high) is None else interval(low,factor(low,high))
            assert actual==common and pref(high)==pref(p)&pref(q)
            trials += 1
    # Two named scalar strands, independent updates each time they cross.
    h = [(0,'a'),(0,'b')]
    data = dict(edges={},initial=[],start_vertex=0,scalar_at={'a':0,'b':0},
                marks={a:[[],[]] for a in 'ab'},higher=[{a+'!':[a,a] for a in 'ab'}],history=h)
    s,t = [],[]
    for j in range(9):
        p,q = ('a!','b!') if j%2==0 else ('b!','a!')
        s.extend([(p,0),('X',0),(q,0)])
        t.extend([(q,1),('X',0),(p,1)])
    yes=solve(dict(data,source=s,target=t))
    assert yes['surface_filler'] and len(yes['windows'])==9
    assert solve(dict(data,source=t,target=s))['surface_filler'] is False
    # Same double crossing and same mark position, separated by a full twist.
    unknown=solve(dict(data,source=[('a!',0),('X',0),('X',0)],
                       target=[('X',0),('X',0),('a!',0)]))
    assert unknown['surface_filler'] is None
    print(f'{trials} seam intervals agree with direct enumeration; 18 updates in nine '
          'successive scalar crossings, reverse obstruction and a nonsimple residual checked')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--faces',type=Path)
    args=p.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()))))
    else:
        checks()
