"""Decide one-sided three-strand surface comparisons, including named strands."""
from argparse import ArgumentParser
from collections import deque
from fractions import Fraction
from math import lcm
from itertools import combinations, permutations, product

from semistrict_surface_crossing_insertion import three_strand_surface
from semistrict_surface_shared_edge import inverse

# A standard crossing lifted to syllables in PSL(2,Z) = <p,q | p^2=q^3=1>.
MODULAR = {1:(-2,1), 2:(1,-2), -1:(1,2), -2:(2,1)}


def act(order, g):
    if abs(g)==1:
        return order[::-1]
    return order[1:]+order[:1] if g>0 else order[-1:]+order[:-1]


class ThreeStrandOrders:
    def __init__(self, origin):
        self.orbit = sorted(set(permutations(origin)))
        self.hubs = {}
        self.arc = {}
        self.factor = {}
        self.period = {}
        graph = {}
        for o in self.orbit:
            for g in (1,2):
                cycle = {o,act(o,g),act(o,-g)}
                hub = (g,min(cycle))
                self.hubs[o,g] = hub
                graph.setdefault(o,[]).append(hub)
                graph.setdefault(hub,[]).append(o)
                if len(cycle)==1 and hub not in self.factor:
                    j = len(self.period)+1
                    self.factor[hub] = j
                    self.period[j] = g+1
        start = tuple(origin)
        tree = set()
        seen = {start}
        todo = deque([start])
        while todo:
            u = todo.popleft()
            for v in graph[u]:
                if v not in seen:
                    seen.add(v)
                    todo.append(v)
                    tree.add(frozenset((u,v)))
        for (o,g),hub in self.hubs.items():
            if frozenset((o,hub)) not in tree:
                j = len(self.period)+1
                self.period[j] = 0
                self.arc[o,g] = j

    def path(self, origin, crossings):
        o = tuple(origin)
        word = []
        for crossing in crossings:
            for step in MODULAR[crossing]:
                g = abs(step)
                hub = self.hubs[o,g]
                if (o,g) in self.arc:
                    word.append(self.arc[o,g])
                if hub in self.factor:
                    word.append(self.factor[hub] if step>0 else -self.factor[hub])
                o = act(o,step)
                if (o,g) in self.arc:
                    word.append(-self.arc[o,g])
        return o,tuple(word)


def cyclic(word, periods):
    runs = []
    def add(g,n):
        if runs and runs[-1][0]==g:
            n += runs.pop()[1]
        order = periods[g]
        if order:
            n %= order
            if n > order//2:
                n -= order
        if n:
            runs.append((g,n))
    for x in word:
        add(abs(x),1 if x>0 else -1)
    while len(runs)>1 and runs[0][0]==runs[-1][0]:
        add(*runs.pop(0))
    w = tuple(x for g,n in runs for x in (g if n>0 else -g,)*abs(n))
    return min((w[i:]+w[:i] for i in range(len(w))), default=())


def planar(boundaries, packets, size):
    boundary_next,packet_next = {},{}
    for cycles,perm in ((boundaries,boundary_next),(packets,packet_next)):
        for cycle in cycles:
            for i,j in zip(cycle,cycle[1:]+cycle[:1]):
                perm[i] = j
    seen = set()
    faces = 0
    for i in range(size):
        if i not in seen:
            faces += 1
            while i not in seen:
                seen.add(i)
                i = boundary_next[packet_next[i]]
    seen.clear()
    components = 0
    for i in range(size):
        if i not in seen:
            components += 1
            todo = [i]
            while todo:
                j = todo.pop()
                if j not in seen:
                    seen.add(j)
                    todo.extend((boundary_next[j],packet_next[j]))
    return len(boundaries)+len(packets)-size+faces == 2*components


def sphere_equation(words, periods):
    curves = [w for v in words if (w:=cyclic(v,periods))]
    if len(curves)<2:
        return not curves
    if len(curves)==2:
        return curves[0] == cyclic(inverse(curves[1]),periods)
    letters, boundaries = [],[]
    for w in curves:
        n = len(letters)
        letters.extend(w)
        boundaries.append(tuple(range(n,n+len(w))))
    for g,k in periods.items():
        e = letters.count(g)-letters.count(-g)
        if (e%k if k else e):
            return False
    pending = [(list(range(len(letters))),[])]
    while pending:
        remaining,packets = pending.pop()
        if not remaining:
            if planar(boundaries,packets,len(letters)):
                return True
            continue
        i,*rest = remaining
        x = letters[i]
        choices = [(j,) for j in rest if letters[j] == (x if periods[abs(x)]==2 else -x)]
        if periods[abs(x)]==3:
            for j,k in combinations((j for j in rest if letters[j]==x),2):
                choices.extend(((j,k),(k,j)))
        pending.extend(([j for j in rest if j not in tail],packets+[(i,*tail)]) for tail in choices)
    return False


def placed_rules(orders, rules):
    seen = set()
    for label,l,r in rules:
        for o in orders.orbit:
            for pos in range(4-len(label)):
                if o[pos:pos+len(label)] != tuple(label):
                    continue
                j,s = orders.path(o,tuple(i+pos for i in l))
                k,t = orders.path(o,tuple(i+pos for i in r))
                if j!=k:
                    raise ValueError('declaration faces must be parallel at their named input')
                delta = len(r)-len(l)
                defect = cyclic(t+inverse(s),orders.period)
                if delta or defect:
                    seen.add((delta,defect))
    return sorted(seen)


def positive_grading(rows):
    """Find an integral linear functional positive on all rows by exact elimination."""
    dimension = len(rows[0])
    bounds = [(row,1) for row in rows]
    def solve(bounds, n):
        if not n:
            return () if all(b<=0 for _,b in bounds) else None
        lower = [(a,b) for a,b in bounds if a[-1]>0]
        upper = [(a,b) for a,b in bounds if a[-1]<0]
        projected = [(a[:-1],b) for a,b in bounds if not a[-1]]
        for a,b in lower:
            for c,d in upper:
                projected.append((tuple(a[-1]*v-c[-1]*u for u,v in zip(a[:-1],c[:-1])),
                                  a[-1]*d-c[-1]*b))
        v = solve(projected,n-1)
        if v is None:
            return None
        def boundary(a,b):
            return Fraction(b-sum(j*k for j,k in zip(a[:-1],v)),a[-1])
        lo = max((boundary(a,b) for a,b in lower),default=None)
        hi = min((boundary(a,b) for a,b in upper),default=None)
        return (*v,lo if lo is not None else hi if hi is not None else 0)
    answer = solve(bounds,dimension)
    if answer is not None:
        denominator = lcm(*(x.denominator for x in answer))
        return tuple(int(x*denominator) for x in answer)
    return None


def raw_bounded(origin, start, target, rules, ceiling):
    if len(target)>ceiling:
        return False
    pending = [start]
    seen = {start}
    while pending:
        w = pending.pop()
        if w==target:
            return True
        o = tuple(origin)
        for i in range(len(w)+1):
            moves = []
            if w[i:i+3] == (1,2,1):
                moves.append((3,(2,1,2)))
            for label,l,r in rules:
                for offset in range(4-len(label)):
                    if o[offset:offset+len(label)]==tuple(label):
                        before = tuple(j+offset for j in l)
                        if w[i:i+len(l)]==before:
                            moves.append((len(l),tuple(j+offset for j in r)))
            for used,after in moves:
                v = w[:i]+after+w[i+used:]
                if len(v)<=ceiling and v not in seen:
                    seen.add(v)
                    pending.append(v)
            if i<len(w):
                j = w[i]-1
                o = o[:j]+(o[j+1],o[j])+o[j+2:]
    return False


def compare(origin, start, target, rules, raw=False):
    orders = ThreeStrandOrders(origin)
    j,s = orders.path(origin,start)
    k,t = orders.path(origin,target)
    if j!=k:
        raise ValueError('old faces must have the same named output')
    placed = placed_rules(orders,rules)
    outer = cyclic(s+inverse(t),orders.period)
    gap = len(target)-len(start)
    if not placed:
        if gap or outer:
            return False
        return raw_bounded(origin,start,target,rules,len(start)) if raw else True
    def vector(d,w):
        return (d,*(w.count(i)-w.count(-i) for i,p in orders.period.items() if not p))
    vectors = [vector(d,w) for d,w in placed]
    grade = positive_grading(vectors)
    if grade is None:
        raise ValueError('no additive rational grading is positive on all nontrivial placed declarations')
    def height(v):
        return sum(a*b for a,b in zip(grade,v))
    cost = list(map(height,vectors))
    assert min(cost)>0
    budget = height(vector(gap,inverse(outer)))
    if budget<0:
        return False
    if raw:
        steps = budget//min(cost)
        ceiling = len(start)+steps*max(0,max(d for d,_ in placed))
        return raw_bounded(origin,start,target,rules,ceiling)
    pending = [(budget,gap,0,[])]
    while pending:
        remaining,delta,first,factors = pending.pop()
        if not remaining:
            if delta==0 and sphere_equation([outer,*factors],orders.period):
                return True
            continue
        pending.extend((remaining-cost[i],delta-d,i,factors+[v])
                       for i,(d,v) in enumerate(placed[first:],first) if cost[i]<=remaining)
    return False


def check():
    # Orevkov's independent 3-braid decision includes all signed conjugates of one crossing.
    words = [w for n in range(5) for w in product((1,2),repeat=n)]
    insert = [('AA',(),(1,))]
    for s,t in product(words,repeat=2):
        assert compare('AAA',s,t,insert) == three_strand_surface(s,t)
        assert compare('AAA',t,s,[('AA',(1,),())]) == three_strand_surface(s,t)
    assert not sphere_equation([(1,2,-1,-2),(3,),(-3,)],{1:0,2:0,3:0})
    assert sphere_equation([(1,2,-1,-2),(1,),(-1,)],{1:0,2:0})
    assert sphere_equation([(1,),(1,),(1,)],{1:3})
    assert sphere_equation([(1,),(-1,)],{1:3})
    named = 0
    for origin,want in [('ABC',[0,0]),('AAB',[0,2]),('AAA',[2,3])]:
        orders = ThreeStrandOrders(origin)
        assert sorted(orders.period.values())==want
        for o in orders.orbit:
            for v in words:
                j,s = orders.path(o,v+(1,2,1))
                k,t = orders.path(o,v+(2,1,2))
                assert j==k and not cyclic(s+inverse(t),orders.period)
                named += 1
    assert compare('ABC',(),(1,1),[('BA',(),(1,1))])
    assert not compare('ABC',(),(2,2),[('BA',(),(1,1))])
    assert compare('AAB',(),(2,2),[('BA',(),(1,1))])
    assert not compare('AAB',(),(1,1),[('BA',(),(1,1))])
    mixed = [('AB',(),(1,1)),('BC',(1,1),())]
    assert compare('ABC',(2,2),(1,1),mixed,raw=True)
    assert compare('ABC',(2,2),(1,1),mixed)
    assert not compare('ABC',(1,1),(2,2),mixed)
    shifted = [('ABC',(1,1),(2,2))]
    assert compare('ABC',(1,1),(2,2),shifted)
    assert not compare('ABC',(2,2),(1,1),shifted)
    assert positive_grading([(1,0),(0,1),(-1,-1)]) is None
    repaired = [('AAA',(2,1,2),(1,2,1)),*insert]
    for w in words:
        for v in words:
            assert compare('AAA',w,v,repaired,raw=True) == three_strand_surface(w,v)
    assert not compare('ABC',(),(1,1),[('BA',(),(1,1))],raw=True)
    assert not compare('AAA',(2,1,2),(1,2,1),[],raw=True)
    print(f'{2*len(words)**2} signed-order decisions agreed with the independent three-strand insertion test.')
    print(f'{named} named path and braid checks; the three types of stabilizer and square placements verified.')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--at',help='three scalar names in their input order')
    parser.add_argument('--faces',nargs=2,metavar=('SOURCE','TARGET'),default=('',''))
    parser.add_argument('--raw',action='store_true',help='decide raw inhabitation at the same boundary')
    parser.add_argument('--rule',action='append',default=[],metavar='NAMES:SOURCE:TARGET')
    args = parser.parse_args()
    if args.at is None:
        check()
        return
    try:
        if len(args.at)!=3:
            raise ValueError('exactly three input names are required')
        def letters(s,n):
            if set(s)-set('12'[:max(n-1,0)]):
                raise ValueError('crossing position outside the declared width')
            return tuple(map(int,s))
        rules = []
        for rule in args.rule:
            name,l,r = rule.split(':')
            if not 1<=len(name)<=3:
                raise ValueError('a placed rule has width one, two or three')
            rules.append((name,letters(l,len(name)),letters(r,len(name))))
        result = compare(args.at,*(letters(w,3) for w in args.faces),rules,raw=args.raw)
    except ValueError as exc:
        parser.error(str(exc))
    print(('raw' if args.raw else 'surface') + (' comparison exists' if result else ' comparison absent'))


if __name__=='__main__':
    main()
