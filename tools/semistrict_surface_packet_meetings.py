"""Decide scalar degree-four movies with length-preserving polygon occurrences."""
from argparse import ArgumentParser
from collections import defaultdict
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_meridian_transport import content, meridian, prod, quasi
from semistrict_surface_polygon_grades import network
from semistrict_surface_scalar_meetings import Meetings, ReflectionQuotient, exhausted, hurwitz, meeting_path
from semistrict_surface_shared_edge import inverse
from semistrict_surface_signed_width_two import Movies, Presentation, Rule


@dataclass(frozen=True)
class Packet:
    before: tuple
    atoms: tuple

    @property
    def after(self):
        return prod(self.before, *self.atoms)

    @property
    def names(self):
        return tuple(meridian(a)[1] for a in self.atoms)


def cut(frame, i, k):
    return Packet(prod(*frame[:i]), frame[i:i+k])


def transport(s, t):
    if s == t:
        return True
    if s.names != t.names:
        return False
    # All packet meridians must share the conjugator of the negative gains.
    u, e = meridian(s.atoms[0])
    v, _ = meridian(t.atoms[0])
    d = content(v).get(e, 0) - content(u).get(e, 0)
    neg = prod(u, ((e if d >= 0 else -e),)*abs(d), inverse(v))
    if any(prod(a, neg) != prod(neg, b) for a,b in zip(s.atoms, t.atoms)):
        return False
    total = prod(inverse(s.after), t.after)
    gain = content(total)
    if any(x in s.names or k != 1 for x,k in gain.items()):
        return False
    return quasi(neg) and quasi(prod(inverse(neg), total))


def compatible(s, t):
    if set(s.names).intersection(t.names):
        return False
    return quasi(prod(inverse(s.after), t.before)) or quasi(prod(inverse(t.after), s.before))


class PacketMeetings(Meetings):
    def __init__(self, n, anchors, packets):
        self.packets = packets
        super().__init__(n, anchors)

    def record(self, frame):
        names = tuple(meridian(a)[1] for a in frame)
        available = {}
        for packet in self.packets:
            i = names.index(packet[0])
            if names[i:i+len(packet)] == packet:
                available[packet] = cut(frame, i, len(packet))
        for (e,s),(f,t) in combinations(available.items(), 2):
            if set(e).isdisjoint(f):
                self.at[e,f][s,t] = self.at[f,e][t,s] = frame


def read(n, reading, graph):
    frame = tuple((e+1,) for e in range(n))
    cuts, anchors = {}, []
    for i,p in reading:
        if p is None:
            frame = hurwitz(frame, i, True)
        else:
            s = cut(frame, i, len(graph[p][1]))
            cuts[s.names,p] = s
            anchors.append(frame)
    return cuts, anchors, frame


def replay(source, target, meetings):
    order, latest = list(source), source.copy()
    for i,frame in meetings:
        n = len(frame)
        names = tuple(meridian(a)[1] for a in frame)
        assert sorted(names) == list(range(1,n+1)) and prod(*frame) == tuple(range(1,n+1))
        e,f = order[i:i+2]
        assert set(e[0]).isdisjoint(f[0])
        for m in (e,f):
            s = cut(frame, names.index(m[0][0]), len(m[0]))
            assert s.names == m[0] and transport(latest[m], s)
            latest[m] = s
        order[i:i+2] = f,e
    assert order == list(target) and all(transport(latest[m], target[m]) for m in target)


def finite_test(n, readings, source, target, modulus):
    if modulus < 1:
        raise ValueError('expected positive reflection modulus')
    group = ReflectionQuotient(range(n), modulus)
    orders = [tuple(e+1 for _,e in h) for h in group.histories]
    charts, gains = {}, defaultdict(set)
    for packet in {e for e,_ in source}:
        k = len(packet)
        orbit = {}
        edges = []
        for h,names in enumerate(orders):
            slot = names.index(packet[0])
            if names[slot:slot+k] != packet or h in orbit:
                continue
            component = packet,h
            todo = [h]
            orbit[h] = component
            while todo:
                now = todo.pop()
                for g,nxt in group.edges[now]:
                    j = abs(g)-1
                    if (j+2 <= slot or j >= slot+k) and nxt not in orbit:
                        orbit[nxt] = component
                        todo.append(nxt)
                if slot+k < n:
                    for sign in (1,-1):
                        nxt = now
                        for j in reversed(range(slot,slot+k)):
                            nxt = group.neighbors[nxt][sign*(j+1)]
                        edges.append((component,nxt))
        charts[packet] = orbit
        for c,h in edges:
            gains[c].add(orbit[h])
    @lru_cache(None)
    def destinations(c):
        # Every gain increases the packet's temporal slot, including in the quotient.
        return {c}.union(*(destinations(d) for d in gains[c]))
    def positions(reading,marks):
        out,h = {},0
        names = iter(marks)
        for i,p in reading:
            if p is None:
                h = group.neighbors[h][i+1]
            else:
                m = next(names)
                out[m] = charts[m[0]][h]
        return out
    a,b = (positions(r,m) for r,m in zip(readings,(source,target)))
    if any(b[m] not in destinations(c) for m,c in a.items()):
        return False
    at = defaultdict(dict)
    for e,f in combinations(charts,2):
        if set(e).isdisjoint(f):
            for h in charts[e].keys() & charts[f].keys():
                c,d = charts[e][h],charts[f][h]
                at[e,f][c,d] = at[f,e][d,c] = h
    return meeting_path(at,a,b,lambda c,d: d in destinations(c)) is not None


def supported(model, source, actions):
    sites = {i for i,_ in source}
    return (not model.attachments and len(sites) <= 1 and
            all(not any(model.pres.marks[e]) for _,e in source) and
            all(not r.path and len(r.source) == len(r.target) and
                all(not any(model.pres.marks[e]) for _,e in r.source+r.target)
                for r in (model.pres.rules[rid] for rid in {a for a,_ in actions if a != 'swap'})))


def decide(model, source, first, second, radius=None, moduli=()):
    if radius is not None and radius < 0:
        raise ValueError('expected nonnegative radius')
    if not supported(model, source, (*first,*second)):
        raise ValueError('expected scalar length-preserving polygons at one spatial gap')
    model.pres.walk(model.start,source)
    if model.parse(source,first)[1] != model.parse(source,second)[1]:
        raise ValueError('expected parallel readings')
    n, ids = len(source), {}
    arities = [(len(r.source),len(r.target)) for r in model.pres.rules]
    a,b = [network(source,w,ids,arities,'swap') for w in (first,second)]
    if a[:2] != b[:2]:
        return dict(surface=False,obstruction='named incidence')
    s,aa,total = read(n,a[2],a[1])
    t,bb,other = read(n,b[2],b[1])
    if total != other:
        return dict(surface=False,obstruction='total braid')
    if s.keys() != t.keys() or any(not transport(u,t[p]) for p,u in s.items()):
        return dict(surface=False,obstruction='packet transport')
    order = {m:i for i,m in enumerate(t)}
    inversions = [(p,q) for p,q in combinations(s,2) if order[p] > order[q]]
    if any(all(compatible(c[p],c[q]) for p,q in inversions) for c in (s,t)):
        return dict(surface=True,method='endpoint packet meetings')
    if all(s[p] == t[p] for p in s):
        return dict(surface=False,obstruction='stationary packet meetings')
    for modulus in moduli:
        if not finite_test(n,(a[2],b[2]),s,t,modulus):
            return dict(surface=False,obstruction='finite packet meetings',modulus=modulus)
    chart = PacketMeetings(n, (*aa,*bb), {packet for packet,_ in s})
    r = 0
    while True:
        witness = meeting_path(chart.at,s,t,transport)
        if witness is not None:
            replay(s,t,witness)
            return dict(surface=True,meeting_radius=r,meetings=witness)
        if not chart.frontier or exhausted(r,n,len(s),(n+1)*(1+len(first)+len(second))):
            return dict(surface=False,obstruction='exhausted packet meetings')
        if radius == r:
            return dict(surface=None,meeting_radius=r,frames=len(chart.seen))
        chart.grow()
        r += 1


def checks():
    from itertools import product
    from semistrict_surface_single_polygon import decide as single
    from semistrict_surface_component_braids import cabling
    from semistrict_surface_scalar_meetings import solve as private
    from semistrict_surface_raw_movie_graph import raw_compare

    a = ((0,'a'),)
    rules = [Rule('',a*k,a*k) for k in (1,2,3)]
    model = Movies(Presentation({}, {'a':('','')},rules,{'a':0}),'')
    count = yes = 0
    # Compare every insertion of one polygon in a short braid against the
    # separate cable-and-restrict decision, including internally twisted blocks.
    for n in (3,4):
        src = a*n
        for k in range(2,n+1):
            if k > len(rules):
                continue
            for length in range(4):
                for word in product(range(n-1),repeat=length):
                    w = [('swap',i) for i in word]
                    movies = [w[:s]+[(k-1,i)]+w[s:] for s in range(length+1) for i in range(n-k+1)]
                    for u,v in product(movies,repeat=2):
                        expected = single(model,src,u,v)['surface']
                        result = decide(model,src,u,v,0)
                        assert result['surface'] == expected
                        count += 1
                        yes += expected
    def projected(u,v,n,modulus):
        ids = {}
        data = [network(a*n,w,ids,[(k,k) for k in (1,2,3)],'swap') for w in (u,v)]
        assert data[0][:2] == data[1][:2]
        s,t = [read(n,d[2],d[1])[0] for d in data]
        return finite_test(n,(data[0][2],data[1][2]),s,t,modulus)
    # Keep the first packet meridian and both boundary cuts fixed while twisting
    # two other internal members. Positive movies have the same total braid.
    w = [('swap',1)]*2
    assert decide(model,a*4,[(2,0)]+w,w+[(2,0)])['obstruction']=='packet transport'
    assert not projected([(2,0)]+w,w+[(2,0)],4,3)
    u,v = [(1,0),(1,2)],[(1,2),(1,0)]
    assert decide(model,a*4,u,v)['surface'] and raw_compare(model,a*4,u,v)['raw']
    assert model.compare(a*4,u,v)['surface']

    # Cable each original strand by its own positive size, replacing a private
    # update by a polygon on all its copies. Lift a meeting certificate as well.
    def lift(movie,sizes):
        order, out = list(range(len(sizes))), []
        for name,i in movie:
            pos = sum(sizes[e] for e in order[:i])
            if name=='X':
                face = [(None,0,sizes[order[i]]),(None,sizes[order[i]],sizes[order[i]]+sizes[order[i+1]])]
                out += [('swap',pos+g-1) for g in cabling(face,(1,))]
                order[i:i+2] = order[i+1], order[i]
            else:
                out.append((sizes[order[i]]-1,pos))
        return out
    def movie(tokens):
        return [('X', x-1) if x>0 else ('p', -x) for x in tokens]+[('X',0)]*4
    left = movie((0,2,1,0,3,2,1,-3,3))
    right = movie((2,3,-3,1,2,3,0,-3,1))
    data = dict(edges={}, initial=[], start_vertex=0, scalar_at={'s':0}, marks={'s':[[],[]]},
                higher=[{'p':['s','s']}],history=[(0,'s')]*4,source=left,target=right)
    expected = private(data,3)
    assert expected['surface_filler'] and expected['meeting_radius']==3
    sizes = (2,1,1,1)
    x,y = lift(left,sizes),lift(right,sizes)
    assert decide(model,a*5,x,y,0)['surface'] is None
    result = decide(model,a*5,x,y,4,(1,3))
    assert result['surface'] and result['meeting_radius']>0, result
    raw = raw_compare(model,a*5,x,y)['raw']
    return dict(lifted_raw=raw,single_queries=count,positive=yes,raw_packet_exchange=True,lifted_radius=result['meeting_radius'],
                lifted_meetings=len(result['meetings']))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    parser.add_argument('--radius',type=int)
    parser.add_argument('--modulus',type=int,action='append',default=[])
    args = parser.parse_args()
    if args.query:
        q = json.loads(args.query.read_text())
        if q.get('attachments'):
            raise ValueError('expected a 3-computad')
        rules = [Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        model = Movies(Presentation(q['edges'],q['marks'],rules,q.get('mark_roots')),q['start'])
        source = tuple(map(tuple,q['source']))
        model.pres.walk(model.start,source,q.get('vertex'))
        result = decide(model,source,q['first'],q['second'],args.radius,args.modulus)
    else:
        result = checks()
    print(json.dumps(result))
