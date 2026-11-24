"""Decide shape-preserving positioned polygon comparisons by signed prefix charts."""
from argparse import ArgumentParser
from itertools import combinations
from math import factorial
from pathlib import Path
import json

from semistrict_surface_history_group import inv, realize
from semistrict_surface_packet_meetings import cut, transport
from semistrict_surface_polygon_grades import network
from semistrict_surface_private_prefix_charts import PrefixChart
from semistrict_surface_scalar_meetings import exhausted, hurwitz
from semistrict_surface_signed_width_two import Movies, Presentation, Rule


def supported(model, actions):
    def shape(face):
        return tuple((i,*model.pres.marks[e],model.pres.mark_roots[e]) for i,e in face)
    return not model.attachments and all(shape(r.source) == shape(r.target) for r in
        (model.pres.rules[rid] for rid in {a for a,_ in actions if a!='swap'}))


def old_prefixes(n, graph, reading):
    frame = tuple((e+1,) for e in range(n))
    names = list(range(1,n+1))
    word, cuts, packets, paths = [],{},{},{}
    for i,p in reading:
        if p is None:
            frame = hurwitz(frame,i,True)
            names[i:i+2] = names[i+1],names[i]
            word.append(i+1)
        else:
            size = len(graph[p][1])
            packets[p] = tuple(names[i:i+size])
            cuts[p] = p,cut(frame,i,size)
            paths[p] = tuple(word)
    return frame,packets,cuts,paths


class Chart(PrefixChart):
    def __init__(self,model,root,packets):
        self.model,self.packets = model,packets
        super().__init__(root,model.pres.marks)

    def entries(self,h):
        slots = {e:i for i,(_,e) in enumerate(h)}
        for p,names in self.packets.items():
            i = slots[names[0]]
            result = self.model.named(h,p,i)
            if result is not None:
                yield p,i,result[1]

    def record(self,frame,h,path):
        placed = []
        for p,i,off in self.entries(h):
            size = len(self.packets[p])
            c = p,cut(frame,i,size)
            placed.append(c)
            for block in self.model.prism_words(h,p,i,off):
                after = frame
                for g in block:
                    after = hurwitz(after,abs(g)-1,g>0)
                d = p,cut(after,i+1,size)
                self.gains[c][d] = path,block
        for (p,c),(q,d) in combinations(placed,2):
            if set(self.packets[p]).isdisjoint(self.packets[q]):
                self.meet[(p,c),(q,d)] = self.meet[(q,d),(p,c)] = path

    def verify(self,old,new,steps):
        order,latest = list(old),old.copy()
        total = 0
        def align(p,path):
            nonlocal total
            h,k = self.follow(latest[p]),self.follow(path)
            i = next(i for q,i,_ in self.entries(h) if q==p)
            word = realize(h,k,inv(latest[p])+path,self.ports)
            assert word is not None
            assert all(abs(g)<i or abs(g)>i+len(self.packets[p]) for g in word)
            total += len(word)
            latest[p] = path
        for op,index,path,*args in steps:
            p = order[index]
            align(p,path)
            h = self.follow(path)
            placed = {q:(i,off) for q,i,off in self.entries(h)}
            if op=='gain':
                block, = args
                assert block in self.model.prism_words(h,p,*placed[p])
                latest[p] = path+block
                assert any(q==p and i==placed[p][0]+1 for q,i,_ in self.entries(self.follow(latest[p])))
            else:
                q = order[index+1]
                align(q,path)
                assert q in placed and set(self.packets[p]).isdisjoint(self.packets[q])
                order[index:index+2] = q,p
        assert order == list(new)
        for p,path in new.items():
            align(p,path)
        return total


def decide(model,source,first,second,radius=None):
    if radius is not None and radius<0:
        raise ValueError('expected nonnegative radius')
    if not supported(model,(*first,*second)):
        raise ValueError('expected shape-preserving polygons on a 3-computad')
    model.pres.walk(model.start,source)
    if model.parse(source,first)[1] != model.parse(source,second)[1]:
        raise ValueError('expected parallel movies')
    arities = [(len(r.source),len(r.target)) for r in model.pres.rules]
    n,ids = len(source),{}
    a,b = [network(source,w,ids,arities,'swap') for w in (first,second)]
    if a[:2]!=b[:2]:
        return dict(surface=False,obstruction='named incidence')
    end,names,s,old = old_prefixes(n,a[1],a[2])
    other,more,t,new = old_prefixes(n,b[1],b[2])
    if end!=other or names!=more:
        return dict(surface=False,obstruction='total braid or strand names')
    def can_finish(c,d):
        return transport(c[1],d[1])
    if any(not can_finish(s[p],t[p]) for p in s):
        return dict(surface=False,obstruction='ambient packet transport')
    # The named base retains exact spatial ports. Each shadow rule uses the
    # entire written window, with its actual ordered original strand names.
    ports = {j:model.pres.marks[e] for j,(_,e) in enumerate(source,1)}
    roots = {j:model.pres.mark_roots[e] for j,(_,e) in enumerate(source,1)}
    root = tuple((i,j) for j,(i,_) in enumerate(source,1))
    rules = []
    for p in range(len(a[1])):
        r = model.pres.rules[a[1][p][0]]
        face = tuple((off,e) for (off,_),e in zip(r.source,names[p]))
        rules.append(Rule(r.path,face,face))
    shadow = Movies(Presentation(model.pres.edges,ports,rules,roots),model.start)
    # Forget the other shape-preserving polygons. Each resulting single-mark
    # comparison is necessary even when the original execution orders differ.
    from semistrict_surface_single_polygon import decide as single
    def individual(reading,p):
        return [('swap' if q is None else p,i) for i,q in reading if q is None or q==p]
    if list(s)!=list(t):
        for p in s:
            result = single(shadow,root,individual(a[2],p),individual(b[2],p),0)
            if result['surface'] is False:
                return dict(surface=False,obstruction='individual positioned window',polygon=p)
    chart = Chart(shadow,root,names)
    frame = tuple((e+1,) for e in range(n))
    for w in set(old.values()) | set(new.values()):
        f = frame
        for g in w:
            f = hurwitz(f,g-1,True)
        chart.record(f,chart.follow(w),w)
    m = len(s)
    meetings = (m*max(0,n-1)+1)*m*(m-1)//2
    spatial = len(model.start)+sum(len(out) for _,out in ports.values())
    vertices = factorial(n)*(spatial+1)**n
    padding = (2*vertices+n+2)**2*(meetings+m*n+2)*(n+1)
    size = padding+len(first)+len(second)
    r = 0
    while True:
        proof = chart.search(s,t,can_finish)
        if proof is not None:
            passive = chart.verify(old,new,proof)
            return dict(surface=True,steps=proof,passive_steps=passive,radius=r)
        if not chart.layer or exhausted(r,n,m,size):
            return dict(surface=False,obstruction='exhausted positioned packet charts')
        if r==radius:
            return dict(surface=None,radius=r,frames=len(chart.seen))
        chart.grow()
        r += 1


def checks():
    from itertools import permutations,product
    from semistrict_surface_single_polygon import expand
    from semistrict_surface_raw_movie_graph import raw_compare

    # Connected and distinct spatial supports make the signed record graph
    # finite and thin, supplying an independent complete comparison.
    ab = ((0,'a'),(1,'b'))
    cd = ((0,'c'),(1,'d'))
    edges = {e:(i,i+1) for i,e in enumerate('fghi')}
    marks = {e:(f,f) for e,f in zip('abcdABCD','fghifghi')}
    rules = [Rule('fg',ab,((0,'A'),(1,'B'))),Rule('hi',cd,((0,'C'),(1,'D')))]
    model = Movies(Presentation(edges,marks,rules),'fghi')
    pairs = positive = 0
    from collections import defaultdict
    from random import Random
    rng = Random(228)
    for seq in permutations('abcd'):
        src = tuple(('abcd'.index(e),e) for e in seq)
        paths = defaultdict(list)
        todo = [(src,(),0)]
        while todo:
            h,w,m = todo.pop()
            if m==2:
                paths[h].append(w)
            for i in range(len(h)):
                nxt = model.swap(h,i,True)
                if nxt is not None:
                    todo.append((nxt,w+(('swap',i),),m))
                for p in (0,1):
                    at = model.named(h,p,i)
                    if at is not None:
                        todo.append((at[0],w+((p,i),),m+1))
        for choices in paths.values():
            sample = rng.sample(choices,min(5,len(choices)))
            for u,v in product(sample,repeat=2):
                result = decide(model,src,u,v)['surface']
                assert result == model.compare(src,u,v)['surface']
                pairs += 1
                positive += result

    # The two constituents fit past b separately, but the whole fk window
    # intersects its kg input. Replacing that spectator by c on g clears it.
    marks = {'a':('f','f'),'b':('kg','kg'),'c':('g','g'),'d':('h','h')}
    edges = {e:(i,i+1) for i,e in enumerate('fkgh')}
    aa = ((0,'a'),)*2
    d = ((0,'d'),)
    guarded = Movies(Presentation(edges,marks,[Rule('fk',aa,aa),Rule('h',d,d)]),'fkgh')
    for pos,e in ((1,'b'),(2,'c')):
        src = ((pos,e),(0,'a'),(0,'a'),(3,'d'))
        u = [('swap',0),('swap',1),(0,0),(1,3)]
        v = [(1,3),(0,1),('swap',0),('swap',1)]
        answer = decide(guarded,src,u,v,4)
        assert answer['surface'] == (e=='c') and answer['surface']==raw_compare(guarded,src,u,v)['raw']

    # Two overlapping packets must retain the execution order on the shared
    # strand. A third operation is disjoint and can move across both.
    ab,bc = ((0,'a'),(1,'b')),((0,'B'),(1,'c'))
    marks = {e:(f,f) for e,f in zip('abcdABCD','fghifghi')}
    edges = {e:(i,i+1) for i,e in enumerate('fghi')}
    rules = [Rule('fg',ab,((0,'A'),(1,'B'))),Rule('gh',bc,((0,'b'),(1,'C'))),
             Rule('i',d,((0,'D'),))]
    overlap = Movies(Presentation(edges,marks,rules),'fghi')
    src = tuple(enumerate('abcd'))
    u,v = [(0,0),(1,1),(2,3)],[(2,3),(0,0),(1,1)]
    assert decide(overlap,src,u,v,0)['surface'] and raw_compare(overlap,src,u,v)['raw']

    # A birth can braid at either new spatial gap. Two scalar inputs travel
    # as one polygon and an independent declaration can change the birth label.
    a = ((0,'a'),)
    born = ((0,'u'),)
    marks = {'a':('',''),'b':('',''),'u':('','f'),'v':('','f')}
    rules = [Rule('',a*2,((0,'b'),)*2),Rule('',born,((0,'v'),))]
    model = Movies(Presentation({'f':(0,0)},marks,rules,{'a':0,'b':0}),'')
    src = a*4+born
    def swaps(w):
        return [('swap',g-1) for g in w]
    u = [(0,0),(1,4)]+swaps(expand(4,0,2,(2,1,2,3,1,1)))
    v = [(1,4)]+swaps(expand(4,0,2,(1,2,1,3)))+[(0,3)]+swaps(expand(4,3,2,(1,1)))
    result = decide(model,src,u,v,5)
    assert result['surface'] and not raw_compare(model,src,u,v)['raw'],result
    assert decide(model,src,v,u,1)['surface'] is False
    assert model.compare(src,u,v)['surface']
    return dict(thin_queries=pairs,thin_positive=positive,birth_radius=result['radius'],
                birth_steps=len(result['steps']),birth_passive=result['passive_steps'],birth_raw=False)


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    parser.add_argument('--radius',type=int)
    args = parser.parse_args()
    if args.query:
        q = json.loads(args.query.read_text())
        if q.get('attachments'):
            raise ValueError('expected a 3-computad')
        rules = [Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        model = Movies(Presentation(q['edges'],q['marks'],rules,q.get('mark_roots')),q['start'])
        source = tuple(map(tuple,q['source']))
        model.pres.walk(model.start,source,q.get('vertex'))
        result = decide(model,source,q['first'],q['second'],args.radius)
    else:
        result = checks()
    print(json.dumps(result))
