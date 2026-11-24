"""Decide and expose stationary meetings on arbitrary executable signed readings."""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from semistrict_surface_history_group import inv
from semistrict_surface_joint_labels import positive_normal
from semistrict_surface_one_step_reflection import reverse_signed
from semistrict_surface_order_locks import divides
from semistrict_surface_packet_meetings import cut
from semistrict_surface_polygon_cabling import rectangle
from semistrict_surface_polygon_grades import resolution
from semistrict_surface_signed_width_two import Movies, Presentation, Rule
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_stationary_polygons import coset, initial_atoms, spelling, strip_atom


def orthogonal(n,word):
    """Positive/negative orthogonal fraction of a signed braid."""
    w = reverse_signed(tuple(word))
    j = next((i for i,g in enumerate(w) if g<0),len(w))
    x,y = (positive_normal(n,reversed(u)) for u in (w[:j],inv(w[j:])))
    while x and y:
        common = initial_atoms(x) & initial_atoms(y)
        if not common:
            break
        g = min(common)
        x,y = strip_atom(n,x,g),strip_atom(n,y,g)
    return tuple(reversed(spelling(x))),tuple(reversed(spelling(y)))


def passive_meeting(n,connector,p,q):
    """Factor an executable seam as a P-exterior path then a Q-exterior path."""
    i,k = p
    j,l = q
    if not (i+k<=j or j+l<=i):
        return None
    # From a common lower history A leads to the start and B to the end.
    b,a = orthogonal(n,connector[::-1])
    a,b = a[::-1],b[::-1]
    top,_ = orthogonal(n,connector)
    total = a+top
    left = tuple(reversed(spelling(coset(n,a,i,i+k))))
    right = tuple(reversed(spelling(coset(n,b,j,j+l))))
    leg,_ = orthogonal(n,inv(left)+right)
    joint = left+leg
    if not divides(n,joint,total):
        return None
    if coset(n,joint,i,i+k)!=coset(n,a,i,i+k) or coset(n,joint,j,j+l)!=coset(n,b,j,j+l):
        return None
    u,v = orthogonal(n,inv(a)+joint)
    x,y = orthogonal(n,inv(joint)+b)
    return u+inv(v),x+inv(y)


def follow(model,h,word):
    for g in word:
        h = model.swap(h,abs(g)-1,g>0)
        if h is None:
            raise ValueError('unavailable signed crossing in the positioned reading')
    return h


def translate(word,slot,old,new):
    out = []
    for g in word:
        if abs(g)<slot:
            out.append(g)
        elif abs(g)>slot+old:
            out.append(g+(new-old)*(1 if g>0 else -1))
        else:
            raise ValueError('path is not exterior to the indicated packet')
    return tuple(out)


def ordinary(word):
    out=[]
    for p,i in word:
        if p=='inverse':
            p='swap'
        if p!='swap' and (not isinstance(p,int) or p<0):
            raise ValueError('expected a rule index, swap, or inverse')
        out.append((p,i))
    return out


def verify_original(model,h,word):
    for p,i in word:
        if p in ('swap','inverse'):
            h = follow(model,h,((i+1)*(1 if p=='swap' else -1),))
        else:
            if p>=len(model.pres.rules) or (result:=model.named(h,p,i)) is None:
                raise ValueError('unavailable polygon in the signed input')
            h=result[0]
    return h


class Signed:
    def __init__(self,model,source,resolved):
        from semistrict_surface_link_schedules import Schedules
        named = Schedules(model,source,resolved)
        self.model,self.root,self.flow = named.model,named.root,resolved[1]
        self.width = sum(resolved[0])

    def decode(self,word,reading):
        seams,boxes = [[]],[]
        for (p,i),(_,name) in zip(word,reading):
            if name is None:
                seams[-1].append((i+1)*(1 if p=='swap' else -1))
            else:
                boxes.append((name,i))
                seams.append([])
        return tuple(boxes),tuple(map(tuple,seams))

    def scan(self,movie):
        boxes,seams = movie
        h = self.root
        placements,prefixes = {},{}
        unit = []
        for j,word in enumerate(seams):
            for g in word:
                i = abs(g)-1
                a,b = (self.flow[e] for _,e in h[i:i+2])
                off = sum(self.flow[e] for _,e in h[:i])
                x,y = (a,b) if g>0 else (b,a)
                block = tuple(t+1 for t in rectangle(off,x,y))
                unit.extend(block if g>0 else inv(block))
                h = follow(self.model,h,(g,))
            if j<len(boxes):
                p,i = boxes[j]
                rule = self.model.pres.rules[p]
                start = sum(self.flow[e] for _,e in h[:i])
                size = sum(self.flow[e] for _,e in h[i:i+len(rule.source)])
                prefixes[p] = (tuple(unit),start,size)
                dest,_ = self.model.named(h,p,i)
                placements[p] = h,dest
                h = dest
        return h,prefixes,placements,tuple(unit)

    def exchange(self,movie,k):
        boxes,seams = movie
        (p,i),(q,j) = boxes[k:k+2]
        pr,qr = self.model.pres.rules[p],self.model.pres.rules[q]
        a,b,c,d = map(len,(pr.source,pr.target,qr.source,qr.target))
        placements = self.scan(movie)[2]
        in_p,out_p = placements[p]
        legs = passive_meeting(len(out_p),seams[k+1],(i,b),(j,c))
        if legs is None:
            return None
        u,v = legs
        u0,v1 = translate(u,i,b,a),translate(v,j,c,d)
        before = follow(self.model,in_p,u0)
        common = follow(self.model,out_p,u)
        assert self.model.named(before,p,i)[0]==common
        assert follow(self.model,common,v)==placements[q][0]
        j0,i1 = (j,i+d-c) if j+c<=i else (j+a-b,i)
        new = boxes[:k]+((q,j0),(p,i1))+boxes[k+2:]
        paths = seams[:k]+(seams[k]+u0,(),v1+seams[k+2])+seams[k+3:]
        self.scan((new,paths))
        return new,paths


def decide(model,source,first,second):
    if model.attachments:
        raise ValueError('expected a positive 3-computad')
    pos = ordinary(first),ordinary(second)
    if verify_original(model,source,first)!=verify_original(model,source,second):
        raise ValueError('expected parallel signed readings')
    arities = [(len(r.source),len(r.target)) for r in model.pres.rules]
    resolved = resolution(source,pos,arities,'swap')
    if resolved is None:
        return dict(stationary=False,obstruction='named incidence')
    calc = Signed(model,source,resolved)
    a,b = [calc.decode(w,r) for w,r in zip((first,second),resolved[-1])]
    h,x,_,u = calc.scan(a)
    end,y,_,v = calc.scan(b)
    if h!=end or braid_image(calc.width,u)!=braid_image(calc.width,v):
        return dict(stationary=False,obstruction='resolved total or terminal names')
    for p,(prefix,i,k) in x.items():
        suffix,j,l = y[p]
        if (i,k)!=(j,l) or cut(braid_image(calc.width,prefix),i,k)!=cut(braid_image(calc.width,suffix),j,l):
            return dict(stationary=False,obstruction='stationary packet cut')
    current = list(x)
    target = list(y)
    for i,p in enumerate(current):
        for q in current[i+1:]:
            if target.index(p)>target.index(q):
                pre,i0,k = x[p]
                post,j0,l = x[q]
                if passive_meeting(calc.width,inv(pre)+post,(i0,k),(j0,l)) is None:
                    return dict(stationary=False,obstruction='inverted cuts have no disjoint meeting')
    # Construct the exact swaps on the original macro histories.
    exchanges = 0
    for i,p in enumerate(target):
        j = current.index(p)
        while j>i:
            a = calc.exchange(a,j-1)
            assert a is not None
            current[j-1:j+1] = reversed(current[j-1:j+1])
            exchanges+=1
            j-=1
    end,r,_,w = calc.scan(a)
    assert end==h and braid_image(calc.width,w)==braid_image(calc.width,v)
    for p,(word,i,k) in r.items():
        assert cut(braid_image(calc.width,word),i,k)==cut(braid_image(calc.width,y[p][0]),i,k)
    return dict(stationary=True,meetings=exchanges)


def checks():
    from random import Random
    rng=Random(22)
    factor_checks = found = 0
    for n in (3,4):
        alphabet = [s*g for g in range(1,n) for s in (-1,1)]
        for _ in range(550):
            i,j = rng.sample(range(n),2)
            w=tuple(rng.choice(alphabet) for _ in range(rng.randrange(7)))
            legs=passive_meeting(n,w,(i,1),(j,1))
            if legs is not None:
                u,v=legs
                assert all(abs(g)<i or abs(g)>i+1 for g in u)
                assert all(abs(g)<j or abs(g)>j+1 for g in v)
                assert braid_image(n,w)==braid_image(n,u+v)
                found+=1
            left=tuple(g for g in w if abs(g)<i or abs(g)>i+1)
            right=tuple(g for g in w[::-1] if abs(g)<j or abs(g)>j+1)
            assert passive_meeting(n,left+right,(i,1),(j,1)) is not None
            factor_checks+=2
    s=((0,'s'),)
    m=Movies(Presentation({'f':(0,0)},{'s':('',''),'b':('','f'),'d':('f','')},
                          [Rule('',s,((0,'b'),(0,'d')))],{'s':0,'b':0}),'f')
    src=s*2+((1,'s'),)*2
    # Wind the first pair negatively, then change their order on opposite
    # sides of two independent splits. Both macro arities change at meetings.
    w=(('inverse',0),('inverse',0))
    a=w+((0,0),(0,4))
    b=(('inverse',0),('inverse',0),(0,3),(0,0))
    assert decide(m,src,a,b)['meetings']==1
    unary=Movies(Presentation({}, {'s':('','')},[Rule('',s,s)],{'s':0}),'')
    def literal(w): return tuple(('swap' if g>0 else 'inverse',abs(g)-1) for g in w)
    for z,fits in (((-2,-2,1,1),True),((1,1,2,2),False)):
        left=((0,0),)+literal(z)+((0,2),)
        right=literal(z)+((0,2),)+literal(inv(z))+((0,0),)+literal(z)
        result=decide(unary,s*3,left,right)
        assert result['stationary']==fits
        if not fits:
            assert result['obstruction']=='inverted cuts have no disjoint meeting'
    # On three strands these two exterior groups are each cyclic. The two
    # exponents count crossings on distinct labelled pairs, so depth bounds
    # each exponent even for signed spellings with cancellation.
    def power(letter,n):
        return ((1 if n>=0 else -1)*letter,)*abs(n)
    depth=4
    valid={braid_image(3,power(2,i)+power(1,j)) for i,j in product(range(-depth,depth+1),repeat=2)}
    cyclic=0
    for k in range(depth+1):
        for w in product((-2,-1,1,2),repeat=k):
            assert (passive_meeting(3,w,(0,1),(2,1)) is not None)==(braid_image(3,w) in valid)
            cyclic+=1
    return dict(signed_factor_checks=factor_checks,successful_random_factors=found,placed_splits=True,
                cyclic_products=cyclic,signed_cut_inversions=2)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        if q.get('attachments'): raise ValueError('expected a 3-computad')
        rules=[Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        model=Movies(Presentation(q['edges'],q['marks'],rules,q.get('mark_roots')),q['start'])
        source=tuple(map(tuple,q['source']))
        model.pres.walk(model.start,source,q.get('vertex'))
        ans=decide(model,source,q['first'],q['second'])
    else:
        ans=checks()
    print(json.dumps(ans))
