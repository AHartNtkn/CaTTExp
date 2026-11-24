"""Read the degree-five surface order of positive two-slot movies from their token transfers."""
from argparse import ArgumentParser
from itertools import combinations, permutations, product
from pathlib import Path
import json

from semistrict_surface_signed_width_two import Movies, Presentation, Rule
from semistrict_surface_two_slot_polygons import segments, width_at_most_two
from semistrict_surface_two_slot_rectangles import compare as raw, routes


def words(model,source,reading):
    h,live = source,list(range(len(source)))
    counts,segment = [0,0],0
    early,late = {},{}
    for p,i in reading:
        if p=='swap':
            h = model.swap(h,i,True)
            live.reverse()
        else:
            rid = p
            rule = model.pres.rules[rid]
            if len(rule.source)!=1 or len(rule.target)!=1:
                h,_ = model.named(h,rid,i)
                segment += 1
                counts = [0,0]
                live = list(range(len(h)))
                continue
            s = live[i]
            key = segment,s,counts[s]
            counts[s] += 1
            before = model.pres.walk(model.start,h[:i])[-1]
            h,off = model.named(h,rid,i)
            end = off+len(model.pres.rules[rid].path)
            (early if i==0 else late)[key] = (rid,before[:off],before[end:])
    return early,late


def bits(early,late,moves):
    end = {k:i for i,k in enumerate(late)}
    times = {k:i for i,k in enumerate(moves)}
    return {(x,y):times[x]>times[y] for x,y in combinations(early,2)
            if x in times and y in times and end[x]>end[y]}


def decide(model,source,first,second,faces):
    if model.attachments:
        raise ValueError('expected a positive 3-computad')
    model.pres.walk(model.start,source)
    a,end = model.parse(source,first)
    b,other = model.parse(source,second)
    if end!=other or len(faces)!=2 or not all(width_at_most_two(model,source,r) for r in (a,b)):
        raise ValueError('expected parallel width-two movies and two prism schedules')
    early,_ = words(model,source,first)
    _,late = words(model,source,second)
    blocks,_ = segments(model,source,first)
    histories = []
    for face in faces:
        sequence = []
        routes(model,source,first,second,face,blocks,sequence)
        moves = {tuple(entry[:3]):entry[3] for entry in sequence}
        assert len(moves)==len(sequence)
        histories.append((moves,bits(early,late,moves)))
    (left,x),(right,y) = histories
    if left!=right:
        return dict(surface=False,obstruction='different token transfers')
    flips = []
    for (q,p),old in x.items():
        if old==y[q,p]:
            continue
        if old or (left[q],left[p])!=(1,-1):
            return dict(surface=False,obstruction='transfer order',tokens=(q,p))
        rid,l,_ = early[p]
        _,k,_ = early[q]
        if len(l)+len(model.pres.rules[rid].path)>len(k):
            return dict(surface=False,obstruction='overlapping initial windows',tokens=(q,p))
        flips.append((q,p))
    return dict(surface=True,changed_orders=flips)


def checks():
    from collections import Counter
    from semistrict_surface_rectangle_currents import shuffles
    counts = Counter()
    def compare(model,src,u,v,choices,tag):
        for a,b in product(choices,repeat=2):
            ans = decide(model,src,u,v,(a,b))
            expected = raw(model,src,u,v,(a,b)) is not None
            assert ans['surface']==expected,(src,u,v,a,b,ans)
            counts[tag]+=1
            counts['positive']+=expected
    # One looping declaration used on both slots and on every winding.
    unit = ((0,'a'),)
    loop = Movies(Presentation({},{'a':('','')},[Rule('',unit,unit)],{'a':0}),'')
    for bands in (((2,1),(1,2),(1,1)),((1,2),(2,1)),((1,1),(1,2),(1,1))):
        u,v,choices = [],[],[[]]
        for r,l in bands:
            right,left = [(0,0)]*r,[(0,0)]*l
            start = right+[('swap',0)]+left
            end,local = shuffles(start,right,left)
            translated = [[(op,i+len(u),*d) for op,i,*d in path] for path in local]
            choices = [x+y for x,y in product(choices,translated)]
            u.extend(start)
            v.extend(end)
        compare(loop,unit*2,u,v,choices,'scalar_loop')
    # A spatial birth and death cannot have any strictly positive conserved
    # length on f. The guards are evaluated on the original top path instead.
    edges = {'f':(0,0),'k':(0,0)}
    marks = {'a':('','f'),'b':('f','')}
    for n in (1,2,3):
        start = 'k'*n+'f'
        p = Rule('k',((0,'a'),),((0,'a'),))
        q = Rule('kf',((1,'b'),),((1,'b'),))
        model = Movies(Presentation(edges,marks,[p,q]),start)
        right,left = [(1,0)]*2,[(0,0)]*2
        u = right+[('swap',0)]+left
        v,choices = shuffles(u,right,left)
        compare(model,((n,'b'),(0,'a')),u,v,choices,'birth_death')
    split = Movies(Presentation({},{'a':('','')},[Rule('',unit,unit),Rule('',unit*2,unit),
                   Rule('',unit,unit*2),Rule('',unit*3,unit*4)],{'a':0}),'')
    start = [(0,0),('swap',0),(0,0)]
    end,local = shuffles(start,[(0,0)],[(0,0)])
    barriers = [(1,0),(0,0),(2,0)]
    u,v = start+barriers+start,end+barriers+end
    choices = []
    for x,y in product(local,repeat=2):
        z = [(op,i+6,*d) for op,i,*d in y]
        choices.extend((x+z,z+x))
    compare(split,unit*2,u,v,choices,'full_history_cuts')

    # Check the width bound on both orders of every pair of independent
    # boxes, and both sides of a mixed transport over a positive spectator.
    width_tests = 0
    for a,b,c,d in product(range(1,4),repeat=4):
        for exterior in range(3):
            left = max(a+c,b+c,b+d)+exterior<=2
            right = max(a+c,a+d,b+d)+exterior<=2
            assert left==right
            if left:
                assert (a,b,c,d)==(1,1,1,1)
            width_tests += 1
    # For the strict target, interleaving two independently composed transfer
    # schedules never changes the observations on the componentwise concatenation.
    tests = 0
    for n in range(1,4):
        part = tuple(range(n))
        tail = tuple(range(n,n+2))
        for a,b in product(permutations(part),permutations(tail)):
            for moves in permutations(part+tail):
                if tuple(k for k in moves if k<n)!=part or tuple(k for k in moves if k>=n)!=tail:
                    continue
                direct = bits(part+tail,a+b,moves)
                assert direct==bits(part,a,part)|bits(tail,b,tail)
                tests+=1
    return dict(counts,interchange_checks=tests,width_checks=width_tests)


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
        ans = decide(model,source,q['first'],q['second'],q['prism_faces'])
    else:
        ans = checks()
    print(json.dumps(ans))
