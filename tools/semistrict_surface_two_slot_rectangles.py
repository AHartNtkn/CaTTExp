"""Compare strict prism pastes and realize native rectangles over two-event readings."""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import product
import json
from pathlib import Path

from semistrict_surface_raw_movie_graph import read,raw_updates
from semistrict_surface_signed_width_two import Movies,Presentation,Rule
from semistrict_surface_two_slot_polygons import advance_crossing,segments,width_at_most_two


def routes(model,source,first,second,schedule,blocks,sequence=None):
    keys = []
    for g,(_,_,order) in enumerate(blocks):
        if g:
            keys.append((g,'whole'))
        keys.extend((g,*key) for key in order)
    actions = tuple(map(tuple,first))
    by_cross = defaultdict(list)
    for step in schedule:
        kind,j,*direction = step
        if not 0<=j<len(actions)-1:
            raise ValueError('local step outside the reading')
        x,y = actions[j:j+2]
        k,l = keys[j:j+2]
        if kind=='commute' and not direction and k[1]==l[1]=='mark' and x[1]!=y[1]:
            changed = y,x
        elif kind=='prism' and direction==[1] and k[1]=='mark' and l[1]=='cross':
            by_cross[l[0],l[2]].append((1,k[2],k[3]))
            if sequence is not None:
                sequence.append((k[0],k[2],k[3],1))
            changed = y,(x[0],1)
        elif kind=='prism' and direction==[-1] and k[1]=='cross' and l[1]=='mark':
            by_cross[k[0],k[2]].append((-1,l[2],l[3]))
            if sequence is not None:
                sequence.append((l[0],l[2],l[3],-1))
            changed = (y[0],1),x
        else:
            raise ValueError('step is not a two-slot prism or disjoint commutation')
        nxt = actions[:j]+changed+actions[j+2:]
        h,w = read(model,source,actions)
        if nxt not in raw_updates(model,actions,h,w,len(actions)):
            raise ValueError('unavailable positioned step')
        actions = nxt
        keys[j:j+2] = l,k
    if actions!=tuple(map(tuple,second)):
        raise ValueError('schedule does not finish at the supplied reading')
    return by_cross


def rectangle_fits(model,h,right,left):
    # At this corner the crossing follows the right update and precedes the left.
    r = model.pres.rules[right]
    right_offset = h[0][0]-r.target[0][0]
    left_step = model.named(model.swap(h,0,True),left,0)
    return left_step is not None and left_step[1]+len(model.pres.rules[left].path)<=right_offset


def compare(model,source,first,second,faces):
    if model.attachments or len(faces)!=2:
        raise ValueError('expected a 3-computad and two parallel prism schedules')
    u,end = model.parse(source,first)
    v,other = model.parse(source,second)
    if end!=other or not all(width_at_most_two(model,source,r) for r in (u,v)):
        raise ValueError('expected two parallel readings of temporal width at most two')
    blocks,_ = segments(model,source,first)
    a,b = [routes(model,source,first,second,face,blocks) for face in faces]
    answer = []
    for g,c in sorted(set(a)|set(b)):
        path = list(a[g,c])
        target = b[g,c]
        rows,crossings,_ = blocks[g]
        for j,mark in enumerate(target):
            k = path.index(mark)
            for t in reversed(range(j,k)):
                forward,backward = path[t:t+2]
                if (forward[0],backward[0])!=(1,-1):
                    return None
                h = crossings[c][0]
                for sign,strand,r in path[:t]:
                    h = advance_crossing(model,h,rows[strand][r],sign==1)
                    assert h is not None
                if not rectangle_fits(model,h,rows[forward[1]][forward[2]],rows[backward[1]][backward[2]]):
                    return None
                answer.append((g,c,forward[2],backward[2]))
                path[t:t+2] = backward,forward
        assert path==target
    return answer


def checks():
    edges = {'f':(0,1),'k':(1,1),'g':(1,2)}
    marks = {'a':('f','f'),'b':('g','g')}
    p = Rule('fk',((0,'a'),),((0,'a'),))
    q = Rule('kg',((1,'b'),),((1,'b'),))
    comparisons = positives = 0
    for length in (1,2,3):
        model = Movies(Presentation(edges,marks,[p,q]),'f'+'k'*length+'g')
        source = ((length+1,'b'),(0,'a'))
        # Two changes on each strand give all six shuffles at one crossing.
        first = [(1,0),(1,0),('swap',0),(0,0),(0,0)]
        second = [(0,1),(0,1),('swap',0),(1,1),(1,1)]
        faces,classified = {},{}
        from itertools import combinations
        for positions in combinations(range(4),2):
            order = [1 if i in positions else -1 for i in range(4)]
            actions = first.copy()
            schedule = []
            def exchange(j,step,changed):
                actions[j:j+2] = changed
                schedule.append(step)
            for sign in order:
                c = actions.index(('swap',0))
                if sign==1:
                    i = max(i for i in range(c) if actions[i]==(1,0))
                    for j in range(i,c-1):
                        exchange(j,('commute',j),actions[j:j+2][::-1])
                    exchange(c-1,('prism',c-1,1),[('swap',0),(1,1)])
                else:
                    i = next(i for i in range(c+1,len(actions)) if actions[i]==(0,0))
                    for j in reversed(range(c+1,i)):
                        exchange(j,('commute',j),actions[j:j+2][::-1])
                    exchange(c,('prism',c,-1),[(0,1),('swap',0)])
            assert actions==second
            key = tuple(order)
            faces[key] = schedule
            classified[key] = {(i,j) for i,loc in enumerate(positions)
                               for j,k in enumerate(n for n in range(4) if n not in positions) if k<loc}
        for x,y in product(faces,repeat=2):
            cert = compare(model,source,first,second,(faces[x],faces[y]))
            expected = x==y if length==1 else classified[x]<=classified[y]
            assert (cert is not None)==expected
            if cert is not None:
                assert len(cert)==len(classified[y]-classified[x])
            positives += expected
            comparisons += 1
    # Two different windings of the very same scalar pair carry independent
    # rectangles. They use disjoint updates even though all four labels repeat.
    s = ((0,'s'),)
    model = Movies(Presentation({}, {'s':('','')},[Rule('',s,s)],{'s':0}),'')
    first = [(0,0),('swap',0),(0,0),(0,0),('swap',0),(0,0)]
    second = [(0,1),('swap',0),(0,1),(0,1),('swap',0),(0,1)]
    # When a first move puts two updates in one gap they commute before the next move.
    def block(offset,bit):
        return ([('prism',offset+1,-1),('commute',offset),('prism',offset+1,1)]
                if bit else [('prism',offset,1),('commute',offset+1),('prism',offset,-1)])
    independent = {}
    for bits in product((0,1),repeat=2):
        independent[bits] = block(0,bits[0])+block(3,bits[1])
    for x,y in product(independent,repeat=2):
        cert = compare(model,s*2,first,second,(independent[x],independent[y]))
        assert (cert is not None)==all(i<=j for i,j in zip(x,y))
    return dict(positioned_queries=comparisons,positive=positives,independent_winding_queries=16)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        if q.get('attachments'):
            raise ValueError('expected a 3-computad')
        rules=[Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        pres=Presentation(q['edges'],q['marks'],rules,q.get('mark_roots'))
        source=tuple(map(tuple,q['source']))
        pres.walk(q['start'],source,q.get('vertex'))
        cert=compare(Movies(pres,q['start']),source,q['first'],q['second'],q['prism_faces'])
        result=dict(raw=cert is not None,rectangles=cert)
        from semistrict_surface_transfer_order import decide
        result['surface']=decide(model,source,q['first'],q['second'],q['prism_faces'])['surface']
    else:
        result=checks()
    print(json.dumps(result))
