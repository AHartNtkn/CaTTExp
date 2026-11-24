"""Decide a positioned signed comparison with one arbitrary positive polygon by contracting its window."""
from argparse import ArgumentParser
from pathlib import Path
import json

from semistrict_surface_component_braids import cabling,restrict
from semistrict_surface_history_group import exchange,inv
from semistrict_surface_meridian_transport import transport
from semistrict_surface_private_prefix_charts import records,solve as private_solve
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_signed_width_two import Movies,Presentation,Rule
from semistrict_surface_single_power import coprime_parts,output_order


def expand(width,slot,arity,word):
    end = 0
    face = []
    for i in range(width):
        size = arity if i==slot else 1
        face.append((None,end,end+size))
        end += size
    return cabling(face,word)


def positive_halves(actions):
    cut, = [i for i,(n,_) in enumerate(actions) if n!='swap']
    return tuple(i+1 for _,i in actions[:cut]),tuple(i+1 for _,i in actions[cut+1:])


def common_end(h,k,first,second,ports,positive):
    for g in first:
        h = exchange(h,g if positive else -g,ports)
        if h is None:
            return None
    for g in second:
        k = exchange(k,g if positive else -g,ports)
        if k is None:
            return None
    return h if h==k else None


def decide(model,source,first,second,radius=None):
    if model.attachments:
        raise ValueError('the one-polygon decision requires a 3-computad')
    u,end = model.parse(source,first)
    v,other = model.parse(source,second)
    if end!=other:
        raise ValueError('the readings must be parallel')
    if len(u)!=1 or len(v)!=1:
        raise ValueError('expected one polygon in each face')
    h,n,i = u[0]
    k,m,j = v[0]
    def no(reason):
        return dict(surface=False,obstruction=reason)
    if n!=m:
        return no('polygon name')
    a,b = positive_halves(first)
    c,d = positive_halves(second)
    t_in,t_out = inv(a)+c,b+inv(d)
    r = model.pres.rules[n]
    arity,outputs = len(r.source),len(r.target)
    order = output_order(range(len(h)),a)
    final_order = output_order(range(len(h)),c)
    if order[i:i+arity]!=final_order[j:j+arity]:
        return no('polygon input origins')
    if j<i:
        return no('polygon moves to an earlier temporal position')
    width = len(h)-arity+1
    keep = [e for e in range(len(h)) if not i<e<i+arity]
    z = restrict(len(h),t_in,keep)
    for size,relative in ((arity,t_in),(outputs,t_out)):
        if braid_image(width-1+size,expand(width,i,size,z))!=braid_image(width-1+size,relative):
            return no('relative braid is not the same full cable on both faces')

    pres = model.pres
    box = 'polygonWindow'
    ports = {box:(r.path,model.patch_ends[n])}
    roots = {box:(pres.poles(r.path)[0] if r.path else pres.mark_roots[r.source[0][1]])}
    def compressed(history,order,slot):
        _,off = model.named(history,n,slot)
        row = []
        for ix,(pos,mark) in enumerate(history):
            if ix==slot:
                row.append((off,box))
            if not slot<=ix<slot+arity:
                key = 'spectator'+str(order[ix])
                ports[key] = pres.marks[mark]
                roots[key] = pres.mark_roots[mark]
                row.append((pos,key))
        return tuple(row)
    h,k = compressed(h,order,i),compressed(k,final_order,j)
    if all(not s and not t for s,t in ports.values()) and len({pos for pos,_ in h+k})==1:
        initial = records(braid_image(width,()))[i+1]
        target = records(braid_image(width,z))[i+1]
        return dict(surface=bool(transport(initial,target)),compressed_braid=z,method='scalar cut')

    # Deletion of strands supplies fractions of the two needed signs without
    # introducing any extra legs. Shorten them before trying the wider window.
    cut = next((a for a,g in enumerate(z) if g>0),len(z))
    bot1,bot2,_ = coprime_parts(inv(z[:cut])[::-1],z[cut:][::-1])
    bottom = common_end(h,k,bot1,bot2,ports,False)
    if bottom is None:
        return no('negative legs do not meet on the contracted histories')
    keep = [e for e in range(width-1+outputs) if not i<e<i+outputs]
    upper = restrict(width-1+outputs,t_out,keep)
    cut = next((a for a,g in enumerate(upper) if g<0),len(upper))
    top1,top2,_ = coprime_parts(upper[:cut],inv(upper[cut:]))
    if common_end(h,k,top1,top2,ports,True) is None:
        return no('positive legs do not meet on the contracted histories')
    def movie(prefix,slot,suffix):
        crosses = lambda word:[('X',g-1) for g in word]
        return crosses(prefix)+[('moveWindow',slot)]+crosses(suffix)
    initial_vertex = pres.poles(model.start)[0] if model.start else roots[bottom[0][1]]
    data = dict(edges=pres.edges,marks={e:(list(s),list(t)) for e,(s,t) in ports.items()},
                scalar_at=roots,initial=list(model.start),start_vertex=initial_vertex,history=bottom,
                higher=[{'moveWindow':(box,box)}],source=movie(bot1[::-1],i,top1),
                target=movie(bot2[::-1],j,top2))
    result = private_solve(data,radius)
    return dict(surface=result['surface_filler'],compressed_braid=z,method='positioned cut',private=result)


def checks():
    from itertools import product
    s = ((0,'a'),)
    base = Presentation({}, {'a':('','')},[Rule('',s*2,s*3),Rule('',s,s*3)],{'a':0})
    model = Movies(base,'')
    from semistrict_surface_private_heap_order import solve as literal_raw
    from semistrict_surface_private_three_windings import solve as three
    from semistrict_surface_private_winding import solve as two
    tested = passed = 0
    steps = lambda w:[('swap',g-1) for g in w]
    for width in range(2,5):
        for i in range(width):
            for length in range(4):
                for word in product(range(1,width),repeat=length):
                    j = output_order(range(width),word).index(i)
                    for rid,arity in enumerate((2,1)):
                        src = s*(width+arity-1)
                        first = [(rid,i)]+steps(expand(width,i,3,word))
                        second = steps(expand(width,i,arity,word))+[(rid,j)]
                        got = decide(model,src,first,second)['surface']
                        plain = dict(edges={},initial=[],start_vertex=0,marks={'s':([],[])},
                                     scalar_at={'s':0},higher=[{'p':('s','s')}],history=[(0,'s')]*width,
                                     source=[('p',i)]+[('X',g-1) for g in word],
                                     target=[('X',g-1) for g in word]+[('p',j)])
                        if width<=3:
                            independent = (two if width==2 else three)(plain)
                            assert got==independent['surface_filler']
                        direct = literal_raw(plain)['raw_filler'] if width<=3 else None
                        if direct:
                            assert got
                        tested += 1
                        passed += got
    src = s*3
    assert not decide(model,src,[(0,0)],[('swap',0),('swap',0),(0,0)])['surface']
    assert not decide(model,src,[(0,0),('swap',0),('swap',0)],[(0,0)])['surface']
    # The full spatial window overlaps the first spectator; the narrower one fits.
    edges = {'f':(0,1),'k':(1,2),'g':(2,3)}
    marks = {'a':('f','f'),'b':('kg','kg'),'c':('g','g')}
    rule = Rule('fk',((0,'a'),),((0,'a'),(0,'a')))
    planar = Movies(Presentation(edges,marks,[rule]),'fkg')
    for pos,letter in ((1,'b'),(2,'c')):
        src = ((pos,letter),(0,'a'))
        first,second = [('swap',0),(0,0)],[(0,1),('swap',0),('swap',1)]
        assert decide(planar,src,first,second,radius=2)['surface']==(letter=='c')
    # A nonsimple braid on a spatial birth and three floating scalars.
    # Replace the earlier one-mark example by a two-input, three-output polygon.
    birth = Presentation({'f':(0,0)},{'a':('',''),'u':('','f')},[Rule('',s*2,s*3)],{'a':0})
    model = Movies(birth,'')
    source = s*4+((0,'u'),)
    pre,tail = (1,2,1,3),(1,1)
    early = [(0,0)]+steps(expand(4,0,3,(2,1,2,3,1,1)))
    late = steps(expand(4,0,2,pre))+[(0,3)]+steps(expand(4,3,3,tail))
    yes = decide(model,source,early,late,radius=3)
    assert yes['surface'] and yes['method']=='positioned cut'
    assert model.compare(source,early,late)['surface']
    assert decide(model,source,late,early,radius=3)['surface'] is False
    # Two copies split by a full-history polygon at five events.
    output = model.parse(source,early)[1]
    wall = Rule('',output,source)
    serial = Movies(Presentation({'f':(0,0)},birth.marks,[birth.rules[0],wall],{'a':0}),'')
    both = serial.compare(source,early+[(1,0)]+early,late+[(1,0)]+late)
    assert both['surface'] and len(both['pieces'])==2
    # A common pure prefix moves an overlapping spectator across the
    # individual inputs, although it cannot cross the entire contracted window.
    two = Rule('fk',((0,'a'),(0,'a')),((0,'a'),))
    placed = Movies(Presentation(edges,marks,[two]),'fkg')
    prefix = [('swap',0),('swap',1),(0,0)]
    assert decide(placed,((1,'b'),(0,'a'),(0,'a')),prefix,prefix,radius=0)['surface']
    from semistrict_surface_raw_movie_graph import raw_compare
    scalar = Movies(base,'')
    reverse = steps((2,1,2))+[(0,3)]
    forward = steps((1,2,1))+[(0,3)]
    assert scalar.compare(s*5,reverse,forward)['surface']
    assert not raw_compare(scalar,s*5,reverse,forward)['raw']
    return dict(cabled_queries=tested,positive=passed,internal_twists_rejected=2,positioned_window_queries=2,positioned_birth_positive=yes['surface'],separated_pieces=len(both['pieces']))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    parser.add_argument('--radius',type=int)
    args = parser.parse_args()
    if args.query:
        q = json.loads(args.query.read_text())
        rules = [Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        if q.get('attachments'):
            raise ValueError('expected a 3-computad')
        pres = Presentation(q['edges'],q['marks'],rules,q.get('mark_roots'))
        src = tuple(map(tuple,q['source']))
        pres.walk(q['start'],src,q.get('vertex'))
        result = decide(Movies(pres,q['start']),src,q['first'],q['second'],args.radius)
    else:
        result = checks()
    print(json.dumps(result))
