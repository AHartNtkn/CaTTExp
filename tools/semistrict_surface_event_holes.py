"""Read the ordinary homology and bounding event groups of a probe component.

Give serial probe_movies JSON. The result includes one selection of structural
3-occurrences to retain as point scalars for each component. For a simply
connected component this projection detects all its probe configuration groups.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, subst_tm, subst_ty, tdim, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_component_braids import Partition
from semistrict_surface_face_whitehead import polynomial
from semistrict_surface_probe_movies import configuration_betti, movie
from semistrict_surface_probe_sweep import point_movie


def analyze(data):
    groups = movie(data,with_homology=True)
    return [dict(component=c['component'],probe_indices=c['probe_indices'],betti=c['betti'],
                 simply_connected=c['simply_connected'],bounded_event_groups=c['event_groups'],
                 retain=[events[0] for events in c['event_groups']]) for c in groups]


def scalar_graph(sizes):
    # Independent compactified trace. Each gate segment is an edge, each
    # change is a vertex, and both regular ends meet the point at infinity.
    n = len(sizes)-1
    parts = Partition()
    for i in range(-1,n):
        parts.at(i)
    for gap,size in enumerate(sizes):
        if size:
            parts.unite(gap-1,gap if gap<n else -1)
    islands = {}
    for i in range(n):
        root = parts.at(i)
        if root!=parts.at(-1):
            islands.setdefault(root,[]).append(i)
    return [1,sum(sizes)-n+len(islands),len(islands)],list(islands.values())


def nested():
    # Wires a and b delimit a transient outer pocket at y. The second event
    # inside it creates a lens on c,d with innermost object z. Each lens
    # is closed by the inverse rule after an additional point event.
    edges = dict(a=['x','y'],b=['y','x'],c=['y','z'],d=['z','y'])
    gates = dict(B=['x','','ab'],D=['x','ab',''],F=['y','','cd'],M=['y','cd',''],
                 H=['x','',''],J=['y','',''],P=['z','',''])
    outer = [(0,'B'),(0,'D')]
    inner = [(0,'F'),(0,'M')]
    def place(rows,slot,a,b):
        return dict(diagram=rows,slot=slot,input=a,output=b)
    outer_site = [(0,'H')]
    inner_site = [(0,'B'),(1,'J'),(0,'D')]
    point_site = [(0,'B'),(1,'F'),(2,'P'),(1,'M'),(0,'D')]
    charts = [place(outer_site,0,[],outer),place(inner_site,1,[],inner),
              place(point_site,2,[],[]),place(inner_site,1,inner,[]),
              place(outer_site,0,outer,[])]
    return dict(edges=edges,gates=gates,path='',vertex='x',charts=charts,seams=[[]]*4,
                probes=[[0,0,0],[1,1,1],[2,2,2]])


def plat(word):
    # Two distinct births, a seam braid on all four points, then deaths
    # at the two adjacent pairs of the actual terminal reading.
    names = list('abcd')
    reached = names.copy()
    for g in word:
        i = abs(g)-1
        reached[i:i+2] = reversed(reached[i:i+2])
    def rows(labels):
        return [(0,g) for g in labels]
    def step(labels,slot,src,dst):
        return dict(diagram=rows(labels),slot=slot,input=rows(src),output=rows(dst))
    charts = [step(['H'],0,[],names[:2]),step([*names[:2],'H'],2,[],names[2:]),
              step(['H',*reached[2:]],0,reached[:2],[]),step(['H'],0,reached[2:],[])]
    return dict(vertex='x',path='',edges={},gates={g:['x','',''] for g in ['H',*names]},
                charts=charts,seams=[[],word,[]]),reached


def audit():
    graphs = seams = 0
    for n in range(2,7):
        for sizes in product(range(3),repeat=n):
            c, = analyze(point_movie(sizes))
            betti,islands = scalar_graph(sizes)
            assert c['betti']==betti and c['bounded_event_groups']==islands
            graphs += 1
    for n in range(4):
        for word in product((1,-1,2,-2,3,-3),repeat=n):
            data,reached = plat(word)
            components = Partition()
            for a,b in [('a','b'),('c','d'),reached[:2],reached[2:]]:
                components.unite(a,b)
            groups = {}
            for i,g in enumerate(['a','c',reached[0],reached[2]]):
                groups.setdefault(components.at(g),[]).append(i)
            c, = analyze(data)
            assert c['betti']==[1,len(groups),len(groups)]
            assert c['bounded_event_groups']==list(groups.values())
            seams += 1
    print(f'{graphs} scalar histories agree with graph duality; {seams} signed plats agree with link-component transport')
    result = sorted(analyze(nested()),key=lambda c:c['probe_indices'])
    assert [c['bounded_event_groups'] for c in result]==[[[0,1,2,3,4]],[[1,2,3]],[[2]]]
    assert all(c['betti']==[1,0,1] for c in result)
    isolated = configuration_betti(1,[1,1,1],lambda x,y,t:x==y==t==1)
    assert isolated==[1,0,1,0]
    # A birth and death of a *two*-point packet leaves a circle obstacle.
    # The two cap centres still represent one complementary component.
    arc, = analyze(point_movie([0,1,0]))
    loop, = analyze(point_movie([0,2,0]))
    assert arc['retain']==loop['retain']==[0] and arc['simply_connected'] and not loop['simply_connected']
    # Around the circle obstacle a meridian changes sheet in its double
    # cover. Collapsing the obstacle to either or both cap centres makes
    # that meridian null. Compare the two puncture lifts in each degree.
    first,second = 1,0
    for k in range(2,10):
        terms = [(1,first),(-1,second)]
        assert polynomial(terms,[0,1])[1][(0,)*(k-2)+(1,)]==1
        assert not polynomial(terms,[0,0])[1]
        first,second = [0,first],[0,second]
    print('the three nested faces select different event sets; the closed-loop deck difference survives in degrees 2–9 and vanishes after point collapse')


def scalar_images(ctx,selected):
    point = (STAR,)
    unit = identity(point,v(0))
    blank = identity(point,unit)
    target = point+(arr(infer(point,blank),blank,blank),)*len(selected)
    names = {g:v(i+1) for i,g in enumerate(selected)}
    images = []
    for i,decl in enumerate(ctx):
        ty = subst_ty(decl,images)
        if i in names:
            if tdim(ty)!=2:
                raise ValueError('select 3-generators')
            _,base,s,t = ty
            left,right = base[2:]
            fitted = comp2(target,1,comp2(target,1,head(point,left,unit),names[i]),head(point,unit,right))
            a,b = infer(target,fitted)[2:]
            value = comp2(target,2,comp2(target,2,head(point,s,a),fitted),head(point,b,t))
        else:
            value = v(0) if ty==STAR else head(point,*ty[2:])
        assert infer(target,value)==ty
        images.append(value)
    return target,images


def typed(directory):
    ctx = (STAR,arr(STAR,v(0),v(0)))
    a = v(1)
    aa = comp2(ctx,0,a,a)
    def hom(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (hom(a,aa),hom(aa,a))
    lens = comp2(ctx,1,v(2),v(3))
    blank = identity(ctx,a)
    ctx += (hom(blank,lens),hom(lens,blank))
    check_ctx(ctx)
    term = comp2(ctx,2,v(4),v(5))
    out = Emitter()
    for name,chosen in [('opening',[4]),('closing',[5]),('bothCentres',[4,5])]:
        target,images = scalar_images(ctx,chosen)
        check_ctx(target)
        projected = subst_tm(term,images)
        actual = subst_ty(infer(ctx,term),images)
        assert infer(target,projected)==actual
        if directory:
            out.check_type(name,target,projected,actual)
    if directory:
        (directory/'EventHoles.agda').write_text(out.module('EventHoles',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(analyze(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
        typed(args.agda_dir)
