"""Lift mixed globular tensor faces at a positioned history, including empty sites.

--atom FILE supplies the private history presentation and a list 'atoms' of
actual generating heads in spatial order. The history lists the whole active
block in temporal order. --sector FILE takes zero-based erased 'crossings'
and optionally an evaluated Response 116 judgment, with columns in final
event order (one tree per event). The judgment must be on that supplied sector.
"""
from argparse import ArgumentParser
from functools import cache
from itertools import product
import json
from pathlib import Path

from gray_globe_comparison import atom
from semistrict_surface_acyclic_private_movies import Traces
from semistrict_surface_globular_judgment import decide
from semistrict_surface_private_histories import solve as validate
from semistrict_surface_scalar_lift import cube,execute


def edge_path(row):
    return sorted(row,key=lambda edge:edge.count((0,1)))


@cache
def movies(profile):
    rows = atom(tuple((d,2) for d in profile))
    result = []
    for side in rows[2]:
        pending = set(side)
        steps = []
        path = edge_path(rows[1][0])
        while pending:
            for face in sorted(pending):
                src,dst = map(edge_path,atom(face)[1])
                if src[0] not in path:
                    continue
                i = path.index(src[0])
                if path[i:i+len(src)] != src:
                    continue
                active = [e for e,(d,_) in enumerate(face) if d]
                if len(active)==2:
                    steps.append(('X',i))
                else:
                    e, = active
                    steps.append(((e,face[e][1]),i))
                path[i:i+len(src)] = dst
                pending.remove(face)
                break
            else:
                raise ValueError('unserializable characteristic two-face')
        assert path == edge_path(rows[1][1])
        result.append(tuple(steps))
    return result


def lift_atom(data):
    h = tuple(map(tuple,data['history']))
    validate({**data,'source':h,'target':h})
    names = data['atoms']
    if len(h)!=len(names) or not h:
        raise ValueError('expected one active event per spatial factor')
    layers = [{},data['marks'],*data.get('higher',[])]
    if len(layers)>2 and 'X' in layers[2]:
        raise ValueError('reserved exchange label')
    ranks = {a:d for d,layer in enumerate(layers) for a in layer}
    profile = tuple(ranks[a] for a in names)
    if sum(profile)<3:
        raise ValueError('expected an atom of local rank at least three')
    def restriction(e,d,tag):
        a = names[e]
        r = profile[e]
        if r==d:
            assert tag==2
            return a
        while r>d+1:
            a = layers[r][a][0]
            r -= 1
        return layers[r][a][tag]
    if [a for _,a in reversed(h)] != [restriction(e,1,2 if d==1 else 0) for e,d in enumerate(profile)]:
        return dict(fits=False)
    chart = Traces(data['marks'],layers[2] if len(layers)>2 else {},{})
    predicted = cube(h,chart.marks,0,len(h)) if len(h)>1 else h
    sides = []
    for abstract in movies(profile):
        reading = [(label if label=='X' else restriction(label[0],2,label[1]),i) for label,i in abstract]
        # Port collisions affect exactly the erased square operations.
        if execute(h,[i for label,i in reading if label=='X'],chart.marks) is None:
            assert predicted is None
            return dict(fits=False)
        end,_ = chart.read(h,reading)
        assert predicted is not None
        expected = tuple((pos,restriction(e,1,2 if d==1 else 1))
                         for e,((pos,_),d) in enumerate(zip(predicted,profile)))
        assert end==expected
        sides.append(reading)
    return dict(fits=True,rank=sum(profile),source_reading=sides[0],target_reading=sides[1],end=end)


def sector(data):
    h = tuple(map(tuple,data['history']))
    validate({**data,'source':h,'target':h})
    end = execute(h,data['crossings'],data['marks'])
    if end is None:
        raise ValueError('erased braid does not execute on these ports')
    order = list(range(len(h)))
    simple = True
    for i in data['crossings']:
        simple &= order[i]<order[i+1]
        order[i],order[i+1]=order[i+1],order[i]
    out = dict(simple=simple,event_columns=order if simple else None)
    if 'judgment' in data:
        j = data['judgment']
        if not simple or j['degree']<4 or len(j['columns'])!=len(order):
            raise ValueError('expected a simple sector and an evaluated column per event in degree four or above')
        out['raw_filler'] = decide(j)
    return out


def example(ds,kinds):
    defs={'scalar':([],[]),'birth':([],['x']),'death':(['x'],[]),'split':(['x'],['x','x'])}
    marks,scalars,layers,heads,h = {},{},[{} for _ in range(max(ds)-1)],[],[]
    pos = 0
    for e,(d,kind) in enumerate(zip(ds,kinds)):
        s,t = defs[kind]
        faces=[]
        for r in range(1,d+1):
            tags = [f'{e}_{r}_{i}' for i in range(1 if r==d else 2)]
            for tag in tags:
                if r==1:
                    marks[tag]=[s,t]
                    if not (s or t):
                        scalars[tag]=0
                else:
                    layers[r-2][tag]=faces
            if r==1:
                h.append((pos,tags[0]))
            faces=tags
        heads.append(faces[0])
        pos+=len(s)
    data=dict(edges={'x':[0,0]},initial=['x']*pos,start_vertex=0,
              marks=marks,scalar_at=scalars,higher=layers,atoms=heads,history=h[::-1])
    return data


def checks():
    # Both strict two-hemispheres against simultaneously positioned spatial
    # factors with genuinely changing phase names at every noninterval slot.
    checks = 0
    for ds in [(3,),(4,1),(2,2),(1,3,1),(1,2,3),(2,1,2,2),(1,1,2,1,2)]:
        for kinds in product(('scalar','birth','death','split'),repeat=len(ds)):
            data = example(ds,kinds)
            assert lift_atom(data)['fits']
            checks+=1
    clash=dict(edges={'x':[0,0]},initial=['x'],marks={x:[['x'],['x']] for x in 'aAb'},
               higher=[{'p':['a','A']}],atoms=['p','b'],history=[(0,'b'),(0,'a')])
    assert not lift_atom(clash)['fits']
    # Actual high-dimensional characteristic boundary, both orientations.
    for ds in ((1,2,1),(2,3,2),(2,4,2)):
        width=len(ds)
        data = example(ds,['scalar']*width)
        original = lift_atom(data)
        assert original['fits']
        data['crossings'] = [i for move,i in original['source_reading'] if move=='X']
        trees=[]
        for d in ds:
            t=[]
            for _ in range(d):
                t=[t]
            trees.append(t)
        sides=[[[[(r,0 if tag==2 else tag) for r,tag in face],1] for face in side]
               for side in atom(tuple((d,2) for d in ds))[-2]]
        j=dict(degree=sum(ds)+1,columns=trees,slots=[],moves=[],source=sides[0],target=sides[1])
        assert sector(dict(data,judgment=j))['raw_filler']
        j['source'],j['target']=j['target'],j['source']
        assert not sector(dict(data,judgment=j))['raw_filler']
    print(f'{checks} physically positioned mixed atoms, overlapping-site rejection and '
          'both orientations of raw judgments in degrees five, eight and nine checked')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    action=p.add_mutually_exclusive_group()
    action.add_argument('--atom',type=Path)
    action.add_argument('--sector',type=Path)
    args=p.parse_args()
    if args.atom:
        print(json.dumps(lift_atom(json.loads(args.atom.read_text()))))
    elif args.sector:
        print(json.dumps(sector(json.loads(args.sector.read_text()))))
    else:
        checks()
