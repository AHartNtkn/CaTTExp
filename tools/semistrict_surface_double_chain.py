"""Double a positioned chain at the original 2-ends and certify higher raw classes.

Supply the positioned chain, including its actual site loops, as JSON. --degree
is the old globe degree (at least six); --count is a positive finite rank.
"""
from argparse import ArgumentParser
import json
from pathlib import Path

from semistrict_surface_closed_port_group import first_basis, lift, nested
from semistrict_surface_component_braids import Group, restrict
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_movie_spine import expanded
from semistrict_surface_probe_kernel import solve as orbit_certificate
from semistrict_surface_scalar_leaves import gate_segments
from semistrict_surface_serial_gate_tracks import motion, read_track
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_wired_localization import localize


def first_word(data):
    first = data['charts'][0]
    group = Group(tuple(map(tuple,first['diagram'])), {g:(s,t) for g,(_,s,t) in data['gates'].items()},
                  len(data['path']))
    idx = group.loc[first['slot']]
    for face in group.packets:
        starts = [a for _,a,_ in face]
        if not any((a,b)==(idx,idx+1) for _,a,b in face):
            continue
        marker = starts.index(idx)+1
        w = inv(group.path)+tuple(first['loop'])+group.path
        braid = restrict(len(first['diagram']), w, set(starts))
        image = braid_image(len(face),braid)[marker-1]
        stem = image[:len(image)//2]
        assert image == stem+(marker,)+inv(stem)
        word = reduced(g if abs(g)<marker else g-(1 if g>0 else -1)
                       for g in stem if abs(g)!=marker)
        return len(face)-1, word
    raise AssertionError('missing first-site face')


def amplify(data, degree, count):
    if degree<6 or count<1:
        raise ValueError('expected degree >= 6 and count >= 1')
    if not read_track(data)['nonzero']:
        return dict(raw_loop_null=True)
    placed = localize(data)
    holes, word = first_word(data)
    assert word and holes==placed['free_rank']
    cert = orbit_certificate(dict(holes=holes,word=word,sphere_degree=degree-4,count=count))
    packed = placed['packed']
    double = dict(packed, charts=packed['charts']*2, seams=packed['seams']+[()]+packed['seams'])
    initial, final, producers, consumers, steps = gate_segments(double)
    sites = len(packed['charts'])
    edges = {(a,b) for a,b in zip(producers,consumers) if a is not None and b is not None}
    assert all((a<sites)==(b<sites) for a,b in edges)
    assert all((i,i+1) in edges for i in range(2*sites-1) if i!=sites-1)
    assert initial==final and all(producers[g] is None and consumers[g] is None for g in final)
    ports = {g:(s,t) for g,(_,s,t) in data['gates'].items()}
    assert motion(expanded(double['charts'][-1],'output'),ports,placed['exterior_seam']) == expanded(data['charts'][-1],'output')
    return dict(first_site_word=word, holes=holes, doubled=double, exterior_seam=placed['exterior_seam'],
                selected_sites=[0,sites], dependence_edges=sorted(edges), higher_certificate=cert)


def audit():
    data = nested(())
    data['gates'].update(K=['x','','ff'], L=['x','ff',''], J=['x','ff','ff'],
                         s=['x','',''], outside=['x','',''])
    data['charts'][1] = dict(diagram=[(0,'B'),(0,'J'),(0,'D'),(0,'extra'),(0,'hole')],
                            slot=1,input=[(1,'p')],output=[(1,'r')])
    for chart in data['charts']:
        chart['diagram'] = [(0,'K')]+[(1+j,g) for j,g in chart['diagram']]+[(1,'s'),(0,'L'),(0,'outside')]
        chart['slot'] += 1
    x,y = first_basis(data)
    for word in [x, x+y+inv(x)+inv(y)]:
        paths = lift(data, word)
        track = dict(data,charts=[dict(c,loop=w) for c,w in zip(data['charts'],paths,strict=True)])
        for degree in (6,7,9):
            result = amplify(track,degree,4)
            assert result['selected_sites'] == [0,3]
            assert result['dependence_edges'] == [(0,1),(0,2),(1,2),(3,4),(3,5),(4,5)]
            assert result['higher_certificate']['old_degree'] == degree
            if word!=x:
                w = result['first_site_word']
                assert all(w.count(a)==w.count(-a) for a in (1,2)) and w
    print('Two disjoint three-use wired chains verified in one stationary lens. Six rank-four '
          'integral certificates passed in degrees 6, 7 and 9, including a meridian commutator.')


if __name__ == '__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('input', type=Path, nargs='?')
    cli.add_argument('--degree', type=int, default=6)
    cli.add_argument('--count', type=int, default=2)
    args = cli.parse_args()
    if args.input:
        print(json.dumps(amplify(json.loads(args.input.read_text()),args.degree,args.count),indent=2))
    else:
        audit()
