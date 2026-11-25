"""Bound generators of all probe-complement groups from ports of a signed movie.

Use --winding with a placement to obtain the primitive integer weights of
the movie-spine generators when the cut bound is at most one.
"""
from argparse import ArgumentParser
from fractions import Fraction
from functools import reduce
import json
from math import gcd,lcm
from pathlib import Path

from semistrict_surface_component_braids import Components, Partition
from semistrict_surface_movie_spine import expanded, presentation
from semistrict_surface_probe_movies import Faces, movie
from semistrict_surface_serial_gate_tracks import read_track


def port_cost(rows,ports,width):
    parts = Partition()
    wires = [('in',i) for i in range(width)]
    vertices = list(wires)
    for j,(p,g) in enumerate(rows):
        s,t = map(len,ports[g])
        vertices.append(j)
        for endpoint in wires[p:p+s]:
            parts.unite(j,endpoint)
        wires[p:p+s] = [j]*t
    return max(0,len({parts.at(v) for v in vertices})-1)


def cut_bound(data):
    charts = data['charts']
    read_track(dict(data,charts=[dict(c,loop=[]) for c in charts]),require_shared_gate=False)
    ports = {g:(s,t) for g,(_,s,t) in data['gates'].items()}
    costs = []
    for c in charts:
        _,marker = c['diagram'][c['slot']]
        width = len(ports[marker][0])
        costs.append([port_cost(c[side],ports,width) for side in ('input','output')])
    diagrams = [expanded(charts[0],'input'),*(expanded(c,'output') for c in charts)]
    gap_costs = []
    moving = sum(b for _,b in costs)
    for j,rows in enumerate(diagrams):
        holes = len(Components(rows,ports,len(data['path'])).skeleton)
        gap_costs.append(moving+holes)
        if j<len(costs):
            a,b = costs[j]
            moving += a-b
    return dict(port_costs=costs,cut_bounds=gap_costs,generator_bound=min(gap_costs))


def weights(spine):
    # Rational echelon reduction of the integral cocycle equations. There is
    # at most one free coordinate after the geometric generator bound.
    pivots = {}
    n = spine['generators']
    for word in spine['faces']:
        row = {}
        for g in word:
            i = abs(g)-1
            row[i] = row.get(i,0)+(1 if g>0 else -1)
        row = {i:Fraction(a) for i,a in row.items() if a}
        while row:
            i = min(row)
            scale = row[i]
            if i not in pivots:
                pivots[i] = {k:a/scale for k,a in row.items()}
                break
            for k,b in pivots[i].items():
                a = row.get(k,0)-scale*b
                if a:
                    row[k] = a
                else:
                    row.pop(k,None)
    free = set(range(n))-pivots.keys()
    assert len(free)<=1
    values = [Fraction(int(i in free)) for i in range(n)]
    for i,row in sorted(pivots.items(),reverse=True):
        values[i] = -sum((b*values[k] for k,b in row.items() if k!=i),Fraction())
    den = reduce(lcm,(v.denominator for v in values),1)
    result = [int(v*den) for v in values]
    div = reduce(gcd,result,0) or 1
    return [a//div for a in result]


def analyze(data,winding=False):
    result = cut_bound(data)
    if winding or 'word' in data:
        if result['generator_bound']>1:
            raise ValueError('cut bound exceeds one; abelian winding alone is inconclusive')
        basis = weights(presentation(data))
        result['winding_weights'] = basis
        if 'word' in data:
            word = data['word']
            if any(type(g) is not int or not 1<=abs(g)<=len(basis) for g in word):
                raise ValueError('expected signed one-based spine generators')
            result['winding'] = sum((1 if g>0 else -1)*basis[abs(g)-1] for g in word)
            result['raw_fibre_null'] = result['winding']==0
    return result


def audit():
    from semistrict_surface_face_lifetimes import lens_movie
    # Check the component formula independently by counting actual rim
    # sectors, their identifications, and holes in all local faces.
    types = [(a,b) for a in range(3) for b in range(3)]
    def visit(start,width,rows,ports):
        faces = Faces(rows,ports,start)
        rim = {f for (j,q),f in faces.spots.items()
               if j in (0,len(rows)) or q in (0,faces.slices[j])}
        holes = sum(faces.holes.values())
        expected = start+width-len(rim)+holes if start+width else max(0,holes-1)
        assert port_cost(rows,ports,start)==expected
        total = 1
        if len(rows)<3:
            for a,b in types:
                g = len(rows)
                for pos in range(width-a+1):
                    total += visit(start,width-a+b,[*rows,(pos,g)],{**ports,g:('f'*a,'f'*b)})
        return total
    total = sum(visit(i,i,[],{}) for i in range(3))
    for r in range(1,6):
        d = lens_movie([0],twist=True,wire_pairs=r)
        result = cut_bound(d)
        assert result['generator_bound']==r
        regions = movie(d,with_homology=True)
        lens, = [c for c in regions if c['graph_rank']==r]
        assert lens['betti']==[1,r,0] and regions[0]['betti']==[1,0,2]
        if r==1:
            # In the signed sample the spectator precedes the parent. Find
            # the inside placement from the actual lens-opening chart.
            j = lens['section']['use']
            slot = d['charts'][j]['slot']
            p = dict(d,placement=[j+1,slot+1,1])
            basis = analyze(p,True)['winding_weights']
            g = next(i+1 for i,a in enumerate(basis) if abs(a)==1)
            for word,value in (([g,g],2),([g,-g],0)):
                test = analyze(dict(p,word=word))
                assert abs(test['winding'])==value and test['raw_fibre_null']==(value==0)
    d = lens_movie([0,1],twist=True,close_with_positive_ports=True)
    backward = dict(d,charts=[dict(c,input=c['output'],output=c['input']) for c in reversed(d['charts'])],
                    seams=[[-g for g in reversed(word)] for word in reversed(d['seams'])])
    for data in (d,backward):
        bounds = cut_bound(data)['cut_bounds']
        assert sorted([bounds[0],bounds[-1]])==[0,2]
        assert all(c['simply_connected'] for c in movie(data,with_homology=True))
    print(f'Checked {total} ports, five sharp free-group ranks, signed integral winding and both one-sided returns.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--winding',action='store_true')
    parser.add_argument('--sample',type=int,metavar='RANK')
    args = parser.parse_args()
    if args.sample is not None:
        from semistrict_surface_face_lifetimes import lens_movie
        if args.sample<0:
            parser.error('rank must be nonnegative')
        d = lens_movie([0],twist=True,wire_pairs=args.sample)
        d['placement'] = [4,d['charts'][3]['slot']+1,1]
        print(json.dumps(d,indent=2))
    elif args.input:
        print(json.dumps(analyze(json.loads(args.input.read_text()),args.winding),indent=2))
    else:
        audit()
