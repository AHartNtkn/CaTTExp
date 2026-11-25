"""Decide named degree-five obstruction on faces with at most two structural sites.

Pass a positioned point-site movie JSON. Free probes and through strands
are unrestricted; the site bound is applied after pruning in each actual face.
"""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path
import json

from semistrict_surface_component_braids import Partition
from semistrict_surface_face_factors import factors
from semistrict_surface_face_obstructions import scalar_movie
from semistrict_surface_scalar_leaves import prune
from semistrict_surface_serial_packet_group import solve


def classify(reduction):
    movie = reduction['movie']
    sites = [(i,c) for i,c in enumerate(movie['charts']) if c['input'] or c['output']]
    k = len(movie['charts'])-len(sites)
    if len(sites)>2:
        return dict(classified=False,structural_sites=len(sites),probes=k)
    m = len(reduction['initial'])
    incidence = {}
    parts = Partition()
    infinity = -1
    vertices = [infinity]
    for j,(_,c) in enumerate(sites):
        vertices.append(j)
        for end,port in ((0,c['output']),(1,c['input'])):
            for _,g in port:
                incidence.setdefault(g,[infinity,infinity])[end] = j
    for g in reduction['initial']+reduction['final']:
        incidence.setdefault(g,[infinity,infinity])
    for start,end in incidence.values():
        parts.unite(start,end)
    # Alexander duality after attaching all fixed boundary tips at infinity.
    cycles = len(incidence)-len(vertices)+len({parts.at(v) for v in vertices})
    assert bool(cycles)==bool(incidence)
    rank = 0
    dependent = False
    if len(sites)==2:
        (i,first),(j,last) = sites
        dependent = bool(set(first['output']) & set(last['input']))
        if dependent:
            seam = [g for w in movie['seams'][i:j] for g in w]
            steps = [dict(slot=c['slot'],input=len(c['input']),output=len(c['output']),seam=w)
                     for c,w in ((first,seam),(last,()))]
            rank = solve(dict(initial=m,steps=steps))['free_rank']
    return dict(classified=True,structural_sites=len(sites),probes=k,dependent=dependent,
                structural_free_rank=rank,one_probe_first_betti=cycles,
                named_degree_five_obstruction=bool(rank or k*cycles))


def analyze(data):
    return [dict(face=f['face'],**classify(prune(scalar_movie(f)))) for f in factors(data)['factors']]


def audit():
    from semistrict_surface_movie_spine import presentation
    from semistrict_surface_scalar_leaves import sample
    count = 0
    for initial_a,final_a,initial_b,final_b in product((0,2),repeat=4):
        if not (initial_a or final_a) or not (initial_b or final_b):
            continue
        for probes,through in product((0,1,3),(0,1)):
            start = [f's{i}' for i in range(initial_a+initial_b+through)]
            changes = [(0,initial_a,final_a)]+[(0,0,0)]*probes+[(final_a,initial_b,final_b)]
            seam = [final_a,final_a] if final_a and initial_b else []
            data = sample(start,changes,[seam]+[[]]*probes)
            result, = analyze(data)
            assert result['structural_sites']==2 and result['probes']==probes
            assert not result['dependent'] and result['structural_free_rank']==0
            assert result['named_degree_five_obstruction']==bool(probes)
            # Removing point events only adds 2-spheres, preserving first Betti.
            assert presentation(data)['betti'][1]==result['one_probe_first_betti']
            count += 1
    # The first and last sites of the closed component can still carry a
    # nonzero structural loop beside a through strand. The intervening
    # genuine probes have no bearing on that structural group.
    comm = (1,1,2,2,-1,-1,-2,-2)
    for seam,rank in (((),1),(comm,0)):
        for k in range(3):
            data = sample(['s'],[(0,0,2)]+[(0,0,0)]*k+[(0,2,0)],[seam]+[[]]*k)
            result, = analyze(data)
            assert result['dependent'] and result['structural_free_rank']==rank
            assert result['named_degree_five_obstruction']==bool(k or rank)
            assert result['one_probe_first_betti']==2
    for k in (1,2,3):
        result, = analyze(sample([],[(0,0,0)]*k,[[]]*(k-1)))
        assert not result['named_degree_five_obstruction']
    print(f'{count} independent port and probe configurations agree with the signed complement spine.')
    print('Six closed-return computations distinguish the structural group from the probe obstruction.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(analyze(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
