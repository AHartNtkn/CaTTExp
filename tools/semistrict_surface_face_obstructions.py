"""Compute named degree-five and degree-six groups on reducible point-site movies.

After pruning the branches of each face, classify through strands and
positive-port structural networks with any number of free sites. An
unclassified face is left unresolved. --emit includes scalar two-cap tests.
"""
from argparse import ArgumentParser
from math import comb
import json
from pathlib import Path

from semistrict_surface_face_factors import factors
from semistrict_surface_movie_spine import expanded, presentation
from semistrict_surface_pocket_closure import enclose
from semistrict_surface_scalar_leaves import prune, swapped
from semistrict_surface_spherical_relations import simplify


def scalar_movie(face):
    def rows(wires):
        return [(0, 'g'+str(w)) for w in wires]

    first = next((b['points'] for b in face['boundaries'] if 'birth' in b),face.get('initial'))
    seams = face['interval_braids']
    live = list(first)
    gates,charts = {},[]
    for step,word in zip(face['steps'],seams):
        live = swapped(live,word)
        j = step['slot']
        site = (0,'s'+str(step['use']))
        a,b = step['input'],step['output']
        assert live[j:j+len(a)]==a
        chart = dict(diagram=rows(live[:j])+[site]+rows(live[j+len(a):]),
                     slot=j,input=rows(a),output=rows(b))
        gates.update({g:['x','',''] for _,g in chart['diagram']+chart['input']+chart['output']})
        charts.append(chart)
        live[j:j+len(a)] = b
    internal = list(seams[1:-1])
    # Realize each nonconstant exterior path verbatim. A unary identity bead
    # at its exterior cut is smoothed by the same strand reduction as usual.
    for before,wire_order,word in [(True,first,seams[0]),(False,swapped(live,seams[-1]),seams[-1])]:
        if word:
            name = 'start_bead' if before else 'end_bead'
            gates[name] = ['x','','']
            row = rows(wire_order)
            chart = dict(diagram=[(0,name),*row[1:]],slot=0,input=row[:1],output=row[:1])
            if before:
                charts.insert(0,chart)
                internal.insert(0,word)
            else:
                charts.append(chart)
                internal.append(word)
    return dict(vertex='x',path='',edges={},gates=gates,charts=charts,seams=internal)


def core_presentation(movie):
    """Delete the free sites, joining all intervening signed paths."""
    charts,seams,word = [],[],[]
    for i,c in enumerate(movie['charts']):
        if c['input'] or c['output']:
            if charts:
                seams.append(word)
            charts.append(c)
            word = []
        if i<len(movie['seams']):
            word.extend(movie['seams'][i])
    core = dict(movie,charts=charts,seams=seams)
    spine = presentation(core)
    edges = len(expanded(charts[0],'input'))+sum(len(c['output']) for c in charts)
    assert spine['betti']==[1,edges-len(charts),0]
    rank,rels,spheres = simplify(spine['generators'],spine['faces'])
    assert not spheres
    return dict(generators=rank,relators=rels,first_betti=edges-len(charts))


def obstructions(data, emit=False):
    out = []
    for face in factors(data)['factors']:
        red = prune(scalar_movie(face))
        row = dict(face=face['face'],uses=[s['use'] for s in face['steps']])
        if not red['other_sites']:
            m,k = red['through'],len(red['isolated_sites'])
            row.update(model='points',punctures=m,probes=k,
                       free_group_factors=k if m else 0,collision_pairs=comb(k,2))
        else:
            arities = [(len(c['input']),len(c['output'])) for c in red['movie']['charts']]
            if all(a and b for a,b in arities if a or b):
                k = len(red['isolated_sites'])
                row.update(model='positive core',probes=k,collision_pairs=comb(k,2))
                if k:
                    row['probe_group'] = core_presentation(red['movie'])
            else:
                row['model'] = 'unresolved'
        if emit and row.get('probes'):
            row['scalar_closure'] = enclose(red['movie'],'anchored')
            row['leading_braid'] = red['initial_braid']
            row['trailing_braid'] = red['final_braid']
        out.append(row)
    known = all(r['model']!='unresolved' for r in out)
    return dict(faces=out,classified=known,
                named_degree_five_nonfilling=(True if any(r.get('free_group_factors') or r.get('probe_group') for r in out)
                                              else False if known else None),
                degree_six_nonfilling=(True if any(r.get('collision_pairs') for r in out)
                                       else False if known else None))


def pockets():
    # An occupied lens containing a second occupied lens. Two probe programs
    # start at independent births and contract along their private terminal legs.
    gates = {g:['x','',''] for g in ['z','p','q']}
    gates.update(B=['x','','ff'],D=['x','ff',''])
    inner = [(1,'B'),(2,'q'),(2,'q'),(2,'q'),(1,'D')]
    outer = [(0,'B'),(1,'p'),*inner,(0,'D')]
    charts = [dict(diagram=[(0,'z')],slot=0,input=[],output=outer)]
    live = outer.copy()
    def step(pos,slot,take,give):
        old = live[slot:slot+take]
        assert all(j==pos for j,_ in old)
        charts.append(dict(diagram=live[:slot]+[(pos,'z')]+live[slot+take:],slot=slot,
                           input=[(0,g) for _,g in old],output=[(0,g) for g in give]))
        live[slot:slot+take] = [(pos,g) for g in give]
    step(1,1,0,['q'])
    step(2,4,0,['q'])
    step(1,1,1,[])
    step(2,3,1,[])
    step(2,3,0,[])
    step(1,1,0,[])
    step(2,3,0,[])
    assert live==outer
    charts.append(dict(diagram=[(0,'z')],slot=0,input=outer,output=[]))
    return dict(vertex='x',path='',edges={'f':['x','x']},gates=gates,
                charts=charts,seams=[[] for _ in charts[1:]])


def audit():
    from semistrict_surface_face_factors import sample
    from semistrict_surface_spherical_relations import analyze

    d = pockets()
    # Restrictions spanning both caps and a single cap at either end.
    for start,end in [(0,len(d['charts'])),(1,len(d['charts'])),(0,len(d['charts'])-1),
                      (1,len(d['charts'])-1)]:
        dd = dict(d,charts=d['charts'][start:end],seams=d['seams'][start:end-1])
        answer = obstructions(dd,True)
        assert answer['classified'] and answer['degree_six_nonfilling'] and answer['named_degree_five_nonfilling']
        points = sorted((r['punctures'],r['probes']) for r in answer['faces'] if r.get('punctures'))
        assert points==[(2,2),(3,3)]
        for r in answer['faces']:
            if r.get('punctures'):
                # Independently compute the complement seen by one extra
                # probe around all retained free sites and capped spectators.
                spine = analyze(r['scalar_closure'])
                assert spine['betti']==[1,r['punctures'],r['probes']+1]
    # Exterior signed paths can be accumulated during a different face's
    # sites, on either side of the first or last retained use.
    framed = dict(boundaries=[],initial=[7,9],final=[9,7],interval_braids=[[1],[-1,-1]],
                  steps=[dict(use=4,slot=1,input=[],output=[])])
    bare = prune(scalar_movie(framed))
    assert bare['through']==2 and len(bare['isolated_sites'])==1
    assert bare['initial_braid']==[1] and bare['final_braid']==[-1,-1]
    # A positive split and merge, interleaved with a free event, inside
    # the innermost occupied face. One daughter winds around a spectator.
    original = d['charts'][0]['output']
    s = 3
    def change(row,j,take,give):
        return dict(diagram=row[:j]+[(2,'z')]+row[j+take:],slot=j,
                    input=[(0,'q')]*take,output=[(0,'q')]*give)
    split = change(original,s,1,2)
    middle = original[:s]+[(2,'q')]+original[s:]
    free = change(middle,s,0,0)
    merge = change(middle,s,2,1)
    for twist in (-1,0,1):
        seam = [twist*(s+2)]*(2*abs(twist))
        branch = dict(d,charts=[d['charts'][0],split,free,merge,d['charts'][-1]],
                      seams=[[],seam,[],[]])
        ans = obstructions(branch,True)
        core, = [r for r in ans['faces'] if r['model']=='positive core']
        assert core['probe_group']['first_betti']==4 and core['probes']==1
        assert ans['named_degree_five_nonfilling'] and not ans['degree_six_nonfilling']
        assert analyze(core['scalar_closure'])['betti']==[1,4,2]
    for turns in range(-3,4):
        word = (1 if turns>=0 else -1,)*(2*abs(turns))
        r = obstructions(sample(True,word))
        assert not r['classified'] and r['degree_six_nonfilling'] is None
    print('Two occupied nested faces yield (2 punctures, 2 probes) and (3 punctures, 3 probes).')
    print('All four choices of exterior cuts and eight scalar complement spines agree.')
    print('Three split-merge tangles have a probe group of first Betti number four and no collision pair.')
    print('Seven signed examples retain a face outside these tests.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--emit',action='store_true',help='include the scalar two-cap tests')
    args = parser.parse_args()
    if args.input:
        print(json.dumps(obstructions(json.loads(args.input.read_text()),args.emit),indent=2))
    else:
        audit()
