"""Concentrate a one-sided scalar face forest into signed packet births and free sites.

Input is a positioned closed-port point-site movie. Each face may choose its
own time orientation after pruning; other faces are reported as unresolved.
"""
from argparse import ArgumentParser
import json
from pathlib import Path

from semistrict_surface_cap_threads import artin, joined
from semistrict_surface_face_factors import factors
from semistrict_surface_face_obstructions import scalar_movie
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_movie_spine import expanded
from semistrict_surface_scalar_leaves import prune, swapped
from semistrict_surface_serial_gate_tracks import read_track


def evaluate(word,images):
    return joined(images[i-1] if i>0 else inv(images[-i-1]) for i in word)


def meridians(charts,seams,tail,terminal_count):
    """A free basis in terms of the final meridians, and those meridians in the basis."""
    if not charts:
        ids = [(i+1,) for i in range(terminal_count)]
        # With no events, the terminal meridians themselves form a basis.
        return ids,ids
    initial_count = len(expanded(charts[0],'input'))
    live = [(i+1,) for i in range(initial_count)]
    count = initial_count
    words = [list(w) for w in seams]+[tail]
    for c,seam in zip(charts,words,strict=True):
        j,n,p = c['slot'],len(c['input']),len(c['output'])
        if p:
            acc = live[j] if n else ()
            packet = [(count+i+1,) for i in range(p-1)]
            count += p-1
            live[j:j+n] = [*packet,reduced(inv(joined(packet))+acc)]
        else:
            assert n==0
        for letter in seam:
            artin(live,letter)
    final = live
    assert len(final)==terminal_count
    live = [(i+1,) for i in range(terminal_count)]
    at_steps = []
    for c,seam in reversed(list(zip(charts,words,strict=True))):
        for letter in inv(seam):
            artin(live,letter)
        j,n,p = c['slot'],len(c['input']),len(c['output'])
        packet = live[j:j+p]
        at_steps.append(packet[:-1])
        incoming = joined(packet)
        if not n:
            assert not evaluate(incoming,final)
        live[j:j+p] = [incoming] if n else []
    basis = live+[w for row in reversed(at_steps) for w in row]
    assert [evaluate(w,final) for w in basis]==[(i+1,) for i in range(count)]
    return basis,final


def packets(reduction):
    movie = reduction['movie']
    charts,seams = movie['charts'],movie['seams']
    start,end = reduction['initial'],reduction['final']
    first,last = reduction['initial_braid'],reduction['final_braid']
    backwards = any(len(c['input'])>1 for c in charts)
    if backwards:
        if any(len(c['output'])>1 for c in charts):
            return dict(classified=False)
        charts = [dict(c,input=c['output'],output=c['input']) for c in reversed(charts)]
        seams = [inv(w) for w in reversed(seams)]
        start,end = end,start
        first,last = inv(last),inv(first)

    leaves = {g:[g] for g in end}
    def flatten(row):
        return [leaf for g in row for leaf in leaves[g]]
    for c in reversed(charts):
        if c['input']:
            (_,g), = c['input']
            leaves[g] = flatten([h for _,h in c['output']])
            assert leaves[g]
    def rows(names):
        return [(0,g) for g in names]
    def names(row):
        return [g for _,g in row]
    live = list(start)
    pending = list(cable(first,[len(leaves[g]) for g in live]))
    lead,inside,middle = [],[],[]
    k,b = 0,0
    for i,c in enumerate(charts):
        live = names(expanded(c,'input'))
        j = c['slot']
        if not c['input']:
            left = flatten(live[:j])
            after = flatten(names(c['output']))
            marker = c['diagram'][j][1]
            middle.append(dict(diagram=rows(left+[marker]+flatten(live[j:])),slot=len(left),
                               input=[],output=rows(after)))
            if len(middle)==1:
                lead = pending
            else:
                inside.append(pending)
            pending = []
            k += not after
            b += bool(after)
        live = names(expanded(c,'output'))
        if i<len(seams):
            pending.extend(cable(seams[i],[len(leaves[g]) for g in live]))
    pending.extend(cable(last,[len(leaves[g]) for g in live]))
    compressed = dict(movie,charts=middle,seams=inside)
    if middle:
        read_track(dict(compressed,charts=[dict(c,loop=[]) for c in middle]),require_shared_gate=False)
        assert swapped(flatten(start),lead)==names(expanded(middle[0],'input'))
        assert swapped(names(expanded(middle[-1],'output')),pending)==end
    else:
        assert swapped(flatten(start),pending)==end
    before_basis,before_ends = meridians(charts,seams,last,len(end))
    after_basis,after_ends = meridians(middle,inside,pending,len(end))
    forward = [evaluate(w,after_ends) for w in before_basis]
    backward = [evaluate(w,before_ends) for w in after_basis]
    identity = [(i+1,) for i in range(len(end)-b)]
    assert [evaluate(w,backward) for w in forward]==identity
    assert [evaluate(w,forward) for w in backward]==identity
    dimension = 0 if b==2 and not start else max(0,b-1)
    return dict(classified=True,reversed=backwards,initial=flatten(start),final=end,
                leading_braid=lead,trailing_braid=pending,movie=compressed,
                packet_births=b,probes=k,probe_group_rank=len(end)-b,
                structural_dimension_bound=dimension,probe_basis_map=forward,probe_basis_inverse=backward)


def analyze_faces(data):
    return [dict(face=f['face'],**packets(prune(scalar_movie(f)))) for f in factors(data)['factors']]


def audit():
    from itertools import product
    from semistrict_surface_scalar_leaves import sample
    from semistrict_surface_movie_spine import presentation

    trials = 0
    for signs in product((-1,0,1),repeat=3):
        def twist(i,s):
            return [i*s]*(2*abs(s))
        # A source-rooted tree and two birth-rooted trees interleave. A
        # short death prunes one twig, and a free event remains in their face.
        changes = [(1,0,2),(0,1,2),(1,0,3),(2,1,2),(2,1,0),(1,0,0),(6,1,2)]
        seams = [twist(1,signs[0]),[],twist(4,signs[1]),[],[],twist(6,signs[2])]
        d = sample(['a'],changes,seams)
        for reverse in (False,True):
            cur = dict(d,charts=[dict(c,input=c['output'],output=c['input']) for c in reversed(d['charts'])],
                       seams=[inv(w) for w in reversed(d['seams'])]) if reverse else d
            ans = packets(prune(cur))
            assert ans['reversed']==reverse and ans['packet_births']==2 and ans['probes']==1
            assert ans['structural_dimension_bound']==1 and ans['probe_group_rank']==6
            for chart in ans['movie']['charts']:
                assert not chart['input']
            # Compare the actual signed graph complement before and after
            # concentrating all trees. One free site contributes one sphere.
            for tested in (cur,ans['movie']):
                spine = presentation(tested)
                assert spine['betti']==[1,ans['probe_group_rank'],1]

            trials += 1
    # A signed end transport before the first or after the last birth has
    # to cable the whole terminal leaf list of each transported root.
    d = sample(['a','a'],[(0,1,2),(2,0,2)],[[2,2]])
    red = prune(d)
    red['initial_braid'] = [1,1]
    ans = packets(red)
    assert ans['leading_braid']==[*cable([1,1],[2,1]),2,2]
    # Run the normal wired entry on a host whose two actual ports are
    # occupied. The terminal ancestor packet may contain many real children.
    def enclosed(row):
        return [(0,'B')]+[(1,g) for _,g in row]+[(0,'D')]
    charts = d['charts']
    z = [(0,'outer')]
    wired = dict(d,edges={'f':['x','x']},gates=dict(d['gates'],B=['x','','ff'],D=['x','ff',''],outer=['x','','']))
    wired['charts'] = [dict(diagram=z,slot=0,input=[],output=enclosed(expanded(charts[0],'input')))]
    wired['charts'] += [dict(c,diagram=enclosed(c['diagram']),slot=c['slot']+1) for c in charts]
    wired['charts'].append(dict(diagram=z,slot=0,input=enclosed(expanded(charts[-1],'output')),output=[]))
    wired['seams'] = [[],*[[g+1 if g>0 else g-1 for g in w] for w in d['seams']],[]]
    case, = [r for r in analyze_faces(wired) if r['packet_births']]
    assert case['packet_births']==1 and len(case['initial'])==3 and case['probe_group_rank']==4
    # Two packets with an intervening split, a probe and signed transport.
    d = sample([],[(0,0,2),(1,1,2),(2,0,2),(0,0,0)],[[-1,-1],[2,2],[-3,-3]])
    for movie in (d,dict(d,charts=[dict(c,input=c['output'],output=c['input']) for c in reversed(d['charts'])],
                         seams=[inv(w) for w in reversed(d['seams'])])):
        case, = analyze_faces(movie)
        assert case['initial']==[] and case['packet_births']==2 and case['probes']==1
        assert case['structural_dimension_bound']==0 and case['probe_group_rank']==3
    print(f'{trials} signed forests and their reversals replayed at their written ends.')
    print('Each has two independent packet births, one probe, and a free complement group of rank six.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(analyze_faces(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
