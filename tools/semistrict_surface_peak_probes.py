"""Compute the middle faces and stationary scalar tests of a planar peak history.

Use the peak-forests JSON fields with one list 'history'. Optional 'probes'
lists [row, wire gap] positions in the expanded source reading of the peak.
The returned packets use zero-based middle-row names even for repeated colours.
"""
import json
from argparse import ArgumentParser
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, subst_tm, subst_ty, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_batch_traces import coarse, validate
from semistrict_surface_birth_death_packets import follow
from semistrict_surface_component_braids import Components, restrict
from semistrict_surface_gate_forests import cable
from semistrict_surface_peak_forests import Peak, expand_roots
from semistrict_surface_probe_movies import Faces
from semistrict_surface_probe_retraction import probe_word
from semistrict_surface_serial_gate_tracks import push
from semistrict_surface_shared_edge import braid_image


def forest_packets(forest, leaves):
    """Partition retained leaf names at every root and every intermediate node."""
    packets = {}
    leaves = iter(leaves)

    def descend(address, tree):
        if tree is None:
            packet = next(leaves)
        else:
            packet = [g for i, child in enumerate(tree[1])
                      for g in descend(address + (i,), child)]
        packets['.'.join(map(str, address))] = packet
        return packet

    for i, tree in enumerate(forest):
        descend((i,), tree)
    if next(leaves, None) is not None:
        raise ValueError('middle name outside the forest')
    return packets


def solve(data):
    model = Peak(data)
    end, left, right, braid = model.normal_form(data['history'])
    rows = expand_roots(model.diagram, left, model.rules)
    # Components uses -1 for the exterior boundary. Each gate needs its own
    # occurrence name even if two leaves use the same declaration.
    named = tuple((p, i) for i, (p, _) in enumerate(rows))
    ports = {i: model.ports[g] for i, (_, g) in enumerate(rows)}
    width = len(model.path)
    faces = Faces(named, ports, width)
    cores = Components(named, ports, width).skeleton
    children = defaultdict(list)
    for core in cores.values():
        first = min(core)
        children[faces.spots[first, named[first][0]]].append(first)
    transported = follow(named, braid, ports)
    end_names = [i for _, i in transported]
    final_rows = tuple((p, rows[i][1]) for p, i in transported)
    if final_rows != expand_roots(end, right, model.rules):
        raise ValueError('middle seam misses the reversed contraction forest')
    counts = Counter()
    for position in data.get('probes', []):
        spot = tuple(position)
        if spot not in faces.spots:
            raise ValueError('probe outside its middle reading')
        counts[faces.spots[spot]] += 1
    tests = []
    for region in sorted(set(faces.spots.values())):
        keep = sorted(children[region])
        selected = set(keep)
        projected = restrict(len(rows), braid, selected)
        stationary = {i: ('','') for i in keep}
        target = follow(tuple((0, i) for i in keep), projected, stationary)
        assert [g for _, g in target] == [i for i in end_names if i in selected]
        packets = [[i] if i in selected else [] for i in range(len(rows))]
        tests.append(dict(spot=list(region), probes=counts[region], children=keep,
                          expansion=forest_packets(left, packets),
                          contraction=forest_packets(right, [packets[i] for i in end_names]),
                          seam=list(projected)))
    return dict(middle=rows, tests=tests)


def audit():
    # First seal a floating lens with two point children. Twist the resulting
    # scalar with another, then open that other scalar into a nested lens.
    outer = [(0,'B'),(1,'u'),(1,'u'),(0,'D')]
    inner = [(0,'J'),(1,'u'),(1,'u'),(0,'K')]
    gates = {g: ['x','',''] for g in ('u','P','Q','R','Z')}
    gates.update({g: ['x','','aa'] for g in ('B','J')})
    gates.update({g: ['x','aa',''] for g in ('D','K')})
    data = dict(edges={'a':['x','x']}, gates=gates, vertex='x', path='',
                diagram=outer+[(0,'P'),(0,'Z')],
                rules={'close':['Q',outer], 'open':['P',[(0,'B'),(1,'R'),(0,'D')]],
                       'inside':['R',inner], 'erase':['Z',[]]},
                orientations={'close':'contract','open':'expand','inside':'expand','erase':'expand'})
    histories = meridians = 0
    for sign, length in product((1,-1), range(5)):
        word = (sign,)*length
        after = int(length % 2 == 0)
        mixed = [[0,0,'close'],*word,[after,'open'],[after+1,'inside'],[7,'erase']]
        ribbon = cable(word,[4,6])
        sorted_history = [[5,'erase'],[4,'open'],[5,'inside'],*ribbon,
                          [0 if after else 6,0,'close']]
        result = solve(dict(data,history=mixed,probes=[[0,0],[1,1],[6,2],[6,2]]))
        assert result == solve(dict(data,history=sorted_history,probes=[[0,0],[1,1],[6,2],[6,2]]))
        outside, old_inside, new_inside, deep = result['tests']
        assert [(t['children'],t['probes']) for t in result['tests']] == [
            ([0,4],1),([1,2],1),([5],0),([6,7],2)]
        assert outside['expansion']['4']==[4] and outside['expansion']['5']==[]
        assert old_inside['contraction'][str(0 if after else 6)]==[1,2]
        assert deep['expansion']['4']==[6,7]
        assert braid_image(2,outside['seam'])==braid_image(2,word)
        assert new_inside['seam']==[] and not deep['seam']
        histories += 1
        # Execute an actual probe meridian/commutator around either packet
        # in the exterior, then keep its representative in each packet.
        positioned = ((0,'probe'),)+tuple(result['middle'])
        ports = {g:(s,t) for g,(_,s,t) in gates.items()}
        ports['probe'] = ('','')
        for letters in [(1,),(2,),(-1,),(1,2,-1,-2),(2,1,-2,-1)]:
            motion = cable(push(letters),[1,4,6])
            assert follow(positioned,motion,ports)==positioned
            image = restrict(len(positioned),motion,{0,1,5})
            assert probe_word(3,image)==letters
            meridians += 1
    print(f'{histories} interleaving comparisons on four middle faces; '
          f'{meridians} signed probe words recovered after the stationary specialization')


def audit_faces():
    # A changing gate on an anchored wire grows a lens. Several floating
    # points are born inside the lens and consumed together at the next use.
    for size in range(5):
        block = [(0,'split')]+[(1,f'p{i}') for i in range(size)]+[(0,'join')]
        gates = {g:['x','a','a'] for g in ('E','C','left','right')}
        gates.update(split=['x','a','aa'],join=['x','aa','a'])
        gates.update({g:['x','',''] for _,g in block[1:-1]})
        data = dict(vertex='x',path='a',edges={'a':['x','x']},gates=gates,
                    diagram=[(0,'left')],rules={'E':['left',block],'C':['right',block]},
                    orientations={'E':'expand','C':'contract'},history=[[0,'E'],[0,0,'C']])
        batches = [dict(diagram=[(0,g)],sites={g:dict(input=a,output=b)})
                   for g,a,b in [('E',data['diagram'],block),('C',block,[(0,'right')])]]
        movie = dict(data,batches=batches,seams=[[]])
        validate(movie)
        ranks,gaps,nodes = coarse(movie)
        tests = solve(data)['tests']
        assert len(ranks)==len(tests)==3 and not any(ranks.values())
        middle = gaps[1]
        assert len({nodes.at((1,tuple(t['spot']))) for t in tests})==len(ranks)
        for t in tests:
            assert middle.holes[tuple(t['spot'])]==len(t['children'])
        assert sorted(len(t['children']) for t in tests)==[0,0,size]
        assert all(t['expansion']['0']==t['contraction']['0']==t['children'] for t in tests)
    print('15 middle faces match the independent temporal incidence calculation on nonempty wire ports')


def typed(directory):
    ctx = (STAR,)
    one = identity(ctx,v(0))
    scalar = arr(infer(ctx,one),one,one)
    ctx += (scalar,)*4
    pair = comp2(ctx,1,v(2),v(3))
    def hom(a,b):
        return arr(infer(ctx,a),a,b)
    empty = identity(ctx,one)
    ctx += (hom(v(1),pair),hom(pair,v(4)),hom(empty,empty))
    check_ctx(ctx)
    term = comp2(ctx,2,comp2(ctx,1,v(5),v(7)),comp2(ctx,1,v(6),identity(ctx,empty)))
    target = (STAR,scalar,scalar,hom(empty,empty))
    check_ctx(target)
    packet = comp2(target,1,v(1),v(2))
    rest = identity(target,packet)
    images = [v(0),packet,v(1),v(2),packet,rest,rest,v(3)]
    for j,ty in enumerate(ctx):
        assert infer(target,images[j])==subst_ty(ty,images[:j])
    mapped = subst_tm(term,images)
    ty = subst_ty(infer(ctx,term),images)
    assert infer(target,mapped)==ty
    if directory:
        out = Emitter()
        out.check_type('expansionProbeContraction',ctx,term,infer(ctx,term))
        out.check_type('stationaryPackets',target,mapped,ty)
        (directory/'PeakProbes.agda').write_text(out.module('PeakProbes',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(solve(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
        audit_faces()
        typed(args.agda_dir)
