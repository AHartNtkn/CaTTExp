"""Compute free probe ranks for serial movies and flattening on strip histories.

Give probe_movies JSON, or width, gap and cuts. Each strip cut is a nonempty
list of zero-based unary-gate lanes in reading order. Letter IDs in loop
words are signed and one-based. The common peripheral has ID 1.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_chain_probe import peripheral
from semistrict_surface_component_braids import Partition
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_probe_movies import configuration_betti, movie
from semistrict_surface_rim_access import strip_arc


def fold_rank(words):
    """Rank of the image by folding the based bouquet of labelled loops."""
    vertices = Partition()
    base = vertices.at(0)
    fresh = 1
    edges = []
    for word in words:
        tail = base
        for i,letter in enumerate(word):
            head = base if i+1==len(word) else fresh
            fresh += int(head!=base)
            edges.append((tail,letter,head) if letter>0 else (head,-letter,tail))
            tail = head
    while True:
        transitions = {}
        changed = False
        for a,label,b in edges:
            for x,key,y in ((a,label,b),(b,-label,a)):
                key = (vertices.at(x),key)
                old = transitions.setdefault(key,y)
                if vertices.at(old)!=vertices.at(y):
                    vertices.unite(old,y)
                    changed = True
        if not changed:
            break
    graph = {(vertices.at(a),k,vertices.at(b)) for a,k,b in edges}
    nodes = {vertices.at(base)} | {x for a,k,b in graph for x in (a,b)}
    return 1+len(graph)-len(nodes)


def read_strip(data):
    width,gap,cuts = data['width'],data['gap'],data['cuts']
    if type(width) is not int or type(gap) is not int or not 0<gap<width or not cuts:
        raise ValueError('give an interior gap and at least one cut')
    arcs = []
    kinds = []
    first_cut = {}
    relators = []
    fresh = 2
    for i,block in enumerate(cuts):
        arc = strip_arc(width,gap,block)
        extra = [(j,) for j in range(fresh,fresh+len(block)-1)]
        fresh += len(extra)
        frame = [reduced(inv(peripheral(extra))+(1,)),*extra]
        assert peripheral(frame)==(1,)
        spelling = reduced(tuple(x for g in arc for x in
                                 (frame[g-1] if g>0 else inv(frame[-g-1]))))
        arcs.append(spelling)
        kind = 'left' if max(block)<gap else 'right' if min(block)>=gap else i
        if kind in first_cut:
            # Telescope the ladder loops from the earlier to the later cut.
            relator = tuple(range(first_cut[kind]+1,i+1))
            relators.append(relator)
        else:
            first_cut[kind] = i
        kinds.append(kind)
    images = [reduced(a+inv(b)) for a,b in zip(arcs,arcs[1:])]
    rank = fold_rank(images)
    assert rank==len(first_cut)-1
    for relator in relators:
        assert not reduced(tuple(x for g in relator for x in images[g-1]))
    return dict(raw_rank=len(images),flat_rank=fresh-1,image_rank=rank,images=images,
                cut_types=kinds,kernel_normal_generators=relators)


def point_movie(sizes):
    # One full closed packet per cut, with persistent names across seams.
    blocks = [[(0,f'g{i}_{j}') for j in range(n)] for i,n in enumerate(sizes)]
    names = ['H']+[g for block in blocks for _,g in block]
    return dict(vertex='x',path='',edges={},gates={g:['x','',''] for g in names},
                charts=[dict(diagram=[(0,'H')],slot=0,input=a,output=b)
                        for a,b in zip(blocks,blocks[1:])],
                seams=[[] for _ in sizes[2:]],probes=[[0,0,0]])


def audit():
    swept = 0
    for n in range(2,6):
        for sizes in product(range(3),repeat=n):
            c, = movie(point_movie(sizes))
            roots = [i for i in range(n) if all(sizes[j] for j in range(n) if j!=i)]
            assert c['root_gaps']==([roots[0],roots[-1]] if roots else [])
            if roots:
                assert c['free_rank']==sum(sizes)-(n-1)
                swept += 1
    # At a single point an empty-to-empty event has sphere complement.
    assert movie(point_movie([0,0]))[0]['free_rank'] is None
    # Death then birth shares no gate; the middle cut is the unique root.
    assert movie(point_movie([2,0,3]))[0]['free_rank']==3
    # Birth then death has a closed obstacle.
    assert movie(point_movie([0,2,0]))[0]['root_gaps']==[]
    print(f'{swept} rooted scalar movies with certified free ranks')

    cuts = [[(1,'a')],[(0,'b'),(1,'c')],[(1,'d')]]
    charts = [dict(diagram=[(0,'H'),(1,'p')],slot=0,input=a,output=b)
              for a,b in zip(cuts,cuts[1:])]
    gates = {g:['x','f','f'] for g in 'abcd'}
    gates.update(H=['x','ff','ff'],p=['x','',''])
    data = dict(vertex='x',path='ff',edges={'f':['x','x']},gates=gates,
                charts=charts,seams=[[]],probes=[[0,0,1]])
    component, = [c for c in movie(data) if c['probes']]
    assert component['free_rank']==3 and component['root_gaps']==[0,2]
    measured = configuration_betti(1,[0,1,2],lambda x,y,t:y==1 and t in (1,3))
    assert measured==[1,2,0,0]
    print('two crossbars have measured Betti numbers',measured,
          'and one extra stationary puncture gives free rank 3')

    counts = [0,0,0]
    blocks = [(0,),(1,),(0,1),(1,0),(0,1,0)]
    for length in range(2,6):
        for cuts in product(blocks,repeat=length):
            r = read_strip(dict(width=2,gap=1,cuts=cuts))
            if r['image_rank']==r['raw_rank']:
                counts[0] += 1
            elif all(r['images']):
                counts[1] += 1
            else:
                counts[2] += 1
    print(f'{counts[0]} faithful strip histories, {counts[1]} with a kernel despite detecting each generator, {counts[2]} with an invisible individual generator')


def typed(directory):
    ctx = (STAR,arr(STAR,v(0),v(0)))
    unary = arr(infer(ctx,v(1)),v(1),v(1))
    ctx += (unary,unary)
    right = comp2(ctx,0,identity(ctx,v(1)),v(2))
    both = comp2(ctx,0,v(3),v(2))
    ctx += (arr(infer(ctx,right),right,both),arr(infer(ctx,both),both,right))
    check_ctx(ctx)
    history = comp2(ctx,2,v(4),v(5))
    expected = arr(infer(ctx,right),right,right)
    assert infer(ctx,history)==expected
    if directory:
        out = Emitter()
        out.check_type('twoFullWidthChangesReturningToTheRightOnlyCut',ctx,history,expected)
        (directory/'ProbeSweep.agda').write_text(out.module('ProbeSweep',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        print(json.dumps(read_strip(data) if 'cuts' in data else movie(data),indent=2))
    else:
        audit()
        typed(args.agda_dir)
