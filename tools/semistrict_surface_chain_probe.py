"""Compute the exterior probe relator of a positioned chain of closed planar rules.

Use the serial gate tracks JSON format (loops are unnecessary). Use an empty
spatial path, put the marked sites in its exterior face, and give every gate
occurrence its own name, preserved across a seam. Group each outermost child's
subtree into consecutive rows at the two ends of every seam. Seam paths can
interleave the children. Generators in output words use signed one-based IDs.
"""
from argparse import ArgumentParser
from collections import Counter
from itertools import product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_component_braids import Components, restrict
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_serial_gate_tracks import motion, push, read_track
from semistrict_surface_shared_edge import braid_image


def peripheral(frame):
    return reduced(tuple(a for word in reversed(frame) for a in word))


def transport(frame, crossings):
    frame = list(frame)
    for g in crossings:
        i = abs(g)-1
        x,y = frame[i:i+2]
        if g>0:
            frame[i:i+2] = [reduced(inv(x)+y+x),x]
        else:
            frame[i:i+2] = [y,reduced(y+x+inv(y))]
    return frame


def cyclic_power(word):
    word = reduced(word)
    while len(word)>1 and word[0]==-word[-1]:
        word = word[1:-1]
    if not word:
        return (),0
    for length in range(1,len(word)+1):
        if len(word)%length==0 and word==word[:length]*(len(word)//length):
            return word[:length],len(word)//length


def children(rows,ports):
    if len(set(g for _,g in rows))!=len(rows):
        raise ValueError('gate occurrence names must distinguish all strands')
    parts = Components(rows,ports,0)
    index = {g:i for i,(_,g) in enumerate(rows)}
    blocks = []
    for c,parent in parts.parent.items():
        if parent is None:
            positions = sorted(index[g] for g in parts.subtree[c])
            if positions!=list(range(positions[0],positions[-1]+1)):
                raise ValueError('group each exterior child in the seam endpoint reading')
            blocks.append((positions[0],c))
    return sorted(blocks)


def evaluate(data):
    charts = data['charts']
    if data['path']:
        raise ValueError('the executable exterior calculation uses an empty spatial path')
    # Checks typed offsets, both port insertions, signed seam endpoints and
    # actual occurrence flow between every pair of consecutive rules.
    read_track(dict(data,charts=[dict(c,loop=()) for c in charts]))
    ports = {g:(s,t) for g,(_,s,t) in data['gates'].items()}
    rank = 0
    cap = None
    previous = None
    for j,chart in enumerate(charts):
        rows = tuple(map(tuple,chart['diagram']))
        slot = chart['slot']
        pos,site = rows[slot]
        sites = [c for _,c in children(rows,ports)]
        if ports[site]!=('','') or site not in sites:
            raise ValueError('expected an exterior point site')
        at = sites.index(site)
        def side(block):
            diagram = rows[:slot]+tuple((pos+p,g) for p,g in block)+rows[slot+1:]
            outer = children(diagram,ports)
            size = len(children(block,ports))
            labels = [c for _,c in outer]
            if labels[:at]+labels[at+size:] != sites[:at]+sites[at+1:]:
                raise ValueError('port insertion did not preserve its exterior siblings')
            return diagram,outer,size
        incoming,holes,m = side(chart['input'])
        outgoing,new_holes,n = side(chart['output'])
        if previous is None:
            rank = len(holes)
            frame = [(i+1,) for i in range(rank)]
        else:
            old_rows,old_holes = previous
            seam = data['seams'][j-1]
            # The same gate (the stable component name) represents each child
            # at both ends, even if its internal gates exchange during the seam.
            keep = {i for i,(_,g) in enumerate(old_rows) if g in {c for _,c in old_holes}}
            crossings = restrict(len(old_rows),seam,keep)
            names = [c for _,c in old_holes]
            for g in crossings:
                i = abs(g)-1
                names[i:i+2] = reversed(names[i:i+2])
            if names!=[c for _,c in holes]:
                raise ValueError('component correspondence across the seam failed')
            frame = transport(frame,crossings)
        total = peripheral(frame[at:at+m])
        if n:
            extra = [(rank+i,) for i in range(1,n)]
            rank += n-1
            fresh = [reduced(inv(peripheral(extra))+total),*extra]
            assert peripheral(fresh)==total
        else:
            if j+1!=len(charts):
                raise ValueError('an interior empty output cannot feed the next rule')
            cap = total
            fresh = []
        frame[at:at+m] = fresh
        previous = outgoing,new_holes
    root,exponent = ((),None) if cap is None else cyclic_power(cap)
    return dict(generators=rank,final_meridians=frame,attaching_word=cap,
                cyclic_root=root,power=exponent,aspherical=cap is None or exponent==1)


def fixture(seam):
    # Each moving child has a different internal diagram, including a lens
    # containing a point. The stationary puncture is itself a closed lens.
    blocks = [((0,'C'),(1,'i'),(0,'D')),((0,'y'),),((0,'J'),(0,'K'))]
    ports = {g: ('','aa') for g in ('B','C','J')}
    ports.update({g:('aa','') for g in ('E','D','K')})
    ports.update({g:('','') for g in ('i','y','site','x')})
    lens = ((0,'B'),(1,'x'),(0,'E'))
    pair = blocks[0]+blocks[1]
    chart = ((0,'site'),)+blocks[2]
    base = dict(edges={'a':['z','z']}, vertex='z',path='',
                gates={g:['z',s,t] for g,(s,t) in ports.items()})
    rule = lambda a,b: dict(diagram=chart,slot=0,input=a,output=b)
    return dict(base,charts=[rule((),lens),rule(lens,pair),rule(pair,())],
                seams=[(),cable(seam,[len(b) for b in blocks])])


def audit():
    # Check both signs of comb transport by moving an actual probe along
    # the conjugated four-strand path and along the predicted free word.
    count = 0
    frame = [(1,),(2,),(3,)]
    for length in range(4):
        for seam in product((-2,-1,1,2),repeat=length):
            full = tuple((abs(g)+1)*(1 if g>0 else -1) for g in seam)
            for j,w in enumerate(transport(frame,seam)):
                lhs = full+push((j+1,))+inv(full)
                assert braid_image(4,lhs)==braid_image(4,push(w))
                count += 1
    print(f'{count} comb transports verified in the four-strand braid group')
    counts = Counter()
    # Pure seams act on identical named input and output rows; equal
    # permutations across a seam can lead to different homotopy types.
    for length in range(4):
        for letters in product((-2,-1,1,2),repeat=length):
            seam = tuple(x for g in letters for x in (g,g))
            data = fixture(seam)
            outcome = evaluate(data)
            counts[outcome['power']] += 1
            # Independently pull the terminal two-child peripheral through
            # the actual signed seam before imposing the birth equation.
            wide = data['seams'][-1]
            before = tuple(data['charts'][-1]['input'])+((0,'J'),(0,'K'))
            gate_ports = {g:(s,t) for g,(_,s,t) in data['gates'].items()}
            assert motion(before,gate_ports,wide)==before
            small = restrict(len(before),wide,{0,3,4})
            full = tuple((abs(g)+1)*(1 if g>0 else -1) for g in small)
            terminal = full+push((2,1))+inv(full)
            unconstrained = peripheral(transport(frame,seam)[:2])
            assert braid_image(4,terminal)==braid_image(4,push(unconstrained))
            # Initial stationary generator 1; first new branch 2. In the
            # intermediate cut the two offspring have opposite meridians.
            values = [(-2,),(2,),(1,)]
            expected = reduced(tuple(x for g in unconstrained for x in
                               (values[g-1] if g>0 else inv(values[-g-1]))))
            assert outcome['attaching_word']==expected
    print(f'{sum(counts.values())} closed lens chains: {dict(sorted(counts.items()))} by cyclic exponent')
    straight = evaluate(fixture(()))
    twisted = evaluate(fixture((2,2)))
    assert straight['attaching_word']==() and straight['generators']==2
    assert twisted['power']==1 and len(twisted['cyclic_root'])==4
    print('single full twist:',twisted['attaching_word'],'cyclic root',twisted['cyclic_root'])
    data = fixture((2,2))
    assert evaluate(dict(data,charts=data['charts'][:2],seams=data['seams'][:1]))['attaching_word'] is None
    assert cyclic_power((3,1,2,1,2,-3))==((1,2),2)


def typed(directory):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    u = identity(ctx,v(0))
    path = comp2(ctx,0,v(2),v(3))
    def between(a,b):
        return arr(infer(ctx,a),a,b)
    ctx += (between(u,path),between(path,u),between(u,u))
    lens = comp2(ctx,1,v(4),v(5))
    blank = identity(ctx,u)
    pair = comp2(ctx,1,lens,v(6))
    ctx += (between(blank,lens),between(lens,pair),between(pair,blank),between(blank,blank))
    check_ctx(ctx)
    chain = comp2(ctx,2,comp2(ctx,2,v(7),v(8)),v(9))
    probe = comp2(ctx,1,comp2(ctx,1,chain,v(10)),lens)
    ty = infer(ctx,probe)
    if directory:
        out = Emitter()
        out.check_type('closedChainWithProbeAndLens',ctx,probe,ty)
        (directory/'ChainProbe.agda').write_text(out.module('ChainProbe',__doc__.splitlines()[0]))


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path,nargs='?')
    p.add_argument('--agda-dir',type=Path)
    args = p.parse_args()
    if args.input:
        print(json.dumps(evaluate(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
        typed(args.agda_dir)
