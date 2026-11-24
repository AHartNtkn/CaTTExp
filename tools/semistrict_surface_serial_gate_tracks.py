"""Check signed tracks through dependent changes of planar gates."""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_component_braids import restrict
from semistrict_surface_gate_forests import Presentation, cable
from semistrict_surface_history_group import exchange, inv, reduced
from semistrict_surface_shared_edge import braid_image


def motion(diagram, ports, braid):
    current = diagram
    for letter in braid:
        current = exchange(current,letter,ports)
        if current is None:
            raise ValueError('illegal planar switch')
    return current


def meridian(i):
    approach = tuple(range(1,i+1))
    return approach+(i+1,i+1)+inv(approach)


def push(free_word):
    return tuple(s for a in free_word for s in
                 (meridian(a-1) if a>0 else inv(meridian(-a-1))))


def read_track(data):
    """Validate a tuple of based one-site loops and determine its nullity."""
    charts, seams = data['charts'], data['seams']
    if not charts or len(seams)+1!=len(charts):
        raise ValueError('expected a nonempty chain and one path per seam')
    previous = None
    first = None
    for i, chart in enumerate(charts):
        diagram = tuple((p,g) for p,g in chart['diagram'])
        j = chart['slot']
        if not 0<=j<len(diagram):
            raise ValueError('site index outside the diagram')
        pos, site = diagram[j]
        if sum(g==site for _,g in diagram)!=1:
            raise ValueError('the active marker needs a name distinct from ordinary gates')
        inputs, outputs = chart['input'], chart['output']
        model = Presentation(dict(data, diagram=diagram, rules={
            'input':[site,inputs], 'output':[site,outputs]}))
        loop = chart['loop']
        if not all(type(b) is int and b!=0 and abs(b)<len(diagram) for b in loop):
            raise ValueError('invalid marker braid letter')
        if motion(diagram,model.ports,loop)!=diagram:
            raise ValueError('one-site path is not a loop')
        # All intermediate positions have fixed names on a based loop of
        # the history. Check the port matching even when gate colours repeat.
        pure = list(range(len(diagram)))
        for b in loop:
            k = abs(b)-1
            pure[k:k+2] = reversed(pure[k:k+2])
        if pure!=list(range(len(diagram))):
            raise ValueError('a named site loop must have trivial permutation')
        ends = []
        for block in (inputs,outputs):
            expanded = diagram[:j]+tuple((pos+p,g) for p,g in block)+diagram[j+1:]
            widths = [1]*len(diagram)
            widths[j] = len(block)
            word = cable(loop,widths)
            if motion(expanded,model.ports,word)!=expanded:
                raise ValueError('expanded loop does not close')
            ends.append((expanded,word,set(range(j,j+len(block)))))
        source, target = ends
        if i==0:
            if braid_image(len(source[0]),source[1])!=braid_image(len(source[0]),()):
                raise ValueError('initial loop is nontrivial')
            first = braid_image(len(diagram),loop)!=braid_image(len(diagram),())
        else:
            prev_diagram, prev_loop, descendants = previous
            seam = tuple(seams[i-1])
            if any(type(b) is not int or not 0<abs(b)<len(prev_diagram) for b in seam):
                raise ValueError('invalid seam braid letter')
            if motion(prev_diagram,model.ports,seam)!=source[0]:
                raise ValueError('seam does not reach the next input diagram')
            order = list(range(len(prev_diagram)))
            for b in seam:
                k = abs(b)-1
                order[k:k+2] = reversed(order[k:k+2])
            if not any(order[k] in descendants for k in source[2]):
                raise ValueError('the two consecutive uses share no gate')
            if braid_image(len(order),prev_loop+seam)!=braid_image(len(order),seam+source[1]):
                raise ValueError('loops disagree at the seam')
        previous = target
    if braid_image(len(target[0]),target[1])!=braid_image(len(target[0]),()):
        raise ValueError('final loop is nontrivial')
    return {'nonzero':first,'sites':len(charts)}


def audit_chain(holes):
    # First a portless change creates a closed lens, then a second change
    # consumes it and produces two points, and a third consumes those points.
    # Each stationary hole is physically a separate two-gate lens.
    hole_rows = tuple((0,f'{name}{i}') for i in range(holes) for name in ('B','D'))
    ports = {g:(('','ab') if g.startswith('B') else ('ab','')) for _,g in hole_rows}
    ports.update(B=('','ab'),D=('ab',''),X=('',''),p=('',''),q=('',''),site=('',''))
    site = ((0,'site'),)+hole_rows
    blocks = [(),((0,'B'),(1,'X'),(0,'D')),((0,'p'),(0,'q')),()]
    hole_sizes = [2]*holes
    meridians = [meridian(i) for i in range(holes)]
    word = meridians[0]
    for m in meridians[1:]:
        word += m+inv(word)+inv(m)
    start = braid_image(holes+1,word)
    assert start!=braid_image(holes+1,())
    steps = 0
    charts,seams = [],[]
    for i in range(3):
        site_loop = cable(word,[1]+hole_sizes)
        charts.append(dict(diagram=site,slot=0,input=blocks[i],output=blocks[i+1],loop=site_loop))
        assert motion(site,ports,site_loop)==site
        keep = {0}|{1+2*j for j in range(holes)}
        assert braid_image(holes+1,restrict(len(site),site_loop,keep)) == braid_image(holes+1,word)
        for b in (blocks[i],blocks[i+1]):
            diagram = b+hole_rows
            expanded = cable(word,[len(b)]+hole_sizes)
            assert motion(diagram,ports,expanded)==diagram
            if not b:
                assert braid_image(len(diagram),expanded)==braid_image(len(diagram),())
        if i<2:
            turn = meridians[(i+1)%holes]
            transported = inv(turn)+word+turn
            widths = [len(blocks[i+1])]+hole_sizes
            left = cable(word,widths)+cable(turn,widths)
            right = cable(turn,widths)+cable(transported,widths)
            seam_diagram = blocks[i+1]+hole_rows
            assert motion(seam_diagram,ports,left)==motion(seam_diagram,ports,right)==seam_diagram
            assert braid_image(len(seam_diagram),left)==braid_image(len(seam_diagram),right)
            seams.append(cable(turn,widths))
            steps += len(left)+len(right)
            word = transported
    data = dict(charts=charts,seams=seams,vertex='x',path='',
                edges={'a':['x','x'],'b':['x','x']},
                gates={g:['x',*pair] for g,pair in ports.items()})
    assert read_track(data)['nonzero']
    trivial = [dict(ch,loop=()) for ch in charts]
    assert not read_track(dict(data,charts=trivial))['nonzero']
    try:
        read_track(dict(data,charts=[charts[0],*trivial[1:]]))
    except ValueError as err:
        assert 'disagree at the seam' in str(err)
    else:
        raise AssertionError('an incompatible tuple passed the seam test')
    print(f'{holes} holes: nonzero first-site commutator, two matching seams ({steps} signed switches)')


def audit_merger():
    # One offspring is consumed together with the first original spectator.
    # After retaining just that offspring its incoming braid must be obtained
    # by duplicating the spectator. Test this subgroup by its split retraction.
    checked = rejected = 0
    for length in range(5):
        for letters in product((1,-1,2,-2),repeat=length):
            w = push(letters)
            # First site has a side branch as well as the continuing strand.
            full = cable(w,[2,1,1])
            single = restrict(4,full,{1,2,3})
            bare = restrict(3,single,{1,2})
            assert braid_image(2,bare)==braid_image(2,())
            repaired = cable(bare,[2,1])
            allowed = braid_image(3,single)==braid_image(3,repaired)
            assert allowed==(not reduced(letters))
            rejected += not allowed
            checked += 1
    print(f'{checked} first-site words tested at a merger with a spectator, {rejected} nonzero obstructions to seam matching')


def typed(directory):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    u = identity(ctx,v(0))
    ab = comp2(ctx,0,v(2),v(3))
    def between(a,b):
        return arr(infer(ctx,a),a,b)
    ctx += (between(u,ab),between(ab,u),between(u,u))
    lens = comp2(ctx,1,v(4),v(5))
    pair = comp2(ctx,1,v(6),v(6))
    blank = identity(ctx,u)
    ctx += (between(blank,lens),between(lens,pair),between(pair,blank))
    check_ctx(ctx)
    closed = comp2(ctx,2,comp2(ctx,2,v(7),v(8)),v(9))
    assert infer(ctx,closed)==between(blank,blank)
    outside = comp2(ctx,1,lens,closed)
    if directory:
        out = Emitter()
        out.check_type('closedChain',ctx,closed,between(blank,blank))
        out.check_type('besideLens',ctx,outside,infer(ctx,outside))
        (directory/'SerialGateTracks.agda').write_text(out.module('SerialGateTracks',__doc__))


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path,nargs='?',help='JSON with edges, gates, vertex, path, charts and seams')
    p.add_argument('--agda-dir',type=Path)
    args = p.parse_args()
    if args.input:
        print(json.dumps(read_track(json.loads(args.input.read_text()))))
    else:
        for h in (2,3):
            audit_chain(h)
        audit_merger()
        typed(args.agda_dir)
