"""Test rim access on ordinary planar ports and read a one-probe strip loop.

Use edges, gates and rules as for port_angles. Alternatively JSON fields
width, input, output, gap specify a full-width rule. Each port lists the
zero-based wire of each unary gate in drawing order, repetitions allowed.
"""
from argparse import ArgumentParser
from itertools import combinations, product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_chain_probe import peripheral
from semistrict_surface_gate_forests import Presentation
from semistrict_surface_history_group import exchange, inv, reduced
from semistrict_surface_probe_retraction import probe_word


def rim(model,site,block):
    x,s,t = model.gates[site]
    if model.sweep(x,s,block)!=t:
        raise ValueError('port has incorrect spatial boundary')
    if not block:
        return dict(passes=False,reason='no gate')
    if not s and not t:
        return dict(passes=True,kind='point')
    wires = list(range(len(s)))
    for pos,g in block:
        a,b = model.ports[g]
        wires[pos:pos+len(a)] = [None]*len(b)
    legs = list(range(1,len(s)+1))
    for j,old in reversed(list(enumerate(wires))):
        legs.append(len(s)+1+j if old is None else -(old+1))
    # Proper arms have independent coordinates. The two ends of a through
    # chord contribute opposite signs in a single coordinate.
    n = len(s)+len(t)
    curr = [0]*n
    prefix = []
    for arm in legs:
        prefix.append(curr.copy())
        curr[abs(arm)-1] += 1 if arm>0 else -1
    period = tuple(curr)
    flank = bool(s and t and (wires[0]==0 or wires[-1]==len(s)-1))
    seen = {}
    collision = None
    if any(period):
        k = period.index(1)
        for i,p in enumerate(prefix):
            normal = tuple(a-p[k]*b for a,b in zip(p,period))
            if normal in seen:
                j = seen[normal]
                collision = [j,i,prefix[j][k]-p[k]]
                break
            seen[normal] = i
    else:
        collision = [0,0,1]
    assert flank==(collision is not None)
    return dict(passes=collision is None,arms=legs,period=period,collision=collision)


def check_rules(data):
    if not data['rules']:
        return {}
    site = next(iter(data['rules']))
    model = Presentation(dict(data,vertex=data['gates'][site][0],path='',diagram=[],rules={}))
    return {k:{side:rim(model,k,io[side]) for side in ('input','output')} for k,io in data['rules'].items()}


def strip(data):
    width,gap = data['width'],data['gap']
    if type(width) is not int or type(gap) is not int or not 0<gap<width:
        raise ValueError('expect an interior gap on a positive width')
    def arc(block):
        if not block or any(type(p) is not int or not 0<=p<width for p in block):
            raise ValueError('give nonempty lists of valid unary gate positions')
        ports = {str(i):('a','a') for i in range(len(block))}
        ports['probe'] = ('','')
        rows = ((gap,'probe'),)+tuple((p,str(i)) for i,p in enumerate(block))
        word = []
        for i in range(1,len(rows)):
            for b in (i,-i):
                moved = exchange(rows,b,ports)
                if moved is not None:
                    break
            if moved is None:
                raise ValueError('probe cannot pass the given gate')
            rows = moved
            word.append(b)
        assert rows[-1]==(gap,'probe')
        # Return along the reference arc on the same side of the entire
        # packet on both ports. It expands from a single flat marker.
        ref = tuple(range(1,len(rows)))
        return probe_word(len(rows),tuple(word)+inv(ref))
    a,b = data['input'],data['output']
    u,vword = arc(a),arc(b)
    total = peripheral([(i+1,) for i in range(len(a))])
    extra = [(i,) for i in range(len(a)+1,len(a)+len(b))]
    frame = [reduced(inv(peripheral(extra))+total),*extra]
    assert peripheral(frame)==total
    target = reduced(tuple(letter for g in vword for letter in
                           (frame[g-1] if g>0 else inv(frame[-g-1]))))
    word = reduced(u+inv(target))
    return dict(raw_strip_rank=1,flat_rank=len(a)+len(b)-1,word=word,detected=bool(word))


def audit():
    shapes = [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1)]
    gates = {f'g{i}{j}':['x','a'*i,'a'*j] for i,j in shapes}
    gates.update({f'S{i}{j}':['x','a'*i,'a'*j] for i in range(4) for j in range(5)})
    model = Presentation(dict(edges={'a':['x','x']},gates=gates,vertex='x',path='',diagram=[],rules={}))
    good = bad = middle = 0
    for n in range(4):
        def walk(rows,w):
            nonlocal good,bad,middle
            if rows and (n or w):
                result = rim(model,f'S{n}{w}',rows)
                arms,P = result['arms'],result['period']
                if result['passes']:
                    good += 1
                    middle += any(a<0 for a in arms)
                else:
                    bad += 1
                    i,j,d = result['collision']
                    delta = [d*t for t in P]
                    for k in range(len(arms)):
                        sign = int(k<j)-int(k<i)
                        arm = arms[k]
                        delta[abs(arm)-1] += sign*(1 if arm>0 else -1)
                    assert not any(delta) and (i!=j or d)
            if len(rows)<3:
                for a,b in shapes:
                    if w+b-a<=4:
                        for p in range(w-a+1):
                            walk(rows+[(p,f'g{a}{b}')],w-a+b)
        walk([],n)
    assert middle and bad
    print(f'{good} passing rim profiles ({middle} with through wires), {bad} replayed zero-intersection rim paths')
    yes = no = 0
    for width in range(2,5):
        sets = [s for n in range(1,width+1) for s in combinations(range(width),n)]
        for a,b,k in product(sets,sets,range(1,width)):
            answer = strip(dict(width=width,input=a,output=b,gap=k))['detected']
            assert answer==(min(a+b)<k<=max(a+b))
            if answer:
                yes += 1
            else:
                no += 1
    # The access combs can be conjugated by an internal permutation. Check
    # membership also with opposite readings and repeated gate rows.
    for a in [(1,2,0),(2,2,1),(0,1,0)]:
        for b in [(1,0),(2,2),(2,0,1)]:
            for k in [1,2]:
                assert strip(dict(width=3,input=a,output=b,gap=k))['detected']==(min(a+b)<k<=max(a+b))
    print(f'{yes} detected and {no} invisible strip generators by positioned braid evaluation')


def typed(directory):
    ctx = (STAR,arr(STAR,v(0),v(0)))
    f = v(1)
    def hom(a,b):
        return arr(infer(ctx,a),a,b)
    ctx += (hom(f,f),hom(f,f))
    pair = comp2(ctx,0,v(2),v(3))
    ctx += (hom(pair,pair),)
    blank = identity(ctx,identity(ctx,v(0)))
    ctx += (hom(blank,blank),)
    check_ctx(ctx)
    marked_gap = comp2(ctx,0,comp2(ctx,0,v(2),v(5)),v(3))
    # The spatially inserted identity path has a different raw writing.
    # Declare this full-width change at the actual two faces of the gap use.
    ty = infer(ctx,marked_gap)
    ctx += (ty,)
    check_ctx(ctx)
    tm = comp2(ctx,2,v(6),marked_gap)
    if directory:
        out = Emitter()
        out.check_type('twoDisconnectedGates',ctx,v(4),hom(pair,pair))
        out.check_type('probeAtThePaddedInteriorGap',ctx,tm,infer(ctx,tm))
        (directory/'RimAccess.agda').write_text(out.module('RimAccess',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        print(json.dumps(check_rules(data) if 'rules' in data else strip(data),indent=2))
    else:
        audit()
        typed(args.agda_dir)
