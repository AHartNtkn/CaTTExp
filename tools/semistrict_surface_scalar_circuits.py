"""Encode a signed scalar movie with birth, death and a single 2-to-2 rule.

Input is serial point-movie JSON. The named edge packets and event images
decode the circuit to the original incidence, port order and signed seams.
"""
from argparse import ArgumentParser
from itertools import chain, product
import json
from pathlib import Path

from semistrict_surface_gate_forests import cable
from semistrict_surface_scalar_leaves import read_edges, sample


def circuit(inputs,outputs):
    """Local instructions: slot, consumed count, ordered decoded output packets, event image."""
    active = [tuple([p]) for p in inputs]
    if not active:
        yield 0,0,[()],False
        active = [()]
    while len(active)>1:
        first = active[0]+active[1]
        yield 0,2,[first,()],False
        yield 1,1,[],False
        active[:2] = [first]
    yield 1,0,[()],False
    yield 0,2,[tuple(outputs),()],True
    yield 1,1,[],False
    for size in range(len(outputs),1,-1):
        yield 1,0,[()],False
        yield 0,2,[tuple(outputs[:size-1]),(outputs[size-1],)],False
    if not outputs:
        yield 0,1,[],False


def encode(data):
    initial,final,_,_,steps = read_edges(data)
    changes,seams,labels,owners = [],[],[],[]
    for i,(below,ins,outs,_) in enumerate(steps):
        for slot,take,packets,central in circuit(ins,outs):
            changes.append((len(below)+slot,take,len(packets)))
            labels.extend(packets)
            owners.append(i if central else None)
            seams.append([])
        if i<len(data['seams']):
            seams[-1] = list(data['seams'][i])
    drawing = sample(['initial'+str(g) for g in initial],changes,seams[:-1])
    packets = [(g,) for g in initial]+labels
    result = dict(movie=drawing,edge_packets=packets,event_images=owners)
    assert decode(result)==(initial,final,steps,[list(w) for w in data['seams']])
    return result


def decode(encoded):
    drawing = encoded['movie']
    labels = encoded['edge_packets']
    initial,final,src,_,steps = read_edges(drawing)
    assert len(labels)==len(src)
    def flat(edges):
        return list(chain.from_iterable(labels[e] for e in edges))
    events = []
    seams = []
    current = []
    for i,((below,ins,outs,above),owner) in enumerate(zip(steps,encoded['event_images'],strict=True)):
        assert (len(ins),len(outs)) in ((0,1),(1,0),(2,2))
        if owner is None:
            assert flat(ins)==flat(outs)
        else:
            assert owner==len(events)
            if events:
                seams.append(current)
            else:
                assert not current
            current = []
            events.append((flat(below),flat(ins),flat(outs),flat(above)))
        if i<len(drawing['seams']):
            current.extend(cable(drawing['seams'][i],[len(labels[e]) for e in below+outs+above]))
    assert not current
    return flat(initial),flat(final),events,seams


def audit():
    # Actual moving external strands, including nontrivial signed exchanges
    # across a source-rule boundary and both empty-port cases.
    checked = 0
    for a,b in product(range(5),repeat=2):
        for sign in (-1,1):
            initial = ['a'+str(i) for i in range(a+2)]
            original = sample(initial,[(1,a,b),(1,b,a)],[[sign*(b+1),-sign] if b else [sign]])
            encode(original)
            checked += 1
    from semistrict_surface_event_holes import plat
    from semistrict_surface_spherical_relations import analyze as spheres
    for word in [(),(2,),(-2,2,-1),(2,2,2)]:
        original,_ = plat(word)
        result = encode(original)
        assert spheres(original)['betti']==spheres(result['movie'])['betti']
    print(f'{checked} signed port round trips and four plats recover every event, segment address and seam.')


def typed(directory):
    from functools import reduce
    from catt import STAR,arr,check_ctx,comp2,disc_tree,infer,src,subst_tm,subst_ty,tgt,tree_ctx,v
    from emit_agda import Emitter
    from relative_coherence_hidden_seam import identity
    from relative_coherence_exchange_faces import head
    from semistrict_surface_skeletal_base import right_unit

    point = (STAR,)
    e = identity(point,identity(point,v(0)))
    scalar = infer(point,e)
    def row(ctx,items):
        return reduce(lambda x,y:comp2(ctx,1,x,y),items) if items else e
    def seq(ctx,*steps):
        return reduce(lambda x,y:comp2(ctx,2,x,y),steps)
    def rule(a,b):
        return arr(scalar,a,b)

    old = point+(scalar,)*5
    oldtype = rule(row(old,[v(1),v(2),v(3)]),row(old,[v(4),v(5)]))
    old += (oldtype,)
    universal = point+(scalar,)
    hh = row(universal,[v(1),v(1)])
    universal += (rule(e,v(1)),rule(v(1),e),rule(hh,hh))

    encoded = encode(sample(['a','b','c'],[(0,3,2)],[]))
    labels = encoded['edge_packets']
    named = point+(scalar,)*len(labels)
    folded = [v(0)]+[v(1)]*len(labels)
    unpacked = [v(0)]+[row(old,[v(g+1) for g in packet]) for packet in labels]
    event = []
    for i,(_,ins,outs,_) in enumerate(read_edges(encoded['movie'])[-1]):
        event.append(v(len(named)))
        named += (rule(row(named,[v(g+1) for g in ins]),row(named,[v(g+1) for g in outs])),)
        if not ins or not outs:
            folded.append(v(2) if not ins else v(3))
            unpacked.append(identity(old,e))
        else:
            folded.append(v(4))
            if encoded['event_images'][i] is not None:
                unpacked.append(comp2(old,1,v(6),e))
            elif not labels[outs[1]]:
                unpacked.append(right_unit(old,unpacked[outs[0]+1],2,True))
            else:
                unpacked.append(right_unit(old,unpacked[ins[0]+1],2,False))
    for ctx,images in [(old,unpacked),(universal,folded)]:
        check_ctx(ctx)
        for i,value in enumerate(images):
            assert infer(ctx,value)==subst_ty(named[i],images[:i])
    check_ctx(named)

    def pack(instr,sink,carrier):
        return seq(named,instr,comp2(named,1,carrier,sink),right_unit(named,carrier,2,False))
    a,b,c = v(1),v(2),v(3)
    first = pack(event[0],event[1],v(4))
    second = pack(event[2],event[3],v(6))
    centre = seq(named,right_unit(named,v(6),2,True),comp2(named,1,v(6),event[4]),
                 event[5],comp2(named,1,v(9),event[6]),right_unit(named,v(9),2,False))
    split = seq(named,right_unit(named,v(9),2,True),comp2(named,1,v(9),event[7]),event[8])
    term = seq(named,comp2(named,1,first,c),second,centre,split)
    typ = rule(row(named,[a,b,c]),row(named,[v(12),v(13)]))
    assert infer(named,term)==typ and subst_ty(typ,unpacked)==oldtype
    emitter = Emitter() if directory else None
    for title,ctx,images in [('oneColourThreeRules',universal,folded),('readOriginalUpdate',old,unpacked)]:
        target = subst_ty(typ,images)
        value = subst_tm(term,images)
        assert infer(ctx,value)==target
        if emitter:
            emitter.check_type(title,ctx,value,target)
    # Check the actual two-way raw 4-fits used to contract decoded collars.
    # In the 2-disc the same fit applies to every pack and unpack block.
    for dim in (2,3):
        disk = tree_ctx(disc_tree(dim))
        top = v(len(disk)-1)
        left,right = (top,top) if dim==2 else (src(disk,top),tgt(disk,top))
        pad = identity(disk,tgt(disk,left))
        collar = lambda p:comp2(disk,1,p,identity(disk,pad))
        body = [right_unit(disk,left,2,True),collar(left)]
        if dim==3:
            body += [comp2(disk,1,top,pad),collar(right)]
        decorated = seq(disk,*body,right_unit(disk,right,2,False))
        plain = identity(disk,top) if dim==2 else top
        for label,s,t in [('shrink',decorated,plain),('insert',plain,decorated)]:
            comparison = head(disk,s,t)
            if emitter:
                emitter.check_type(label+'Collar'+str(dim),disk,comparison,arr(infer(disk,s),s,t))
    if emitter:
        (directory/'ScalarCircuit.agda').write_text(emitter.module('ScalarCircuit',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(encode(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
        typed(args.agda_dir)
