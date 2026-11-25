"""Compile a typed planar gate presentation to one loop and three fixed gates.

Use gate-forest JSON fields edges, gates, vertex, path and diagram, with an
optional signed list braid of legal adjacent gate exchanges. The labelled
intermediate table records the source object even for an empty wire packet.
"""
from argparse import ArgumentParser
import json
from pathlib import Path

from semistrict_surface_component_braids import restrict
from semistrict_surface_gate_forests import Presentation, cable
from semistrict_surface_history_group import exchange
from semistrict_surface_scalar_circuits import circuit


PORTS = {'B':('','f'),'D':('f',''),'T':('ff','ff')}


def compile_gate(model,name):
    vertex,src,dst = model.gates[name]
    live = list(src)
    instructions = []
    for offset,take,new,central in circuit(src,dst):
        packets = [''.join(p) for p in new]
        at = model.end(vertex,''.join(live[:offset]))
        ins = live[offset:offset+take]
        before,after = ''.join(ins),''.join(packets)
        if central:
            assert (at,before,after)==(vertex,src,dst)
        else:
            assert before==after
        assert model.end(at,before)==model.end(at,after)
        def typed(port):
            start = at
            result = []
            for word in port:
                result.append((start,word))
                start = model.end(start,word)
            return result
        shape = 'B' if not take else 'D' if not packets else 'T'
        assert PORTS[shape]==('f'*take,'f'*len(packets))
        instructions.append(dict(offset=offset,gate=shape,vertex=at,inputs=typed(ins),
                                 outputs=typed(packets),old_gate=name if central else None))
        live[offset:offset+take] = packets
    assert live==list(dst)
    return instructions


def encode(data):
    model = Presentation(dict(data,rules={}))
    templates = {g:compile_gate(model,g) for g in model.gates}
    def expand(rows):
        return tuple((pos+step['offset'],step['gate']) for pos,g in rows for step in templates[g])
    rows = model.diagram
    drawing = initial = expand(rows)
    folded = Presentation(dict(vertex='x',path='f'*len(data['path']),edges={'f':['x','x']},
                               gates={g:('x',a,b) for g,(a,b) in PORTS.items()},rules={},diagram=drawing))
    signed = []
    marked = {i for i,step in enumerate(step for _,g in rows for step in templates[g])
              if step['old_gate'] is not None}
    for g in data.get('braid',[]):
        dest = exchange(rows,g,model.ports)
        if dest is None:
            raise ValueError('illegal source exchange')
        wide = cable((g,),[len(templates[h]) for _,h in rows])
        for s in wide:
            drawing = exchange(drawing,s,folded.ports)
            assert drawing is not None
        rows = dest
        assert drawing==expand(rows)
        signed.extend(wide)
    assert list(restrict(len(initial),signed,marked))==list(data.get('braid',[]))
    old_end = model.sweep(model.vertex,model.path,rows)
    assert folded.sweep('x',folded.path,drawing)=='f'*len(old_end)
    return dict(templates=templates,input_path=folded.path,diagram=initial,braid=signed,final_diagram=drawing)


def audit():
    from itertools import product
    data = dict(vertex='x',path='',edges={'a':('x','y'),'b':('y','x')},
                gates={'open':('x','','ab'),'close':('x','ab',''),'inner':('y','',''),
                       'outer':('x','',''),'change':('x','ab','abab'),'shrink':('x','abab','ab')},
                diagram=[(0,'open'),(1,'inner'),(0,'close'),(0,'outer')])
    p = Presentation(dict(data,rules={}))
    todo = [(p.diagram,())]
    checked = letters = 0
    while todo:
        diagram,word = todo.pop()
        r = encode(dict(data,braid=word))
        checked += 1
        letters += len(r['braid'])
        if len(word)<3:
            for g in (1,-1,2,-2,3,-3):
                after = exchange(diagram,g,p.ports)
                if after is not None:
                    todo.append((after,(*word,g)))
    # Two empty carriers at different vertices decode to different identities.
    r = encode(dict(data,diagram=[(0,'open'),(0,'change'),(3,'inner'),(0,'shrink'),(0,'close')]))
    assert r['templates']['inner'][0]['outputs']==[('y','')]
    assert r['templates']['outer'][0]['outputs']==[('x','')]
    for n,m in product(range(5),repeat=2):
        inp,out = 'ab'*n,'ab'*m
        encode(dict(data,path=inp,gates={'wide':('x',inp,out)},diagram=[(0,'wide')]))
    print(f'{checked} signed histories, {letters} individual circuit exchanges, 25 multi-object port pairs decoded.')


def typed(directory):
    from functools import reduce
    from catt import STAR,arr,check_ctx,comp2,disc_tree,infer,src,subst_tm,subst_ty,tgt,tree_ctx,v
    from emit_agda import Emitter
    from relative_coherence_exchange_faces import head
    from relative_coherence_hidden_seam import identity
    from semistrict_surface_directed_power_queries import apply
    from semistrict_surface_skeletal_base import right_unit

    def seq(ctx,cut,*terms):
        return reduce(lambda a,b:comp2(ctx,cut,a,b),terms)
    def between(ctx,a,b):
        return arr(infer(ctx,a),a,b)
    graph = (STAR,)*3+(arr(STAR,v(0),v(1)),arr(STAR,v(1),v(2)),arr(STAR,v(0),v(2)))
    a,b,c = map(v,range(3,6))
    ab = comp2(graph,0,a,b)
    blank = identity(graph,v(2))
    old = graph+(between(graph,ab,c),)*2
    old += (between(old,v(6),v(7)),)
    named = graph+(arr(STAR,v(0),v(2)),arr(STAR,v(2),v(2)))
    p,t = v(6),v(7)
    pt,ct = comp2(named,0,p,t),comp2(named,0,c,t)
    named += (between(named,ab,pt),between(named,t,blank),between(named,blank,t),between(named,pt,ct),between(named,pt,ct))

    def program(ctx,p,c,merge,birth,death,update):
        pack = seq(ctx,1,merge,comp2(ctx,0,p,death),right_unit(ctx,p,1,False))
        centre = seq(ctx,1,right_unit(ctx,p,1,True),comp2(ctx,0,p,birth),update,
                     comp2(ctx,0,c,death),right_unit(ctx,c,1,False))
        return seq(ctx,1,pack,centre)
    first,last = (program(named,p,c,v(8),v(10),v(9),v(i)) for i in (11,12))
    named += (between(named,first,last),)

    single = (STAR,arr(STAR,v(0),v(0)))
    f = v(1)
    empty,ff = identity(single,v(0)),comp2(single,0,f,f)
    single += (between(single,empty,f),between(single,f,empty),between(single,ff,ff))
    folded = [v(0)]*3+[f]*5+[v(i) for i in (4,3,2,4,4)]
    single += (subst_ty(named[-1],folded),)
    folded.append(v(5))

    images = [v(i) for i in range(6)]+[ab,blank,right_unit(old,ab,1,True),
              identity(old,blank),identity(old,blank),comp2(old,0,v(6),blank),comp2(old,0,v(7),blank)]
    disk = tree_ctx(disc_tree(2))
    g = v(len(disk)-1)
    u,w = src(disk,g),tgt(disk,g)
    unit = identity(disk,tgt(disk,u))
    inert = identity(disk,unit)
    padded = program(disk,u,w,right_unit(disk,u,1,True),inert,inert,comp2(disk,0,g,unit))
    shrink,expand = head(disk,padded,g),head(disk,g,padded)

    def fit(ctx,cell,forward):
        return apply(ctx,(disk,shrink if forward else expand),[cell])
    def transport(ctx,cell):
        return seq(ctx,2,fit(ctx,src(ctx,cell),True),cell,fit(ctx,tgt(ctx,cell),False))
    images.append(transport(old,v(8)))
    for ctx,relabel in [(single,folded),(old,images)]:
        check_ctx(ctx)
        for i,value in enumerate(relabel):
            assert infer(ctx,value)==subst_ty(named[i],relabel[:i])
    check_ctx(named)
    assert subst_tm(first,images)==apply(old,(disk,padded),[v(6)])
    high = tree_ctx(disc_tree(3))
    j = v(len(high)-1)
    back = seq(high,2,fit(high,src(high,j),False),transport(high,j),fit(high,tgt(high,j),True))
    witness = apply(old,(high,head(high,back,j)),[v(8)])
    if directory:
        emitter = Emitter()
        emitter.check_typed('compoundArrowDiagram',named,first)
        emitter.check_type('foldedHigherUpdate',single,folded[-1],subst_ty(named[-1],folded))
        emitter.check_type('decodedHigherUpdate',old,images[-1],subst_ty(named[-1],images))
        emitter.check_typed('recoverOriginalThreeCell',old,witness)
        (directory/'WireCircuit.agda').write_text(emitter.module('WireCircuit',__doc__.splitlines()[0]))


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
