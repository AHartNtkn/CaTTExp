"""Compile wired updates with just two pairs outside the connected-port criterion.

Use the same positioned source/target JSON as semistrict_surface_box_ports.
--presentation prints exact gate diagrams and their computed connectivity.
"""
from argparse import ArgumentParser
from collections import Counter
import json
from pathlib import Path

import semistrict_surface_box_ports as box
from semistrict_surface_component_braids import Partition


b,d,m,s,h = box.b,box.d,box.m,box.s,box.h
one,zero = box.one,box.zero
width_two = box.identity(2)
unit_pairs = ['join-left-unit','join-right-unit','fork-left-unit','fork-right-unit']
adapt = [*unit_pairs,'cancel-fork']
rules = {name:ports for name,ports in box.library.items()
         if name not in {*adapt,'leaf-id0','leaf-id1','horizontal','cancel-empty'}}
for name in adapt:
    rules[name+'-to-h'] = box.library[name][0],h
rules.update({'absorb-pair':(box.stack(box.beside(h,h),m),box.stack(m,h)),
              'empty-seed':(zero,box.stack(b,d)),
              'wire-pair':(width_two,box.stack(m,s))})


def atom(name):
    return box.step(name,rules=rules)


def translate(path,macros):
    parts = []
    for move in path.moves:
        if move.name in macros:
            part = macros[move.name]
        elif move.name=='rectangle':
            part = box.step('rectangle',move.grid)
        elif move.name=='update':
            part = box.step('update')
        else:
            part = atom(move.name)
        if move.reverse:
            part = box.reverse(part)
        for axis,l,r in move.frames:
            part = box.frame(axis,l,part,r)
        parts.append(part)
    result = box.chain(*parts) if parts else box.same(path.start)
    assert (result.start,result.end)==(path.start,path.end)
    return result


def build_macros():
    # Park an empty seed on the left of the wire. The second exceptional
    # pair can now reach both the seed wire and the original bare wire.
    enter,leave = box.beside(b,one),box.beside(d,one)
    open_wire = box.chain(
        box.horizontal(atom('empty-seed'),r=one),
        box.step('rectangle',[(b,one),(d,one)]),
        box.vertical(atom('wire-pair'),l=enter,r=leave),
        box.vertical(atom('join-left-unit-to-h'),r=box.stack(s,leave)),
        box.vertical(atom('fork-left-unit-to-h'),l=h),
        atom('vertical'))
    macros = {'leaf-id1':open_wire,
              'leaf-id0':box.chain(atom('empty-seed'),box.vertical(open_wire,l=b,r=d)),
              'horizontal':box.chain(box.vertical(atom('wire-pair'),l=box.beside(h,h)),
                                     box.vertical(atom('absorb-pair'),r=s))}
    for name in adapt:
        macros[name] = box.chain(atom(name+'-to-h'),box.reverse(open_wire))
    side = box.parallel(box.step('leaf-d'),box.step('leaf-b'))
    macros['cancel-empty'] = box.chain(box.reverse(box.step('rectangle',[(d,zero),(zero,b)])),
                                      translate(side,macros),box.reverse(open_wire))
    for name,path in macros.items():
        assert (path.start,box.replay(path,rules))==box.library[name]
    return macros


def graph_counts(cell):
    """Read connectivity from the actual ordered gate incidences and wire legs."""
    parts = Partition()
    boundary = [('in',i) for i in range(cell.source)]
    gates = []
    def run(c,live):
        if c.op=='id':
            return live
        if c.op=='stack':
            for child in c.children:
                live = run(child,live)
            return live
        if c.op=='beside':
            out = []
            at = 0
            for child in c.children:
                out.extend(run(child,live[at:at+child.source]))
                at += child.source
            return out
        site = ('gate',len(gates))
        gates.append(site)
        for wire in live:
            parts.unite(wire,site)
        return [site]*c.target
    ends = run(cell,boundary)
    all_parts = {parts.at(g) for g in boundary+gates+ends}
    leg_parts = {parts.at(g) for g in boundary+ends}
    return dict(gates=len(gates),components=len(all_parts),boundary_components=len(leg_parts))


def report(data,macros,certificate):
    a,z = [box.read_port(data[k]) for k in ('source','target')]
    if (a.source,a.target)!=(z.source,z.target):
        raise ValueError('expected parallel ports')
    proof = box.chain(translate(box.normalize(a),macros),
                      box.vertical(atom('update'),l=box.pack(a.source),r=box.mirror(box.pack(a.target))),
                      box.reverse(translate(box.normalize(z),macros)))
    assert box.replay(proof,rules)==z
    result = dict(moves=dict(Counter(move.name for move in proof.moves)))
    if certificate:
        result['certificate'] = list(map(box.emit,proof.moves))
    return result


def audit():
    macros = build_macros()
    failures = []
    for name,ports in {**rules,'update':(h,h)}.items():
        for i,c in enumerate(ports):
            counts = graph_counts(c)
            if counts['gates']==0 or counts['components']!=1:
                failures.append((name,i))
    assert failures==[('empty-seed',0),('wire-pair',0)]
    for name in box.library:
        for path in [box.step(name),box.reverse(box.step(name))]:
            assert box.replay(translate(path,macros),rules)==path.end
    tested = 0
    for n in range(4):
        for pos in range(n+1):
            for other in range(n+1):
                ports = [dict(width=n,diagram=[(i,'b'),(i,'d')]) for i in [pos,other]]
                assert report(dict(zip(('source','target'),ports)),macros,False)['moves']['update']==1
                tested += 1
    print(f'All 30 port templates replay in the revised library, as do {tested} situated updates.')
    print('Incidence check: exactly the blank faces of empty-seed and wire-pair fail the port condition.')


def typed(directory):
    from catt import comp2,disc_tree,infer,maximal_vars,tree_ctx,v
    from emit_agda import Emitter
    from relative_coherence_exchange_faces import head
    from relative_coherence_hidden_seam import identity
    from semistrict_surface_directed_power_queries import apply
    from semistrict_surface_skeletal_base import right_unit

    ctx,read,inst,_ = box.fixed_context(rules)
    f = v(1)
    def seq(*cells):
        return box.raw_row(ctx,2,cells)
    def stack(*cells):
        return box.raw_row(ctx,1,cells)
    def rebracket(cells,source,target):
        arity = tree_ctx((((),)*len(cells),))
        variables = list(map(v,maximal_vars(arity)))
        def term(tree):
            if type(tree) is int:
                return variables[tree]
            return comp2(arity,1,term(tree[0]),term(tree[1]))
        return apply(ctx,(arity,head(arity,term(source),term(target))),cells)

    line = tree_ctx(disc_tree(1))
    edge = v(2)
    pure = identity(line,v(0))
    padded = comp2(line,0,pure,edge)
    forward,backward = head(line,edge,padded),head(line,padded,edge)
    left,right = (apply(ctx,(line,p),[f]) for p in (forward,backward))
    blank = comp2(line,0,identity(line,pure),identity(line,edge))
    collar = box.raw_row(line,1,[forward,blank,backward])
    start_fit = apply(ctx,(line,head(line,identity(line,edge),collar)),[f])
    seed = stack(left,comp2(ctx,0,inst['empty-seed',False],read(one)),right)

    arity = tree_ctx((((),()),()))
    gb,gd,gf = map(v,maximal_vars(arity))
    unit = identity(arity,gf)
    first = comp2(arity,0,comp2(arity,1,gb,gd),unit)
    second = comp2(arity,1,comp2(arity,0,gb,unit),comp2(arity,0,gd,unit))
    rect = apply(ctx,(arity,head(arity,first,second)),[read(b),read(d),f])
    dist = stack(left,rect,right)
    unpacked = [left,comp2(ctx,0,read(b),read(one)),comp2(ctx,0,read(d),read(one)),right]
    adjust = rebracket(unpacked,((0,(1,2)),3),((0,1),(2,3)))
    enter,leave = read(box.beside(b,one)),read(box.beside(d,one))
    prepare = comp2(ctx,1,right_unit(ctx,enter,2,True),leave)
    connect = stack(enter,inst['wire-pair',False],leave)
    assoc = rebracket([enter,read(m),read(s),leave],((0,(1,2)),3),((0,1),(2,3)))
    collapse = seq(comp2(ctx,1,inst['join-left-unit-to-h',False],stack(read(s),leave)),
                   comp2(ctx,1,read(h),inst['fork-left-unit-to-h',False]),inst['vertical',False])
    result = seq(start_fit,seed,dist,adjust,prepare,connect,assoc,collapse)
    expected = box.raw_hom(ctx,read(one),read(h))
    assert infer(ctx,result)==expected
    if directory:
        emitter = Emitter()
        emitter.check_type('createGateOnBareWire',ctx,result,expected)
        (directory/'TwoExceptionalPorts.agda').write_text(emitter.module('TwoExceptionalPorts',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--presentation',action='store_true')
    parser.add_argument('--certificate',action='store_true')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.presentation:
        print(json.dumps({n:[dict(diagram=box.display(c),**graph_counts(c)) for c in ports]
                          for n,ports in {**rules,'update':(h,h)}.items()},indent=2))
    elif args.input:
        print(json.dumps(report(json.loads(args.input.read_text()),build_macros(),args.certificate),indent=2))
    else:
        audit()
        typed(args.agda_dir)
