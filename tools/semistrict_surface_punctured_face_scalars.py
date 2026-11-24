"""Detect the motion of one floating change in a planar face with several holes."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, subst_tm, subst_ty, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_component_braids import Components, cabling, restrict
from semistrict_surface_history_group import exchange, inv
from semistrict_surface_shared_edge import braid_image


def audit(holes):
    # One temporary scalar marker at the exterior vertex, followed by closed
    # lenses. The inner point of each lens is in its bounded face.
    ports = {'probe':('','')}
    root = [(0,'probe')]
    for j in range(holes):
        for g,pos,rule in [('birth',0,('','ab')),('inner',1,('','')),('death',0,('ab',''))]:
            key = f'{g}{j}'
            ports[key] = rule
            root.append((pos,key))
    root = tuple(root)
    diagram = Components(root,ports,0)
    packets = next(f for f in diagram.packets(root,ports) if len(f)==holes+1)
    probe = next(c for c,l,r in packets if root[l][1]=='probe')
    assert all(diagram.parent[f'inner{j}'] == f'birth{j}' for j in range(holes))
    assert packets[0][0] == probe
    generators = []
    for j in range(holes):
        # Move the probe across the preceding siblings, circle this one, undo.
        walk = tuple(range(1,j+1))
        generators.append(walk+(j+1,j+1)+inv(walk))
    loop = generators[0]
    for g in generators[1:]:
        loop = loop+g+inv(loop)+inv(g)
    lifted = cabling(packets,loop)
    state = root
    for step in lifted:
        state = exchange(state,step,ports)
        assert state is not None
    assert state == root
    # Check that the underlying planar braid with the probe erased is trivial.
    # The action is faithful. Projections to one chosen event per hole may
    # retain its birth or its death, with the same result.
    bare = restrict(len(root),lifted,set(range(1,len(root))))
    assert braid_image(len(root)-1,bare) == braid_image(len(root)-1,())
    expected = braid_image(holes+1,loop)
    assert expected != braid_image(holes+1,())
    for choices in product((0,2),repeat=holes):
        selected = {0} | {1+3*j+c for j,c in enumerate(choices)}
        image = restrict(len(root),lifted,selected)
        assert braid_image(holes+1,image) == expected
        for missing in selected-{0}:
            shortened = restrict(len(root),lifted,selected-{missing})
            assert braid_image(holes,shortened) == braid_image(holes,())
    print(holes,'holes:',len(lifted),'legal switches,',2**holes,
          'choices of representative agree; every proper hole erasure kills the loop')


def typed(directory):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    a,b = v(2),v(3)
    unit = identity(ctx,v(0))
    ab = comp2(ctx,0,a,b)
    birth = arr(infer(ctx,unit),unit,ab)
    death = arr(infer(ctx,unit),ab,unit)
    pole = identity(ctx,unit)
    ctx += (birth,death,birth,death,arr(infer(ctx,pole),pole,pole))
    lens0,lens1 = comp2(ctx,1,v(4),v(5)),comp2(ctx,1,v(6),v(7))
    exterior = comp2(ctx,1,comp2(ctx,1,lens0,lens1),v(8))
    check_ctx(ctx)
    point = (STAR,)
    u = identity(point,v(0))
    uu = comp2(point,0,u,u)
    into = head(point,u,uu)
    back = head(point,uu,u)
    blank = identity(point,u)
    target = point+(arr(infer(point,u),u,u),)*2+(arr(infer(point,blank),blank,blank),)
    check_ctx(target)
    e = Emitter()
    for j,choices in enumerate(product((0,1),repeat=2)):
        images = [v(0),v(0),u,u]
        for k,c in enumerate(choices):
            puncture = v(1+k)
            images.extend((comp2(target,1,puncture,into),back) if c==0
                          else (into,comp2(target,1,back,puncture)))
        images.append(v(3))
        for k,ty in enumerate(ctx):
            assert infer(target,images[k]) == subst_ty(ty,images[:k])
        tm = subst_tm(exterior,images)
        expected = subst_ty(infer(ctx,exterior),images)
        assert infer(target,tm) == expected
        if directory:
            e.check_type('projection'+str(j),target,tm,expected)
    if directory:
        e.check_type('outsideTwoLenses',ctx,exterior,infer(ctx,exterior))
        (directory/'PuncturedFaceScalars.agda').write_text(e.module('PuncturedFaceScalars',__doc__))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    for h in (2,3,4):
        audit(h)
    typed(args.agda_dir)
