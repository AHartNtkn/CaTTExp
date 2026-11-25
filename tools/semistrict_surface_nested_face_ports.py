"""Check planar scalar-rule endpoint maps in two nested punctured faces."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, subst_tm, subst_ty, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_component_braids import Components, cabling, restrict
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import exchange, inv
from semistrict_surface_shared_edge import braid_image


def audit():
    # Lenses A and B occupy the exterior. In A sit the two lenses C and D.
    # A point in each of these two faces changes into a block of 0,1,2 ports.
    root = ((0,'out'), (0,'A+'), (1,'in'), (1,'C+'), (1,'C-'),
            (1,'D+'), (1,'D-'), (0,'A-'), (0,'B+'), (0,'B-'))
    shape = {name: (('','aa') if name.endswith('+') else
                    ('aa','') if name.endswith('-') else ('','')) for _, name in root}
    outer_ids = ('out','A+','B+')
    inner_ids = ('in','C+','D+')
    faces = Components(root,shape,0)
    assert faces.parent['C+'] == faces.parent['D+'] == 'A+'
    around1, around2 = (1,1), (1,2,2,-1)
    comm = around1+around2+inv(around1)+inv(around2)
    def motion(names):
        packets, = [p for p in faces.packets(root,shape)
                    if tuple(c for c,_,_ in p) == names]
        return cabling(packets,comm)
    outside, inside = motion(outer_ids), motion(inner_ids)
    checks = 0
    for n,m in product(range(3),repeat=2):
        sizes = [n if g=='out' else m if g=='in' else 1 for _,g in root]
        expanded = tuple((pos, g+str(i) if g in ('out','in') else g)
                         for (pos,g),width in zip(root,sizes) for i in range(width))
        labels = [g for _,g in expanded]
        ports = {g:shape.get(g,('','')) for g in labels}
        real = Components(expanded,ports,0)
        for i in range(n):
            assert real.parent['out'+str(i)] is None
        for i in range(m):
            assert real.parent['in'+str(i)] == 'A+'
        two = [cable(w,sizes) for w in (outside,inside)]
        for path in two:
            state = expanded
            for b in path:
                state = exchange(state,b,ports)
                assert state is not None
            assert state == expanded
        # The two paths commute before projection, despite the outer braid
        # carrying the entire inner diagram past the exterior siblings.
        count = len(expanded)
        assert braid_image(count,two[0]+two[1]) == braid_image(count,two[1]+two[0])
        for face,(tag,holes,width) in enumerate([('out','AB',n),('in','CD',m)]):
            for signs in product('+-',repeat=2):
                keep = {labels.index(tag+str(i)) for i in range(width)}
                keep.update(labels.index(h+s) for h,s in zip(holes,signs))
                original = restrict(count,two[face],keep)
                other = restrict(count,two[1-face],keep)
                expected = cable(comm,[width,1,1])
                assert braid_image(width+2,original) == braid_image(width+2,expected)
                assert braid_image(width+2,other) == braid_image(width+2,())
                assert (braid_image(width+2,original) != braid_image(width+2,())) == bool(width)
                checks += 1
    print(f'{checks} endpoint and representative projections; all 9 nested pairs commute')


def typed(directory):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    a,b = v(2),v(3)
    ux,uy = identity(ctx,v(0)),identity(ctx,v(1))
    middle = comp2(ctx,0,comp2(ctx,0,a,uy),b)
    def between(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (between(ux,middle),between(middle,ux),between(uy,uy),between(ux,ux))
    inner, outer = v(6),v(7)
    ctx += (between(identity(ctx,uy),comp2(ctx,1,inner,inner)),
            between(comp2(ctx,1,outer,outer),identity(ctx,ux)))
    check_ctx(ctx)
    nested = comp2(ctx,0,comp2(ctx,0,a,v(8)),b)
    lens = comp2(ctx,1,comp2(ctx,1,v(4),nested),v(5))
    combined = comp2(ctx,1,lens,v(9))
    point = (STAR,)
    u = identity(point,v(0))
    uuu = comp2(point,0,comp2(point,0,u,u),u)
    into,back = head(point,u,uuu),head(point,uuu,u)
    target = point+(arr(infer(point,u),u,u),)*3
    blank = identity(target,u)
    inner2 = comp2(target,1,v(2),v(2))
    outer2 = comp2(target,1,v(3),v(3))
    target += (arr(infer(target,blank),blank,inner2),arr(infer(target,blank),outer2,blank))
    check_ctx(target)
    emitter = Emitter()
    for j,(left,right) in enumerate([(comp2(target,1,v(1),into),back),
                                     (into,comp2(target,1,back,v(1)))]):
        images = [v(0),v(0),u,u,left,right,v(2),v(3),v(4),v(5)]
        for k,A in enumerate(ctx):
            assert infer(target,images[k]) == subst_ty(A,images[:k])
        tm,A = subst_tm(combined,images),subst_ty(infer(ctx,combined),images)
        assert infer(target,tm) == A
        if directory:
            emitter.check_type('flatten'+str(j),target,tm,A)
    if directory:
        emitter.check_type('birthInsideDeathOutside',ctx,combined,infer(ctx,combined))
        (directory/'NestedFacePorts.agda').write_text(emitter.module('NestedFacePorts',__doc__))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    audit()
    typed(args.agda_dir)
