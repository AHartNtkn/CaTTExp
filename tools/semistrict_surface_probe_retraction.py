"""Project flattened probe braids back to the free group of a planar face.

Use gate-forest JSON fields edges, gates, vertex, path and diagram. The probe
field names an isolated point. A loop is a signed planar braid with all gates
returning by name; after forgetting the probe the braid must be trivial.
Set flat to true for a loop of the flattened diagram. representatives may map
a child or enclosing component (its least gate name) to a chosen core gate.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, subst_tm, subst_ty, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_birth_death_packets import expand, expand_path, follow
from semistrict_surface_chain_probe import evaluate, peripheral
from semistrict_surface_component_braids import Components, restrict
from semistrict_surface_gate_forests import Presentation, cable
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_serial_gate_tracks import push
from semistrict_surface_shared_edge import braid_image


def probe_word(size,word):
    # With the probe first, its Artin image is C x_0 C^-1. Forget x_0
    # in C and reverse the order for the positive access comb.
    image = braid_image(size,word)[0]
    mid = len(image)//2
    if image[mid]!=1 or image[mid+1:]!=inv(image[:mid]):
        raise ValueError('the probe did not return')
    spelling = tuple((abs(a)-1)*(1 if a>0 else -1) for a in reversed(image[:mid]) if abs(a)!=1)
    result = reduced(spelling)
    if braid_image(size,push(result))!=braid_image(size,word):
        raise ValueError('the braid has residual spectator motion')
    return result


def project(data):
    model = Presentation(dict(data,rules={}))
    probe = data['probe']
    rows = model.diagram
    names = [g for _,g in rows]
    if len(set(names))!=len(names) or probe not in names or model.ports[probe]!=('',''):
        raise ValueError('expected distinct gate occurrences and a point probe')
    word = tuple(data['loop'])
    if any(type(g) is not int or not 0<abs(g)<len(rows) for g in word):
        raise ValueError('invalid signed braid generator')
    if not data.get('flat') and follow(rows,word,model.ports)!=rows:
        raise ValueError('positioned path misses its endpoint')
    at = names.index(probe)
    order = list(range(len(rows)))
    for g in word:
        i = abs(g)-1
        order[i:i+2] = reversed(order[i:i+2])
    if order!=list(range(len(rows))):
        raise ValueError('expected a named loop')
    bare = restrict(len(rows),word,set(range(len(rows)))-{at})
    if braid_image(len(rows)-1,bare)!=braid_image(len(rows)-1,()):
        raise ValueError('the unmarked diagram has nontrivial motion')

    parts = Components(rows,model.ports,len(model.path))
    frame = [c for c,f in parts.face.items() if f==parts.face[probe] and c!=probe]
    parent = parts.parent[probe]
    choices = data.get('representatives',{})
    def rep(c):
        g = choices.get(c,c)
        if g not in parts.skeleton[c]:
            raise ValueError('representative must lie on the connected component itself')
        return g
    children = sorted(map(rep,frame),key=names.index)
    shell = None if parent is None else rep(parent)
    all_gates = sorted(children+([] if shell is None else [shell]),key=names.index)
    indices = {names.index(g) for g in all_gates}|{at}
    keep = restrict(len(rows),word,indices)
    initial = tuple(range(1,1+sum(i<at for i in indices)))
    flat = probe_word(len(indices),initial+keep+inv(initial))
    values = {g:(i+1,) for i,g in enumerate(children)}
    if shell is not None:
        # In the compactified plane the total peripheral product is null.
        i = all_gates.index(shell)
        left = peripheral([values[g] for g in all_gates[i+1:]])
        right = peripheral([values[g] for g in all_gates[:i]])
        values[shell] = inv(left)+inv(right)
    answer = reduced(tuple(b for a in flat for b in (values[all_gates[a-1]]
                          if a>0 else inv(values[all_gates[-a-1]]))))
    return dict(children=children,shell=shell,word=answer)


def audit():
    sites = ('probe','H','u','v','w','outside')
    gates = {g:['x','',''] for g in sites}
    gates.update({g:['x','','aa'] for g in ('B','J')})
    gates.update({g:['x','aa',''] for g in ('D','K')})
    base = dict(edges={'a':['x','x']},gates=gates,path='',vertex='x',probe='probe')
    joint = ((0,'B'),(1,'probe'),(1,'u'),(1,'H'),(0,'D'),(0,'outside'))
    # A change in the enclosed face replaces v by a lens and a separate point.
    blocks = [((0,'v'),),((0,'J'),(0,'K'),(0,'w'))]
    counts = caps = 0
    for length in range(4):
        for word in product((1,-1,2,-2),repeat=length):
            if reduced(word)!=word:
                continue
            local = push(word)
            loop = tuple((abs(g)+1)*(1 if g>0 else -1) for g in local)
            assert project(dict(base,diagram=joint,loop=loop))['word']==word
            for block in blocks:
                packet = {'H':block}
                rows = expand(joint,packet)
                wide = expand_path(joint,loop,packet)
                for shell in ('B','D'):
                    for child in (('J','K') if len(block)>1 else ('v',)):
                        reps = {'B':shell, 'J' if len(block)>1 else 'v':child}
                        result = project(dict(base,diagram=rows,loop=wide,representatives=reps))
                        piece = (3,2) if len(block)>1 else (2,)
                        expected = reduced(tuple(b for g in word for b in
                                      ((g,) if abs(g)==1 else piece if g>0 else inv(piece))))
                        assert result['word']==expected
                        counts += 1
    for block in blocks:
        rows = expand(joint,{'H':block})
        size = len(rows)-2  # all gates of the enclosing packet (apart from probe and outside)
        route = (1,)       # move probe from the initial flat comb to its reference slot
        whole = inv(route)+cable((1,1),[1,size,1])+route
        for shell in ('B','D'):
            for rep in (('J','K') if len(block)>1 else ('v',)):
                reps = {'B':shell,'J' if len(block)>1 else 'v':rep}
                data = dict(base,diagram=rows,loop=whole,flat=True,representatives=reps)
                assert not project(data)['word']
                # The ordinary plane forgetting just the shell would send the
                # exact same loop to a nonempty total child meridian.
                indices = {i for i,(_,g) in enumerate(rows) if g in {'probe','u','w',rep}}
                plain = restrict(len(rows),whole,indices)
                assert probe_word(len(indices),plain)==tuple(range(len(indices)-1,0,-1))
                caps += 1
    # Sweep the entire flattened open/change/close chain. Recover the rank-three
    # group of the enclosed position component by mapping the flattened free
    # generators to meridians at the two cuts where those generators arise.
    bare = tuple((0,g) for _,g in joint if g!='probe')
    inside = [(0,'J'),(0,'K'),(0,'w')]
    outer = ((0,'H'),(0,'outside'))
    def ch(rows,slot,l,r):
        return dict(diagram=rows,slot=slot,input=l,output=r)
    opened = tuple((0,g) for g in ('B','u','v','D'))
    closed = tuple((0,g) for g in ('B','u','J','K','w','D'))
    data = dict(base,gates={g:['x','',''] for g in gates},seams=[(),()],
                charts=[ch(outer,0,(),opened),ch(bare,2,[(0,'v')],inside),ch(outer,0,closed,())])
    computed = evaluate(data)
    def apply(values,word):
        return reduced(tuple(b for a in word for b in (values[a-1] if a>0 else inv(values[-a-1]))))
    # First born meridians u,v and the enclosing death gate; then K,w at the split.
    # In the enclosed group choose a=u, b=v, c=w. The J meridian is c^-1 b.
    values = [(),(1,),(2,),(),(),(3,)]
    assert computed['generators']==len(values) and not apply(values,computed['attaching_word'])
    assert [apply(values,x) for x in computed['final_meridians']]==[()]
    rows = expand(joint,{'H':blocks[-1]})
    sub = expand_path(joint,(2,2),{'H':blocks[-1]})
    outside = cable((1,1),[len(rows)-1,1])
    for shell in ('B','D'):
        test = dict(base,diagram=rows,representatives={'B':shell})
        assert project(dict(test,loop=outside+sub+inv(outside)))['word']==project(dict(test,loop=sub))['word']
    print(f'{counts} positioned lifts through the interior rule, {caps} boundary loops killed by the enclosing puncture relation')
    print('closed six-generator flat presentation maps to the three interior meridians; both enclosing-gate choices survive exterior transport')


def typed(directory):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    a,b = v(2),v(3)
    u = identity(ctx,v(0))
    path = comp2(ctx,0,comp2(ctx,0,a,identity(ctx,v(1))),b)
    def hom(context,s,t):
        return arr(infer(context,s),s,t)
    ctx += (hom(ctx,u,path),hom(ctx,path,u))
    inner = identity(ctx,v(1))
    ctx += (hom(ctx,inner,inner),)
    probe_base = identity(ctx,inner)
    ctx += (hom(ctx,probe_base,probe_base),)
    # Whisker the probe on its actual interior object and close the lens.
    inside = comp2(ctx,0,comp2(ctx,0,a,comp2(ctx,1,v(6),v(7))),b)
    term = comp2(ctx,1,comp2(ctx,1,v(4),inside),v(5))
    check_ctx(ctx)
    target = (STAR,)
    one = identity(target,v(0))
    padded = comp2(target,0,comp2(target,0,one,one),one)
    flat = hom(target,one,one)
    target += (flat,flat,flat)
    pole = identity(target,one)
    target += (hom(target,pole,pole),)
    check_ctx(target)
    images = [v(0),v(0),one,one,comp2(target,1,v(1),head((STAR,),one,padded)),
              comp2(target,1,head((STAR,),padded,one),v(2)),v(3),v(4)]
    for j,ty in enumerate(ctx):
        assert infer(target,images[j])==subst_ty(ty,images[:j])
    result = subst_tm(term,images)
    wanted = subst_ty(infer(ctx,term),images)
    assert infer(target,result)==wanted
    if directory:
        out = Emitter()
        out.check_type('enclosedProbe',ctx,term,infer(ctx,term))
        out.check_type('allGateFlattening',target,result,wanted)
        (directory/'ProbeRetraction.agda').write_text(out.module('ProbeRetraction',__doc__.splitlines()[0]))


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path,nargs='?')
    p.add_argument('--agda-dir',type=Path)
    args = p.parse_args()
    if args.input:
        print(json.dumps(project(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
        typed(args.agda_dir)
