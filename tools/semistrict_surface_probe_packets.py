"""Compute the exterior component of a scalar probe at a closed planar rule.

Gate-forest JSON fields specify a named diagram containing one point 'site',
with relative 'input' and 'output' diagrams at that site. Optional 'loop' is
a signed one-based meridian word, numbered in order: common spectator holes,
input holes, output holes. Within a port order its exterior children by their
earliest gate. The probe approaches these holes along the positive braid comb.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, maximal_vars, sub_from, subst_tm, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, steps, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_component_braids import Components
from semistrict_surface_gate_forests import Presentation, cable
from semistrict_surface_birth_death_packets import follow
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_shared_edge import braid_image


def normal_form(h,m,n,word):
    if any(type(x) is not int or not 1<=abs(x)<=h+m+n for x in word):
        raise ValueError('unknown signed hole index')
    # The product in each port runs from last to first for the positive comb.
    ins = tuple(range(h+m,h,-1))
    outs = tuple(range(h+m+n,h+m,-1))
    primary,other = (ins,outs) if m else (outs,ins)
    if not primary:
        return reduced(word)
    pivot = primary[-1]
    rewrite = inv(primary[:-1])+other
    expanded = []
    for g in word:
        expanded.extend(rewrite if g==pivot else inv(rewrite) if g==-pivot else (g,))
    return reduced(expanded)


def geometry(data):
    site = data['site']
    a,b = data['input'],data['output']
    model = Presentation(dict(data,rules={'in':[site,a],'out':[site,b]}))
    names = [g for _,g in model.diagram]
    if site not in names or model.ports[site]!=('',''):
        raise ValueError('expected a point site in the joint chart')
    for reading in (names,[g for _,g in a],[g for _,g in b]):
        if len(set(reading))!=len(reading):
            raise ValueError('give each gate in a reading its own occurrence name')
    parts = Components(model.diagram,model.ports,len(model.path))
    # Order the actual children for reporting and for interpreting loop letters.
    def order(children,rows,subtrees):
        return sorted(children,key=lambda c:min(i for i,(_,g) in enumerate(rows) if g in subtrees[c]))
    siblings = [c for c in parts.face if c!=site and parts.face[c]==parts.face[site]]
    ins,outs = [],[]
    for rows,dest in ((a,ins),(b,outs)):
        side = Components(rows,model.ports,0)
        dest.extend(order([c for c,v in side.parent.items() if v is None],rows,side.subtree))
    siblings = order(siblings,model.diagram,parts.subtree)
    h,m,n = map(len,(siblings,ins,outs))
    return dict(spectators=siblings,input_holes=ins,output_holes=outs,
                free_rank=h+max(0,m+n-1),sphere_summands=int(m+n==0),
                reduced_loop=normal_form(h,m,n,data.get('loop',[])))


def meridian(j):
    prefix = tuple(range(1,j+1))
    return prefix+(j+1,)*2+inv(prefix)


def audit():
    probe,site = 'probe','site'
    gates = {g:['x','',''] for g in (probe,site)}
    def lens(label,nested):
        start,end = label+'b',label+'d'
        gates.update({start:['x','','aa'],end:['x','aa','']})
        return [(0,start)]+[(1+p,g) for p,g in nested]+[(0,end)]
    def point(label):
        gates[label] = ['x','','']
        return [(0,label)]
    blocks = [lens('P',point('hidden')),point('separate'),lens('outer',lens('inner',[]))]
    stationary = lens('S',point('enclosed'))
    base = dict(edges={'a':['x','x']},gates=gates,vertex='x',path='',site=site)
    packets = [[]]+[sum(blocks[:k],[]) for k in range(1,len(blocks)+1)]
    ports = {g:(s,t) for g,(_,s,t) in gates.items()}
    braids = diagrams = words = 0
    for nested in (False,True):
        around = (lambda rows: lens('frame',rows)) if nested else (lambda rows: rows)
        chart = around([(0,probe),(0,site)]+stationary)
        ports.update({g:(s,t) for g,(_,s,t) in gates.items()})
        for k,rows in enumerate(packets):
            offset = int(nested)
            # Remove the probe from the unmarked baseline used by geometry.
            orig = around([(0,site)]+stationary)
            for l,second in enumerate(packets):
                result = geometry(dict(base,diagram=orig,input=rows,output=second))
                assert len(result['input_holes'])==k and len(result['output_holes'])==l
                assert len(result['spectators'])==1
                assert result['free_rank']==1+max(k+l-1,0)
                assert result['sphere_summands']==int(k+l==0)
                i = tuple(range(1+k,1,-1))
                o = tuple(range(1+k+l,1+k,-1))
                rel = i+inv(o)
                for a,b in product(range(1,2+k+l),repeat=2):
                    u = (a,b,-a)
                    assert normal_form(1,k,l,u+rel+(-b,))==normal_form(1,k,l,u+(-b,))
                    words += 1
                diagrams += 1
            # Execute the whole site meridian with k enclosed subdiagrams, then
            # independently circle the top-level children one at a time.
            joint_word = (offset+1,)*2
            assert follow(tuple(chart),joint_word,ports)==tuple(chart)
            actual = tuple(around([(0,probe)]+rows+stationary))
            whole = cable(joint_word,[len(rows) if g==site else 1 for _,g in chart])
            unit_loop = sum((meridian(j) for j in reversed(range(k))),())
            inside = cable(unit_loop,[1]+[len(z) for z in blocks[:k]])
            individual = tuple((abs(x)+offset)*(1 if x>0 else -1) for x in inside)
            for w in (whole,individual):
                assert follow(actual,w,ports)==actual
            assert braid_image(len(actual),whole)==braid_image(len(actual),individual)
            if k>=2:
                reversed_path = cable(sum((meridian(j) for j in range(k)),()),[1]+[len(z) for z in blocks[:k]])
                wrong = tuple((abs(x)+offset)*(1 if x>0 else -1) for x in reversed_path)
                assert follow(actual,wrong,ports)==actual
                assert braid_image(len(actual),wrong)!=braid_image(len(actual),whole)
            braids += 1
    assert normal_form(0,0,3,(1,2,-1,-2))
    print(f'{diagrams} diagram spans, {braids} positioned peripheral comparisons, {words} based relator checks')


def typed(directory):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    u = identity(ctx,v(0))
    path = comp2(ctx,0,v(2),v(3))
    def between(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (between(u,path),between(path,u),between(u,u))
    target = comp2(ctx,1,comp2(ctx,1,v(4),v(5)),v(6))
    blank = identity(ctx,u)
    ctx += (between(blank,blank),between(blank,target))
    check_ctx(ctx)
    generic = tree_ctx(string_tree(1,[3,3]))
    slots = maximal_vars(generic)
    paths = [composite(generic,2,steps(generic,list(map(v,slots)),order))
             for order in ((0,1),(1,0))]
    labels = sub_from(generic,ctx,dict(zip(slots,(v(7),v(8)))))
    ends = tuple(subst_tm(p,labels) for p in paths)
    track = subst_tm(head(generic,*paths),labels)
    assert infer(ctx,track)==between(*ends)
    if directory:
        out = Emitter()
        out.check_type('probeCrossesClosedBirth',ctx,track,between(*ends))
        (directory/'ProbePackets.agda').write_text(out.module('ProbePackets',__doc__.splitlines()[0]))


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('input',nargs='?',type=Path)
    p.add_argument('--agda-dir',type=Path)
    args = p.parse_args()
    if args.input:
        print(json.dumps(geometry(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
        typed(args.agda_dir)
