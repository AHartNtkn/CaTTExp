"""Decide common lifted corners of nonempty closed planar rule ports.

JSON: gate-forest graph fields and a jointly collapsed 'diagram'; 'blocks'
maps each selected point marker to its nonempty, positioned closed diagram.
'paths' gives one positioned named return braid at the expanded cut for each
marker. Return a common coset representative or an incompatible pair.
"""
from argparse import ArgumentParser
from functools import lru_cache
from itertools import combinations, permutations, product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_birth_death_packets import expand, expand_path, follow
from semistrict_surface_component_braids import Components, cabling, restrict
from semistrict_surface_gate_forests import Presentation, cable
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_shared_edge import braid_image


class Corner:
    def __init__(self,data):
        self.blocks = data['blocks']
        self.model = Presentation(dict(data,rules={k:[k,b] for k,b in self.blocks.items()}))
        self.joint = self.model.diagram
        labels = [g for _,g in self.joint]
        if len(labels)!=len(set(labels)) or not set(self.blocks)<=set(labels):
            raise ValueError('expected distinct named rows including every marker')
        self.rows = expand(self.joint,self.blocks)
        names = [g for _,g in self.rows]
        if len(set(names))!=len(names) or set(names)&set(self.blocks):
            raise ValueError('give expanded gates distinct occurrence names apart from markers')
        self.sizes = {}
        for k,b in self.blocks.items():
            if not b or self.model.ports[k]!=('',''):
                raise ValueError('expected a point site with a nonempty closed port')
            sizes = [1]*len(names)
            pos = names.index(b[0][1])
            sizes[pos:pos+len(b)] = [len(b)]+[0]*(len(b)-1)
            self.sizes[k] = sizes
        self.image = lru_cache(maxsize=256)(lambda w:braid_image(len(self.rows),w))

    def project(self,k,word):
        return reduced(cable(word,self.sizes[k]))

    def contains(self,k,rep,candidate):
        delta = reduced(inv(rep)+candidate)
        return self.image(delta)==self.image(self.project(k,delta))

    def meet(self,paths):
        x = ()
        earlier = []
        for k,rep in paths.items():
            y = reduced(inv(x)+rep)
            for j in earlier:
                y = self.project(j,y)
            x = reduced(x+y)
            if not self.contains(k,rep,x):
                return None
            earlier.append(k)
        return x


def solve(data):
    corner = Corner(data)
    paths = {k:tuple(w) for k,w in data['paths'].items()}
    if set(paths)!=set(corner.blocks):
        raise ValueError('supply a corner path for each selected site')
    for w in paths.values():
        if follow(corner.rows,w,corner.model.ports)!=corner.rows:
            raise ValueError('expected a positioned loop returning each gate by name')
    x = corner.meet(paths)
    if x is not None:
        assert all(corner.contains(k,w,x) for k,w in paths.items())
        return dict(common_braid=x)
    for a,b in combinations(paths,2):
        if corner.meet({a:paths[a],b:paths[b]}) is None:
            return dict(incompatible_pair=[a,b])
    raise AssertionError('pairwise compatible directions have no joint lift')


def example():
    # Two exterior rules and a third in a spectator lens at a different
    # object. A replaced child itself has two independent inner points.
    joint = [(0,'A'),(0,'D'),(0,'S+'),(1,'C'),(1,'v'),(0,'S-')]
    blocks = dict(A=[(0,'L+'),(1,'m'),(1,'n'),(0,'L-'),(0,'z')],
                  D=[(0,'p'),(0,'q')],C=[(0,'t'),(0,'u')])
    gates = {g:['x','',''] for g in ('A','D','p','q','z')}
    gates.update({g:['y','',''] for g in ('C','m','n','t','u','v')})
    for g in ('S','L'):
        gates[g+'+'] = ['x','','ab']
        gates[g+'-'] = ['x','ab','']
    return dict(edges={'a':['x','y'],'b':['y','x']},gates=gates,vertex='x',path='',
                diagram=joint,blocks=blocks)


def audit():
    data = example()
    c = Corner(data)
    ports = c.model.ports
    groups = Components(c.rows,ports,0)
    packets = groups.packets(c.rows,ports)
    def motion(children,word):
        fibre, = [f for f in packets if tuple(b for b,_,_ in f)==children]
        return cabling(fibre,word)
    # Generators on both sides of cluster boundaries and inside an enclosed
    # component of the port. Alternating group commutators matter here.
    exterior = ('L+','z','p','q','S+')
    cross = motion(exterior,(2,2))
    turns = motion(('m','n'),(1,1))
    inside = motion(('t','u','v'),(2,2))
    side = motion(exterior,(3,3))
    outer = motion(exterior,(1,1))
    comm = reduced(cross+side+inv(cross)+inv(side))
    words = [(),cross,inv(cross),turns,inside,side,outer,comm]
    for w in words:
        assert follow(c.rows,w,ports)==c.rows
    # Compare the joint projection against actual simultaneous marker
    # collapse and re-expansion, on every subset and every test motion.
    projections = 0
    for count in range(4):
        for subset in combinations(c.blocks,count):
            blocks = {k:c.blocks[k] for k in subset}
            collapsed = expand(c.joint,{k:b for k,b in c.blocks.items() if k not in subset})
            omitted = {g for k in subset for _,g in c.blocks[k][1:]}
            keep = {i for i,(_,g) in enumerate(c.rows) if g not in omitted}
            for w in words:
                short = restrict(len(c.rows),w,keep)
                assert follow(collapsed,short,ports)==collapsed
                actual = expand_path(collapsed,short,blocks)
                assert follow(c.rows,actual,ports)==c.rows
                for order in permutations(subset):
                    now = w
                    for k in order:
                        now = c.project(k,now)
                    assert c.image(now)==c.image(actual)
                    projections += 1
    assert c.project('A',turns)==() and c.image(turns)!=c.image(())
    assert c.project('D',turns)==turns
    good = bad = 0
    for reps in product(((),cross,comm),((),cross,side),((),inside,turns)):
        paths = dict(zip(c.blocks,reps))
        x = c.meet(paths)
        pairs = [c.meet({k:paths[k] for k in keys}) for keys in combinations(paths,2)]
        assert (x is not None)==all(w is not None for w in pairs)
        if x is None:
            bad += 1
        else:
            good += 1
            assert all(c.contains(k,w,x) for k,w in paths.items())
        for keys in permutations(paths):
            alternate = c.meet({k:paths[k] for k in keys})
            assert (alternate is None)==(x is None)
            if alternate is not None:
                assert all(c.contains(k,w,alternate) for k,w in paths.items())
    assert good and bad
    # This obstruction has no pairwise linking numbers anywhere in the
    # expanded drawing. Its incompatibility is a nonabelian coset test.
    assert all(sum(1 if g>0 else -1 for g in restrict(len(c.rows),comm,set(pair)))==0
               for pair in combinations(range(len(c.rows)),2))
    assert c.meet({'A':(), 'D':comm}) is None
    print(f'{projections} positioned collapse/re-expansion comparisons; '
          f'{good} compatible and {bad} incompatible triples in all six orders')
    print('zero-linking commutator obstructs a joint lift of the two exterior ports')


def typed(directory):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    a,b = v(2),v(3)
    ux,uy = identity(ctx,v(0)),identity(ctx,v(1))
    mid = comp2(ctx,0,comp2(ctx,0,a,uy),b)
    def between(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (between(ux,mid),between(mid,ux),between(uy,uy),between(ux,ux))
    inner,outer = v(6),v(7)
    def close(at):
        placed = comp2(ctx,0,comp2(ctx,0,a,at),b)
        return comp2(ctx,1,comp2(ctx,1,v(4),placed),v(5))
    left = comp2(ctx,1,close(comp2(ctx,1,inner,inner)),outer)
    right = comp2(ctx,1,outer,outer)
    ctx += (between(left,right),between(comp2(ctx,1,inner,inner),inner))
    check_ctx(ctx)
    joint = comp2(ctx,1,v(8),close(v(9)))
    if directory:
        out = Emitter()
        out.check_type('closedPortBesideInteriorChange',ctx,joint,infer(ctx,joint))
        (directory/'ClosedPortLinks.agda').write_text(out.module('ClosedPortLinks',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(solve(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
        typed(args.agda_dir)
