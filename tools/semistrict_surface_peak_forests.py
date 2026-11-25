"""Compare planar expansion/contraction histories with no contraction feeding an expansion.

Use the gate-forest JSON input. Each rule still specifies [bare gate, diagram].
A step [slot,rule] expands. A step [slot,wire offset,rule] contracts the written
diagram at that offset, including an empty diagram. Integers are signed switches.
The 'orientations' table assigns each rule 'expand' or 'contract'.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, maximal_vars, sub_from, subst_tm, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, steps, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_gate_forests import Presentation, cable
from semistrict_surface_history_group import exchange
from semistrict_surface_shared_edge import braid_image


def expand_roots(diagram, trees, rules):
    def expand(pos, gate, tree):
        if tree is None:
            return [(pos,gate)]
        rule, children = tree
        bare, output = rules[rule]
        assert gate == bare
        return [row for (p,g),child in zip(output,children,strict=True)
                for row in expand(pos+p,g,child)]
    return tuple(row for (p,g),t in zip(diagram,trees,strict=True) for row in expand(p,g,t))


class Peak(Presentation):
    def __init__(self, data):
        super().__init__(data)
        self.orientation = data['orientations']
        if set(self.rules) != set(self.orientation) or not all(
                o in ('expand','contract') for o in self.orientation.values()):
            raise ValueError('every rule needs a designated orientation')

    def normal_form(self, history):
        diagram = self.diagram
        trees = [None]*len(diagram)
        # Each current root carries its ordered packet at the peak, addressed
        # by the corresponding leaf of the expansion forest on the source.
        packets = [[(i,)] for i in range(len(diagram))]
        fired = {}
        braid = ()
        for step in history:
            if type(step) is int:
                if step == 0 or (new := exchange(diagram,step,self.ports)) is None:
                    raise ValueError('illegal signed switch')
                braid += cable((step,),list(map(len,packets)))
                j = abs(step)-1
                packets[j:j+2] = reversed(packets[j:j+2])
                trees[j:j+2] = reversed(trees[j:j+2])
                diagram = new
                continue
            j, rule = step[0], step[-1]
            bare, block = self.rules[rule]
            if self.orientation[rule] == 'expand':
                if len(step)!=2 or not 0<=j<len(diagram) or diagram[j][1]!=bare:
                    raise ValueError('incorrect expansion site')
                if trees[j] is not None:
                    raise ValueError('a contraction feeds an expansion at this occurrence')
                origin, = packets[j]
                leaves = sorted(a for packet in packets for a in packet)
                braid = cable(braid,[len(block) if a==origin else 1 for a in leaves])
                fired[origin] = rule
                packets[j:j+1] = [[origin+(i,)] for i in range(len(block))]
                trees[j:j+1] = [None]*len(block)
                pos = diagram[j][0]
                rows = tuple((pos+p,g) for p,g in block)
                diagram = diagram[:j]+rows+diagram[j+1:]
            else:
                if len(step)!=3 or not 0<=j<=len(diagram):
                    raise ValueError('incorrect contraction site')
                pos = step[1]
                rows = tuple((pos+p,g) for p,g in block)
                k = j+len(rows)
                if diagram[j:k] != rows:
                    raise ValueError('contraction does not match the given rows')
                # Needed also for nullary blocks or a block with through wires.
                wire = self.sweep(self.vertex,self.path,diagram[:j])
                self.sweep(self.vertex,wire,[(pos,bare)])
                trees[j:k] = [(rule,tuple(trees[j:k]))]
                packets[j:k] = [[a for packet in packets[j:k] for a in packet]]
                diagram = diagram[:j]+((pos,bare),)+diagram[k:]
        def source_tree(address):
            if address in fired:
                rule = fired[address]
                return rule, tuple(source_tree(address+(i,)) for i in range(len(self.rules[rule][1])))
            return None
        source = tuple(source_tree((i,)) for i in range(len(self.diagram)))
        start = expand_roots(self.diagram,source,self.rules)
        end = expand_roots(diagram,trees,self.rules)
        replay = start
        for b in braid:
            replay = exchange(replay,b,self.ports)
            assert replay is not None
        assert replay == end
        return diagram, source, tuple(trees), braid

    def read(self, history):
        diagram, source, target, braid = self.normal_form(history)
        leaves = expand_roots(diagram,target,self.rules)
        return diagram, source, target, braid_image(len(leaves),braid)

    def compare(self, left, right):
        x,y = self.read(left),self.read(right)
        if x[0]!=y[0]:
            raise ValueError('the written target diagrams differ')
        return x==y


def choose_orientations(ends):
    """Find a global designation from the bare source/target colours, or None."""
    if any(a is None and b is None for a,b in ends.values()):
        return None
    pending = [r for r,(a,b) in ends.items() if a is None]
    reached = set(pending)
    starts = {}
    for r,(a,b) in ends.items():
        starts.setdefault(a,[]).append(r)
    while pending:
        _, bare_target = ends[pending.pop()]
        if bare_target is None:
            return None
        for r in starts.get(bare_target,[]):
            if r not in reached:
                reached.add(r)
                pending.append(r)
    return {r: 'contract' if r in reached else 'expand' for r in ends}


def audit_orientations():
    choices = [(a,b) for a,b in product((None,'x','y'),repeat=2)
               if a is not None or b is not None]
    for rows in product(choices,repeat=3):
        ends = dict(enumerate(rows))
        def valid(os):
            if any(row[o] is None for row,o in zip(rows,os)):
                return False
            return not ({b for (a,b),o in zip(rows,os) if o==1} &
                        {a for (a,b),o in zip(rows,os) if o==0})
        answer = choose_orientations(ends)
        assert (answer is not None)==any(valid(o) for o in product((0,1),repeat=3))
        if answer is not None:
            assert valid([int(answer[r]=='contract') for r in ends])
    print(f'{len(choices)**3} colour presentations agree with exhaustive orientation search')


def audit():
    # C closes a two-wire lens with a scalar inside, E opens a new lens.
    lens = [(0,'B'),(1,'X'),(0,'D')]
    gate = {'B':['x','','aa'],'D':['x','aa',''],'X':['x','',''],
            'P':['x','',''],'Q':['x','','']}
    data = dict(edges={'a':['x','x']},gates=gate,vertex='x',path='',
                diagram=lens+[(0,'P')],rules={'C':['Q',lens],'E':['P',lens]},
                orientations={'C':'contract','E':'expand'})
    count = 0
    for c,e in product([[],[(0,'X')],lens],[[],[(0,'X')],lens]):
        model = Peak(dict(data, diagram=c+[(0,'P')],rules={'C':['Q',c],'E':['P',e]}))
        for sign in (1,-1):
            for length in range(7):
                word = (sign,)*length
                # In the mixed order two bare middle strands can braid by
                # either sign. In sorted order both strands are packets.
                close = [0,0,'C']
                open_after = [int(length%2==0),'E']
                mixed = [close,*word,open_after]
                pos = 0 if length%2==0 else len(e)
                sorted_steps = [[len(c),'E'],*cable(word,[len(c),len(e)]),[pos,0,'C']]
                assert model.compare(mixed,sorted_steps)
                count += 1
    model = Peak(data)
    assert not model.compare([[0,0,'C'],[1,'E']],[[0,0,'C'],1,1,[1,'E']])
    # Even a zero-leaf output tree records which contraction produced its root.
    empty = Peak(dict(data,diagram=[],rules={'C':['Q',[]],'D':['Q',[]]},
                      orientations={'C':'contract','D':'contract'}))
    assert not empty.compare([[0,0,'C']],[[0,0,'D']])
    seam = Peak(dict(data,diagram=lens,rules={'C':['P',lens],'E':['P',lens]}))
    try:
        seam.read([[0,0,'C'],[0,'E']])
    except ValueError as error:
        assert 'feeds an expansion' in str(error)
    else:
        raise AssertionError('accepted a shared middle gate')
    print(f'{count} mixed and sorted histories agree; surviving twist and shared-gate controls checked')


def audit_sorting(e,c):
    # All interleavings of two fixed sequences of batches. X joins the next
    # two batches. Verify each elementary collapse has exactly one cofacet.
    def paths(i,j):
        if not (i or j):
            yield ''
        for marker,a,b in [('E',1,0),('C',0,1),('X',1,1)]:
            if a<=i and b<=j:
                for rest in paths(i-a,j-b):
                    yield marker+rest
    cells = set(paths(e,c))
    initial = len(cells)
    cofaces = {u:set() for u in cells}
    for u in cells:
        for j,ch in enumerate(u):
            if ch=='X':
                for corner in ('CE','EC'):
                    cofaces[u[:j]+corner+u[j+1:]].add(u)
    def inversions(u):
        return sum(u[i+1:].count('E') for i,ch in enumerate(u) if ch=='C')
    for w in sorted((u for u in cells if 'X' not in u),key=inversions,reverse=True):
        pos = w.find('CE')
        if pos<0:
            continue
        near = [u for u in cells if u.replace('X','CE')==w]
        for u in sorted(near,key=lambda t:t.count('X'),reverse=True):
            i = 0
            for j,ch in enumerate(u):
                if i>=pos:
                    break
                i += 2 if ch=='X' else 1
            if u[j]=='X':
                continue
            assert i==pos and u[j:j+2]=='CE'
            mate = u[:j]+'X'+u[j+2:]
            assert cofaces[u] & cells == {mate}
            cells.difference_update((u,mate))
    assert cells=={'E'*e+'C'*c}
    return (initial-1)//2


def typed(directory):
    ctx = (STAR,STAR,arr(STAR,v(0),v(1)),arr(STAR,v(1),v(0)))
    u = identity(ctx,v(0))
    ab = comp2(ctx,0,v(2),v(3))
    def between(a,b):
        return arr(infer(ctx,a),a,b)
    ctx += (between(u,ab),between(ab,u),between(u,u),between(u,u))
    lens = comp2(ctx,1,v(4),v(5))
    ctx += (between(lens,v(6)),between(v(7),lens))
    check_ctx(ctx)
    def compose(first,second):
        return comp2(ctx,2,first,second)
    c,e = v(8),v(9)
    mixed = compose(comp2(ctx,1,c,v(7)),comp2(ctx,1,v(6),e))
    sorted_tm = compose(comp2(ctx,1,lens,e),comp2(ctx,1,c,lens))
    assert infer(ctx,mixed)==infer(ctx,sorted_tm)
    P = tree_ctx(string_tree(1,[3,3]))
    slots = maximal_vars(P)
    rows = list(map(v,slots))
    paths = [composite(P,2,steps(P,rows,order)) for order in ((0,1),(1,0))]
    labels = sub_from(P,ctx,dict(zip(slots,(c,e))))
    switch = subst_tm(head(P,*paths),labels)
    assert infer(ctx,switch)==between(mixed,sorted_tm)
    if directory:
        out = Emitter()
        out.check_type('sortTwoChanges',ctx,switch,between(mixed,sorted_tm))
        for name,t in [('contractFirst',mixed),('expandFirst',sorted_tm)]:
            out.check_type(name,ctx,t,infer(ctx,mixed))
        (directory/'PeakForests.agda').write_text(out.module('PeakForests',__doc__.splitlines()[0]))


if __name__=='__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path,nargs='?')
    p.add_argument('--agda-dir',type=Path)
    args = p.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        print('same 3-arrow class:',Peak(data).compare(data['left'],data['right']))
    else:
        audit()
        audit_orientations()
        count = sum(audit_sorting(e,c) for e,c in product(range(5),repeat=2))
        print(f'{count} verified free-face collapses on 25 interleaving grids')
        typed(args.agda_dir)
