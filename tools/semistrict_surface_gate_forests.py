"""Compare serial histories of rules replacing one planar gate by a diagram.

A JSON query supplies edges (name to two vertices, single-character names),
gates (name to [vertex,input word,output word]), rules (name to [source gate,
positioned output diagram]), vertex, path, diagram, and two lists left/right.
A diagram lists [wire offset,gate name]. A history step is a signed one-based
adjacent exchange, or [zero-based diagram slot,rule name].
"""
import json
from argparse import ArgumentParser
from collections import Counter
from itertools import product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_component_braids import cabling
from semistrict_surface_history_group import exchange
from semistrict_surface_shared_edge import braid_image


def cable(word, sizes):
    packets = []
    pos = 0
    for i, size in enumerate(sizes):
        packets.append((i,pos,pos+size))
        pos += size
    return cabling(packets,word)


class Presentation:
    def __init__(self, data):
        self.edges = data['edges']
        self.gates = data['gates']
        self.ports = {g: (s, t) for g, (_, s, t) in self.gates.items()}
        self.rules = data['rules']
        self.vertex, self.path = data['vertex'], data['path']
        self.diagram = tuple((p,g) for p,g in data['diagram'])
        for x, s, t in self.gates.values():
            if self.end(x, s) != self.end(x, t):
                raise ValueError('gate has incompatible path endpoints')
        self.sweep(self.vertex, self.path, self.diagram)
        for gate, diagram in self.rules.values():
            x, s, t = self.gates[gate]
            if self.sweep(x, s, diagram) != t:
                raise ValueError('rule output has incorrect boundary')

    def end(self, vertex, word):
        for letter in word:
            x, y = self.edges[letter]
            if vertex != x:
                raise ValueError('noncomposable edge word')
            vertex = y
        return vertex

    def sweep(self, vertex, word, diagram):
        self.end(vertex, word)
        for pos, g in diagram:
            x, s, t = self.gates[g]
            if not (0 <= pos <= len(word) and word.startswith(s,pos)
                    and self.end(vertex,word[:pos]) == x):
                raise ValueError('gate outside its typed position')
            word = word[:pos]+t+word[pos+len(s):]
        return word

    def read(self, history):
        diagram = self.diagram
        active = [(i,) for i in range(len(diagram))]
        nodes = {}
        switches = []
        for step in history:
            if type(step) is int:
                if step == 0 or (new := exchange(diagram, step, self.ports)) is None:
                    raise ValueError('illegal signed planar exchange')
                i = abs(step)-1
                switches.append((step,tuple(active)))
                diagram = new
                active[i:i+2] = [active[i+1],active[i]]
            else:
                index, rule = step
                gate, output = self.rules[rule]
                if not 0 <= index < len(active) or diagram[index][1] != gate:
                    raise ValueError('rule does not match this gate')
                parent = active[index]
                pos = diagram[index][0]
                nodes[parent] = rule
                active[index:index+1] = [parent+(j,) for j in range(len(output))]
                diagram = (diagram[:index]+tuple((pos+p,g) for p,g in output)
                           +diagram[index+1:])
        # Expand all trees first. A crossing is now a rectangle on its final
        # descendant packets. A completely consumed packet has width zero.
        widths = Counter(a[:n] for a in active for n in range(1,len(a)+1))
        braid = tuple(b for step,ids in switches
                      for b in cable((step,), [widths[a] for a in ids]))
        def expand(i, pos, g):
            if i not in nodes:
                return [(pos,g)]
            return [leaf for j,(p,h) in enumerate(self.rules[nodes[i]][1])
                    for leaf in expand(i+(j,),pos+p,h)]
        expanded = tuple(cell for j,(p,g) in enumerate(self.diagram)
                         for cell in expand((j,),p,g))
        result = expanded
        for b in braid:
            result = exchange(result,b,self.ports)
            assert result is not None
        assert result == diagram
        return tuple(sorted(nodes.items())), diagram, braid

    def compare(self, left, right):
        f, y, p = self.read(left)
        g, z, q = self.read(right)
        if y != z:
            raise ValueError('histories have different written target diagrams')
        return f == g and braid_image(len(y),p) == braid_image(len(y),q)


def audit():
    data = dict(edges={'a':['x','y'],'b':['y','x']},
                gates={'P':['x','',''],'B':['x','','ab'],'D':['x','ab',''],
                       'U':['x','a','a'],'X':['y','',''],'Y':['y','','']},
                rules={'open':['P',[(0,'B'),(0,'U'),(1,'X'),(0,'D')]],
                       'stop':['U',[]], 'split':['X',[(0,'Y'),(0,'Y')]]},
                vertex='x',path='',diagram=[(0,'P')]*3)
    model = Presentation(data)
    def grow(i, variant):
        steps = [[i,'open']]
        if variant in (1,3):
            steps.append([i+1,'stop'])
        if variant in (2,3):
            steps.append([i+(1 if variant==3 else 2),'split'])
        return steps
    checked = 0
    for word in [(), (1,), (-1,), (1,2,1), (-2,-1,-2), (1,1), (1,2,-1),
                 (1,1,2,2,-1,-1,-2,-2)]:
        order = [0,1,2]
        for b in word:
            i = abs(b)-1
            order[i:i+2] = [order[i+1],order[i]]
        for kinds in product(range(4),repeat=3):
            sizes = [4-(k in (1,3))+(k in (2,3)) for k in kinds]
            after = list(word)
            before = []
            for i in reversed(range(3)):
                before += grow(i,kinds[i])
                after += grow(i,kinds[order[i]])
            before += list(cable(word,sizes))
            assert model.compare(after,before)
            checked += 1
    # The full twist before consuming a gate may disappear, but a winding
    # among two surviving exterior packets and an internal child swap survive.
    erased = Presentation(dict(data, rules={**data['rules'],'erase':['P',[]]}))
    assert erased.compare([1,1,[0,'erase']], [[0,'erase']])
    assert not model.compare([1,1,[0,'open']], [[0,'open']])
    assert not model.compare([[0,'open']], [1,[0,'open']])
    inside = grow(0,2)
    assert not model.compare(inside+[3,3],inside)
    # Pure braid relation after a full three-packet expansion.
    assert model.compare([1,2,1]+grow(2,3),[2,1,2]+grow(2,3))
    print(f'{checked} nested expansion comparisons; root, child, and vanishing windings checked')


def typed(directory):
    x,y = v(0),v(1)
    ctx = (STAR,STAR,arr(STAR,x,y),arr(STAR,y,x))
    a,b = v(2),v(3)
    u = identity(ctx,x)
    ab = comp2(ctx,0,a,b)
    def between(s,t):
        return arr(infer(ctx,s),s,t)
    ctx += (between(u,u),between(u,ab),between(ab,u),between(a,a))
    lens = comp2(ctx,1,comp2(ctx,1,v(5),comp2(ctx,0,v(7),b)),v(6))
    ctx += (between(v(4),lens),between(v(7),identity(ctx,a)))
    check_ctx(ctx)
    shrink = comp2(ctx,1,comp2(ctx,1,v(5),comp2(ctx,0,v(9),b)),v(6))
    two = comp2(ctx,1,comp2(ctx,2,v(8),shrink),v(8))
    ty = infer(ctx,two)
    if directory:
        emitter = Emitter()
        emitter.check_type('twoExpandedLenses',ctx,two,ty)
        (directory/'GateForests.agda').write_text(emitter.module('GateForests',__doc__.splitlines()[0]))


if __name__ == '__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('input',nargs='?',type=Path)
    p.add_argument('--agda-dir',type=Path)
    args = p.parse_args()
    if args.input:
        obj = json.loads(args.input.read_text())
        print('same 3-arrow class:',Presentation(obj).compare(obj['left'],obj['right']))
    else:
        audit()
        typed(args.agda_dir)
