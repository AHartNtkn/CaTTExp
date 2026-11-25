"""Decide empty-end returns for point-site rules with arbitrary closed planar ports.

Use vertex, edges, gates and rules mapping a name to [object,input,output].
A port is an ordered list of [spatial offset, gate colour]. --dependent requires
each successive pair of uses to share a generated gate occurrence. Needs islpy.
"""
from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache
from itertools import product
import json
from pathlib import Path

from semistrict_surface_component_braids import Components
from semistrict_surface_gate_forests import Presentation
from semistrict_surface_history_group import HistoryGroup
from semistrict_surface_positive_labels import reachable
from semistrict_surface_probe_movies import Faces
from semistrict_surface_scalar_leaves import swapped


class Templates:
    def __init__(self, data):
        self.gates = data['gates']
        self.edges = data['edges']
        self.node = []
        self.ids = {}

    def forest(self, vertex, diagram, mark=None):
        """Intern typed core skeletons with their multisets in each bounded face."""
        diagram = tuple((p,(g,i==mark)) for i,(p,g) in enumerate(diagram))
        ports = {g:tuple(self.gates[g[0]][1:]) for _,g in diagram}
        indexed = tuple((p,i) for i,(p,_) in enumerate(diagram))
        indexed_ports = {i:ports[g] for i,(_,g) in enumerate(diagram)}
        parts = Components(indexed,indexed_ports,0)
        def build(root):
            core = parts.skeleton[root]
            wires, row, locations = [], [], []
            for i,(p,g) in enumerate(diagram):
                before, after = ports[g]
                offset = sum(wires[:p])
                locations.append((len(row),offset))
                if i in core:
                    row.append((offset,g))
                wires[p:p+len(before)] = [i in core]*len(after)
            row = tuple(row)
            base = self.gates[row[0][1][0]][0]
            graph = HistoryGroup(row,ports)
            normal = min(graph.tree_paths)
            order = swapped(range(len(row)),graph.tree_paths[normal])
            faces = Faces(tuple((p,i) for i,(p,_) in enumerate(row)),
                          {i:ports[g] for i,(_,g) in enumerate(row)},0)
            # The port-order corner of a canonically indexed gate names its
            # incident face even when that face has no current children.
            addresses = {}
            types = {}
            word = ''
            for i,(p,g) in enumerate(row):
                before, after = ports[g]
                new_word = word[:p]+after+word[p+len(before):]
                for side, (legs, path) in enumerate(((before,word),(after,new_word))):
                    for j in range(len(legs)+1):
                        region = faces.spots[i+side,p+j]
                        key = (order.index(i),side,j)
                        addresses[region] = min(key,addresses.get(region,key))
                        types[region] = base if p+j==0 else self.edges[path[p+j-1]][1]
                word = new_word
            outer = faces.spots[0,0]
            contents = {r:[] for r in addresses if r!=outer}
            for child, parent in parts.parent.items():
                if parent == root:
                    region = faces.spots[locations[min(parts.skeleton[child])]]
                    contents[region].append(build(child))
            slots = tuple(sorted((addresses[r],types[r],tuple(sorted(kids))) for r,kids in contents.items()))
            node = (base, normal, slots)
            if node not in self.ids:
                self.ids[node] = len(self.node)
                self.node.append(node)
            return self.ids[node]
        roots = tuple(sorted(build(r) for r,p in parts.parent.items() if p is None))
        assert all(self.node[r][0]==vertex for r in roots)
        return roots


def decide(data, dependent=False):
    lib = Templates(data)
    rules, starts, finishes = [], [], []
    single = False
    for x, left, right in data['rules'].values():
        # Recheck the written diagrams before using their forest readings.
        model = Presentation(dict(data,vertex=x,path='',rules={},diagram=left))
        if model.sweep(x,'',left) or model.sweep(x,'',right):
            raise ValueError('expected a closed port')
        a,b = lib.forest(x,left),lib.forest(x,right)
        if not dependent:
            rules.append((x,a,b))
            if x==data['vertex'] and not a:
                starts.append(b)
        else:
            ma = [lib.forest(x,left,i) for i in range(len(left))]
            mb = [lib.forest(x,right,i) for i in range(len(right))]
            rules.extend((x,u,v) for u,v in product(ma,mb))
            if x==data['vertex']:
                if not a:
                    starts.extend(mb)
                    single |= not b
                if not b:
                    finishes.extend(ma)
    if not dependent:
        finishes = [()]
    if single or not starts or not finishes:
        return dict(positive_return=single, templates=len(lib.node), summary_rounds=0)
    summaries = set()
    rounds = 0
    while True:
        def vector(items, places):
            counts = Counter(items)
            return tuple(counts[p] for p in places)
        @lru_cache(None)
        def test(x,left,right):
            if left==right:
                return True
            places = [i for i,item in enumerate(lib.node) if item[0]==x]
            moves = [(a,b) for y,a,b in rules if y==x]
            moves.extend(((i,),(j,)) for i,j in summaries if lib.node[i][0]==x)
            net = dict(source=vector(left,places),target=vector(right,places),
                       transitions=[(vector(a,places),vector(b,places)) for a,b in moves])
            return reachable(net)
        if any(test(data['vertex'],u,v) for u,v in product(starts,finishes)):
            return dict(positive_return=True,templates=len(lib.node),summary_rounds=rounds)
        more = set()
        for i,(x,core,slots) in enumerate(lib.node):
            for j,(y,other,ends) in enumerate(lib.node):
                if i==j or (i,j) in summaries or (x,core)!=(y,other):
                    continue
                assert [(a,t) for a,t,_ in slots]==[(a,t) for a,t,_ in ends]
                if all(test(t,u,v) for (_,t,u),(_,_,v) in zip(slots,ends,strict=True)):
                    more.add((i,j))
        if not more:
            return dict(positive_return=False,templates=len(lib.node),summary_rounds=rounds)
        summaries.update(more)
        rounds += 1


def shell_net(net, depth):
    """Reduce marking reachability to a closed return using a nested wire lens."""
    if depth<1:
        raise ValueError('positive shell depth required')
    places = [f'p{i}' for i in range(len(net['source']))]
    gates = {p:['x','',''] for p in [*places,'control']}
    gates.update(B=['x','','ff'],D=['x','ff',''])
    def port(mark):
        if len(mark)!=len(places) or any(type(x) is not int or x<0 for x in mark):
            raise ValueError('invalid marking')
        return [(0,'control'),*((0,p) for p,n in zip(places,mark) for _ in range(n))]
    def shell(row):
        for _ in range(depth):
            row = [(0,'B')]+[(p+1,g) for p,g in row]+[(0,'D')]
        return row
    rules = dict(open=['x',[],shell(port(net['source']))], close=['x',shell(port(net['target'])),[]])
    for i,(a,b) in enumerate(net['transitions']):
        rules[f't{i}'] = ['x',port(a),port(b)]
    return dict(vertex='x',edges={'f':['x','x']},gates=gates,rules=rules)


def audit():
    for depth in (1,2,3):
        for a,b in [(1,0),(0,1),(1,1)]:
            data=shell_net(dict(source=[a],target=[b],transitions=[([1],[0])]),depth)
            for dependent in (False,True):
                result=decide(data,dependent)
                assert result['positive_return']==(b<=a)
                if a>b and not dependent:
                    assert result['summary_rounds']==depth
    # Reconstruct the corresponding positive programs at their actual ports.
    from semistrict_surface_serial_gate_tracks import read_track
    for depth in (1,2,3):
        data = shell_net(dict(source=[1],target=[0],transitions=[([1],[0])]),depth)
        old = data['rules']['open'][2]
        new = data['rules']['close'][1]
        left,right = data['rules']['t0'][1:]
        gates = dict(data['gates'],site=['x','',''])
        base = [(0,'site')]
        mid = old[:depth]+[(depth,'site')]+old[depth+len(left):]
        charts = [dict(diagram=base,slot=0,input=[],output=old,loop=()),
                  dict(diagram=mid,slot=depth,input=left,output=right,loop=()),
                  dict(diagram=base,slot=0,input=new,output=[],loop=())]
        assert read_track(dict(data,gates=gates,path='',charts=charts,seams=[[],[]]))['sites']==3

    # The bounded face of an x->y->x lens has object y. A rule at x cannot
    # fire there; a change between two differently labelled y-points can.
    typed = dict(vertex='x',edges={'f':['x','y'],'g':['y','x']},
                 gates={'B':['x','','fg'],'D':['x','fg',''],'p':['y','',''],'q':['y','','']},
                 rules={'open':['x',[],[(0,'B'),(1,'p'),(0,'D')]],
                        'close':['x',[(0,'B'),(1,'q'),(0,'D')],[]]})
    assert not decide(typed)['positive_return']
    typed['rules']['inner'] = ['y',[(0,'p')],[(0,'q')]]
    assert decide(typed,True)['positive_return']

    # Two bounded faces of one three-wire core have distinct port addresses.
    # A scalar cannot jump between them even when their objects agree.
    data = shell_net(dict(source=[],target=[],transitions=[]),1)
    data['gates'].update(B=['x','','fff'],D=['x','fff',''])
    data['rules']['close'][1][1] = (2,'control')
    assert not decide(data)['positive_return']
    assert not decide(data,True)['positive_return']
    # Same core and face contents, presented by different legal gate orders.
    data = shell_net(dict(source=[1],target=[1],transitions=[]),1)
    data['rules']['close'][1][1:3] = reversed(data['rules']['close'][1][1:3])
    assert decide(data)['positive_return'] and decide(data,True)['positive_return']
    data = dict(vertex='x',edges={},gates={g:['x','',''] for g in 'ab'},rules={
        'birth':['x',[],[(0,'a'),(0,'b')]], 'da':['x',[(0,'a')],[]], 'db':['x',[(0,'b')],[]]})
    assert decide(data)['positive_return'] and not decide(data,True)['positive_return']
    print('Both return decisions passed 18 nested exact-marking tests, the two-face mismatch, '
          'the reordered port and the split death. Three nested lenses required three summary rounds.')


if __name__=='__main__':
    cli=ArgumentParser(description=__doc__)
    cli.add_argument('input',type=Path,nargs='?')
    cli.add_argument('--dependent',action='store_true')
    cli.add_argument('--shell-net',type=int,metavar='DEPTH')
    args=cli.parse_args()
    if args.input:
        data=json.loads(args.input.read_text())
        print(json.dumps(shell_net(data,args.shell_net) if args.shell_net is not None else decide(data,args.dependent),indent=2))
    else:
        audit()
