"""Decide degree-four surface comparisons with freely invertible unary updates.

Use the history_group JSON format with unary {name:[source_rule,target_rule]}.
The two unit cancellations in both directions are part of this presentation.
Positive integer movie letters are one-based crossings. A unary letter is
[name, zero_based_position, sign], where sign is 1 or -1. commutations
lists pairs of commuting cycle names in the lexicographic spanning forest basis.
"""
from argparse import ArgumentParser
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_braid_reflection import end_vertex
from semistrict_surface_component_braids import Components, Partition
from semistrict_surface_component_order import PairGroup, attainable
from semistrict_surface_history_group import FacePair, HistoryGroup, exchange, placements


class Colours:
    def __init__(self, data):
        rules = data['rules']
        self.marks = {name: (a,b) for name,(_,a,b) in rules.items()}
        self.arrows = data.get('unary', {})
        partition = Partition()
        self.axis = {}
        for name,(a,b) in sorted(self.arrows.items()):
            if rules[a] != rules[b]:
                raise ValueError('unary update requires parallel rule generators')
            if partition.at(a) == partition.at(b):
                self.axis[name] = len(self.axis)
            partition.unite(a,b)
        self.colour = {a:partition.at(a) for a in rules}
        self.cycles = {c:[] for c in self.colour.values()}
        for name,i in self.axis.items():
            self.cycles[self.colour[self.arrows[name][0]]].append(i)
        self.commutations = set()
        for a,b in data.get('commutations', []):
            if a not in self.axis or b not in self.axis or self.colour[self.arrows[a][0]] != self.colour[self.arrows[b][0]]:
                raise ValueError('commutation requires two cycle generators at the same component')
            self.commutations.add(frozenset((self.axis[a],self.axis[b])))

    def shape(self, h):
        return tuple((p,self.colour[a]) for p,a in h)


class DecoratedGroup(PairGroup):
    def __init__(self, n, rank):
        super().__init__(n)
        self.rank = rank
        p, v = self.one
        self.one = p, v+(0,)*(rank*n)

    def act(self, p, v):
        d = len(self.pairs)
        pairs = super().act(p,v[:d])
        out = [0]*(len(p)*self.rank)
        for i,j in enumerate(p):
            a,b = i*self.rank,j*self.rank
            out[b:b+self.rank] = v[d+a:d+a+self.rank]
        return pairs+tuple(out)

    def letter(self, e, i):
        p, v = self.one
        w = list(v)
        w[len(self.pairs)+e*self.rank+i] = 1
        return p, tuple(w)


class Faces:
    def __init__(self, data, entry, colours):
        # Validate the original spatial path and starting diagram at its poles.
        start = FacePair([*entry[:3],[],[]],data['edges'],data['rules'],colours.marks)
        self.root, self.path, self.original = start.root, start.path, start.history
        self.history = colours.shape(start.history)
        self.movies = entry[3:]
        a,b = (self.read(start.history, m, colours, 0) for m in self.movies)
        if a[0] != b[0]:
            raise ValueError('old movies have different positioned end histories')

    @staticmethod
    def read(h, movie, colours, offset):
        moves = []
        for token in movie:
            if isinstance(token,int):
                if token < 1 or (h:=exchange(h,token,colours.marks)) is None:
                    raise ValueError('old crossing not executable')
                moves.append(token+offset)
            else:
                name,i,sign = token
                a,b = colours.arrows[name]
                if sign not in (-1,1) or not 0<=i<len(h):
                    raise ValueError('invalid unary position or sign')
                if sign < 0:
                    a,b = b,a
                if h[i][1] != a:
                    raise ValueError('unary source mismatch')
                h = h[:i]+((h[i][0],b),)+h[i+1:]
                if name in colours.axis:
                    moves.append((offset+i,colours.axis[name],sign))
        return h, moves

    def defect(self, group, colours, offset):
        sides = []
        for m in self.movies:
            _, moves = self.read(self.original,m,colours,offset)
            v = group.one
            for move in moves:
                if isinstance(move,int):
                    factor = group.word((move,))
                else:
                    i,j,sign = move
                    factor = group.letter(i,j)
                    if sign < 0:
                        factor = group.inv(factor)
                v = group.mul(v,factor)
            sides.append(v)
        return group.mul(sides[1],group.inv(sides[0]))


def solve(data):
    if any(len(x)!=1 for x in data['edges']):
        raise ValueError('edge names must be single characters')
    for root,a,b in data['rules'].values():
        if end_vertex(data['edges'],root,a)!=end_vertex(data['edges'],root,b):
            raise ValueError('nonparallel rule')
    cols = Colours(data)
    q = Faces(data,data['query'],cols)
    atoms = [Faces(data,a,cols) for a in data['attachments']]
    chart = HistoryGroup(q.history,cols.marks)
    n = len(q.history)
    group = DecoratedGroup(n,len(cols.axis))
    gs = {group.word(w) for w in chart.braids.values()}
    for e,(_,c) in enumerate(q.history):
        gs.update(group.letter(e,i) for i in cols.cycles[c])
    defects = set()
    for h,path in chart.tree_paths.items():
        t = group.word(path)
        for k,a in placements(h,q.root,q.path,atoms,data['edges'],cols.marks):
            d = a.defect(group,cols,k)
            defects.add(group.mul(group.mul(t,d),group.inv(t)))
    result = attainable(group,gs,defects,q.defect(group,cols,0))
    h = tuple((p,e) for e,(p,_) in enumerate(q.history))
    ports = {e:cols.marks[c] for e,(_,c) in enumerate(q.history)}
    faces = Components(h,ports,len(q.path)).faces
    largest = max(map(len,faces),default=0)
    names = {i:name for name,i in cols.axis.items()}
    missing = sorted({tuple(sorted((names[a],names[b]))) for _,c in q.history
                      for a,b in combinations(cols.cycles[c],2) if frozenset((a,b)) not in cols.commutations})
    exact = largest<=2 and not missing
    return dict(result, exact=exact, surface=result['accepted'] if exact or not result['accepted'] else None,
                largest_sibling_family=largest, noncommuting_pairs=missing)


def checks():
    from random import Random
    from semistrict_surface_component_order import solve as bare
    from semistrict_surface_component_braids import cabling
    from semistrict_surface_framed_pair import face, moves, point, relation
    rng = Random(169)
    def history(n):
        return [(0,'s')]*n
    def old(v):
        k,counts = v
        return [[name,i,1 if value>=0 else -1] for i,vs in enumerate(counts)
                for name,value in zip(('p','q'),vs) for _ in range(abs(value))]+[1]*k
    def entry(n,a,b):
        return ['v','',history(n),old(a),old(b)]
    def value(n):
        return [rng.randrange(3) if n==2 else 0,
                [[rng.randrange(-1,2),rng.randrange(-1,2)] for _ in range(n)]]
    base = dict(edges={},rules={'s':['v','','']},unary={'p':['s','s'],'q':['s','s']},
                commutations=[['p','q']])
    good = bad = 0
    for i in range(120):
        rules = []
        for _ in range(1+i%3):
            n = rng.choice((1,2))
            rules.append([n,value(n),value(n)])
        a,b = value(2),value(2)
        if i%4==0:
            n = 2
            rules.append([n,a,b])
        answer = solve(dict(base,attachments=[entry(*r) for r in rules],query=entry(2,a,b)))
        k, x = face(a,2,2)
        l, y = face(b,2,2)
        expected = not relation(2,moves(2,rules),True).is_disjoint(point([k,l,*[v-u for u,v in zip(x,y)]]))
        assert answer['exact'] and answer['surface']==expected
        good += expected
        bad += not expected
    assert good and bad
    # Two geometrically distinct coloured events become exchangeable through
    # their tree update. Transport a directed cycle at b back to a.
    h = [(0,'a'),(0,'b')]
    data = dict(edges={},rules={x:['v','',''] for x in 'ab'},
                unary={'j':['a','b'],'p':['a','b']},attachments=[],query=['v','',h,[],[['p',0,1],['j',0,-1]]])
    assert solve(data)['surface'] is False
    data['attachments'] = [['v','',[(0,'b')],[],[['j',0,-1],['p',0,1]]]]
    assert solve(data)['surface'] is True
    data['query'][3],data['query'][4] = data['query'][4],data['query'][3]
    assert solve(data)['surface'] is False
    # At a lone occupied colour a missing commutation can be seen by the
    # class threshold even when the abelian quotient accepts the commutator.
    d = dict(base,query=['v','',history(1),[],[['p',0,1],['q',0,1],['p',0,-1],['q',0,-1]]],attachments=[])
    assert solve(d)['surface']
    unresolved = solve(dict(d,commutations=[]))
    assert unresolved['noncommuting_pairs']==[('p','q')] and unresolved['surface'] is None
    # A signed suffix at the whole-bigon exchange reallocates arbitrary
    # labelled decoration between the two disconnected closed components.
    h = [(0,'U'),(1,'s'),(1,'s'),(0,'D')]*2
    outer = list(cabling(((0,0,4),(1,4,8)),(1,)))
    base = dict(edges={'x':['v','v']},rules={'U':['v','','xx'],'D':['v','xx',''],'s':['v','','']})
    atom = ['v','',h,[],outer]
    assert bare(dict(base,attachments=[atom],query=atom))['surface']
    for y,expected in ((-9,True),(-8,False)):
        changes = [['p',0,1]]*9+[['p',4,-1]]*abs(y)
        marked = dict(base,unary={'p':['U','U']},attachments=[atom],query=['v','',h,[],changes+outer])
        answer = solve(marked)
        assert answer['exact'] and answer['surface']==expected
    print(f'{good+bad} mixed two-strand decisions agree with the independent Presburger '
          f'relation ({good} positive, {bad} negative). Relabelling across a spanning-tree '
          'edge, the free-rank obstruction, and both nested whole-component transfers checked.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--presentation',type=Path)
    args = parser.parse_args()
    if args.presentation:
        print(json.dumps(solve(json.loads(args.presentation.read_text()))))
    else:
        checks()
