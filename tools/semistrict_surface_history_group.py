"""Compile an old degree-four Gray query into a finitely presented group order.

JSON: edges maps names to endpoint pairs; rules maps names to [vertex,input,
output] as in semistrict_surface_braid_reflection. query and attachments use
[vertex, initial_edge_word, history, left_crossings, right_crossings].
Edge names are single characters. The abelian decision is returned only when
the program certifies commutation of every pair of surviving generators.
"""
import argparse
import json
from collections import Counter, defaultdict, deque
from itertools import combinations, product
from pathlib import Path

from semistrict_surface_braid_reflection import end_vertex, follow
from semistrict_surface_return_gaps import exchange_at
from semistrict_surface_one_step_reflection import reverse_signed
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_single_power import coprime_parts
from semistrict_surface_scalar_sites import coefficients


def inv(w):
    return tuple(-x for x in reversed(w))


def reduced(w):
    result = []
    for x in w:
        if result and result[-1] == -x:
            result.pop()
        else:
            result.append(x)
    return tuple(result)


def cyclic(w):
    w = reduced(w)
    while len(w) > 1 and w[0] == -w[-1]:
        w = w[1:-1]
    if not w:
        return ()
    return min(s[i:]+s[:i] for s in (w, inv(w)) for i in range(len(w)))


def exchange(h, letter, marks):
    i = abs(letter)-1
    if not 0 <= i < len(h)-1:
        return None
    if letter > 0:
        return exchange_at(h, i, marks)
    (a, left), (b, right) = h[i:i+2]
    l, r = marks[left]
    if a+len(r) > b:
        return None
    prev = h[:i]+((b+len(l)-len(r),right),(a,left))+h[i+2:]
    assert exchange_at(prev,i,marks) == h
    return prev


def realize(start, end, word, marks):
    """Return a legal representative of this ambient braid at these histories."""
    if len(start) != len(end):
        return None
    if any(not 1 <= abs(x) < len(start) for x in word):
        raise ValueError('braid generator outside the temporal width')
    fraction = reverse_signed(tuple(word))
    n = next((i for i,x in enumerate(fraction) if x < 0),len(fraction))
    a,b,_ = coprime_parts(fraction[:n],inv(fraction[n:]))
    try:
        if follow(start,a,marks) == follow(end,b,marks):
            return a+inv(b)
    except ValueError:
        pass
    return None


class FacePair:
    def __init__(self, entry, edges, rules, marks):
        self.root, self.path, history, l, r = entry
        self.history = tuple((p,x) for p,x in history)
        self.left, self.right = tuple(l), tuple(r)
        path = self.path
        end_vertex(edges,self.root,path)
        for p,x in self.history:
            root, before, after = rules[x]
            if not (0 <= p <= len(path) and path.startswith(before,p)
                    and end_vertex(edges,self.root,path[:p]) == root):
                raise ValueError('ill-typed temporal event')
            path = path[:p]+after+path[p+len(before):]
        if follow(self.history,l,marks) != follow(self.history,r,marks):
            raise ValueError('nonparallel faces')


class HistoryGroup:
    """Finite positioned exchange graph and its fundamental group at start."""
    def __init__(self,start,marks):
        self.marks = marks
        seen = {start}
        todo = deque(seen)
        self.labels = {}
        self.generators = set()
        self.braids = {}
        tree_paths = {start: ()}
        width = len(start)
        while todo:
            h = todo.popleft()
            for i in range(1,width):
                for e in (i,-i):
                    k = exchange(h,e,self.marks)
                    if k is None:
                        continue
                    edge = (h,i) if e > 0 else (k,i)
                    if k not in seen:
                        seen.add(k)
                        tree_paths[k] = tree_paths[h]+(e,)
                        todo.append(k)
                        self.labels[edge] = ()
                    elif edge not in self.labels:
                        g = len(self.generators)+1
                        self.generators.add(g)
                        self.labels[edge] = (g,)
                        left = edge[0]
                        right = exchange_at(left,i-1,self.marks)
                        self.braids[g] = reduced(tree_paths[left]+(i,)+inv(tree_paths[right]))
        self.vertices = len(seen)
        self.tree_paths = tree_paths
        outgoing = defaultdict(list)
        indegree = Counter()
        for h,i in self.labels:
            dest = exchange_at(h,i-1,self.marks)
            outgoing[h].append(dest)
            indegree[dest] += 1
        ready = deque(h for h in seen if not indegree[h])
        processed = 0
        while ready:
            h = ready.popleft()
            processed += 1
            for dest in outgoing[h]:
                indegree[dest] -= 1
                if not indegree[dest]:
                    ready.append(dest)
        self.acyclic = processed == len(seen)
        self.relators = set()
        for h in sorted(seen):
            for i in range(1,width-1):
                self.relation(h,(i,i+1,i),(i+1,i,i+1),self.relators)
            for i,j in combinations(range(1,width),2):
                if j-i >= 2:
                    self.relation(h,(i,j),(j,i),self.relators)

    def relation(self,h,l,r,dest):
        a,b = self.read(h,l),self.read(h,r)
        if a is not None:
            assert b is not None and a[0] == b[0]
            word = reduced(b[1]+inv(a[1]))
            if word:
                dest.add(cyclic(word) if dest is self.relators else word)

    def read(self,h,word):
        result = ()
        for i in word:
            k = exchange(h,i,self.marks)
            if k is None:
                return None
            label = self.labels[h,i] if i > 0 else inv(self.labels[k,-i])
            result += label
            h = k
        return h,reduced(result)


def placements(h, root, initial, atoms, edges, marks):
    """Yield every matching temporal interval and spatial subpath at its slice."""
    path = initial
    for k in range(len(h)+1):
        for a in atoms:
            for offset in range(len(path)-len(a.path)+1):
                if not (path.startswith(a.path,offset) and end_vertex(edges,root,path[:offset]) == a.root):
                    continue
                fragment = tuple((p+offset,x) for p,x in a.history)
                if h[k:k+len(fragment)] == fragment:
                    yield k, a
        if k < len(h):
            pos,x = h[k]
            before,after = marks[x]
            path = path[:pos]+after+path[pos+len(before):]


class Presentation(HistoryGroup):
    def __init__(self, data):
        edges,rules = data['edges'],data['rules']
        if any(len(e) != 1 for e in edges):
            raise ValueError('edge names must be single characters')
        self.marks = {x:(l,r) for x,(_,l,r) in rules.items()}
        for root,l,r in rules.values():
            if end_vertex(edges,root,l) != end_vertex(edges,root,r):
                raise ValueError('nonparallel generating rule')
        q = FacePair(data['query'],edges,rules,self.marks)
        atoms = [FacePair(a,edges,rules,self.marks) for a in data['attachments']]
        super().__init__(q.history,self.marks)
        self.query = q
        self.atoms = defaultdict(set)
        self.defects = set()
        for h in sorted(self.tree_paths):
            for k, a in placements(h, q.root, q.path, atoms, edges, self.marks):
                l,r = (tuple(j+k for j in w) for w in (a.left,a.right))
                self.atoms[h].add((l,r))
                self.relation(h,l,r,self.defects)
        self.target = reduced(self.read(q.history,q.right)[1]+inv(self.read(q.history,q.left)[1]))
        self.relators.discard(())
        self.simplify()

    def simplify(self):
        while True:
            elim = next(((w,i) for w in sorted(self.relators,key=lambda w:(len(w),w))
                         for i,x in enumerate(w) if sum(abs(t)==abs(x) for t in w)==1), None)
            if elim is None:
                return
            w,i = elim
            g = abs(w[i])
            # Rotate the relator to g^sign * tail = 1.
            tail = w[i+1:]+w[:i]
            replace = inv(tail) if w[i] > 0 else tail
            def sub(v):
                return reduced(y for x in v for y in
                               (replace if x == g else inv(replace) if x == -g else (x,)))
            self.generators.remove(g)
            self.relators = {cyclic(sub(v)) for v in self.relators} - {()}
            self.defects = {sub(v) for v in self.defects} - {()}
            self.target = sub(self.target)

    def abelian_decision(self):
        gs = sorted(self.generators)
        for g,h in combinations(gs,2):
            a,b = self.braids[g],self.braids[h]
            n = len(self.query.history)
            if braid_image(n,a+b) != braid_image(n,b+a):
                return None
        def vec(w):
            return tuple(w.count(g)-w.count(-g) for g in gs)
        rows = [vec(w) for w in self.defects]
        for v in self.relators:
            rows.extend([vec(v),vec(inv(v))])
        return coefficients(rows,vec(self.target)) is not None

    def acyclic_raw(self):
        if not self.acyclic:
            return None
        todo = deque([self.query.left])
        seen = set(todo)
        while todo:
            w = todo.popleft()
            if w == self.query.right:
                return True
            h = self.query.history
            for j in range(len(w)+1):
                moves = list(self.atoms[h])
                if j+1 < len(w):
                    a,b = w[j:j+2]
                    if abs(a-b) >= 2:
                        moves.append(((a,b),(b,a)))
                    if b == a+1 and w[j:j+3] == (a,b,a):
                        moves.append(((a,b,a),(b,a,b)))
                for l,r in moves:
                    if w[j:j+len(l)] == l:
                        new = w[:j]+r+w[j+len(l):]
                        if new not in seen:
                            seen.add(new)
                            todo.append(new)
                if j < len(w):
                    h = exchange_at(h,w[j]-1,self.marks)
        return False

    def result(self):
        return dict(histories=self.vertices, generators=sorted(self.generators),
                    braid_generators={i:self.braids[i] for i in sorted(self.generators)},
                    relators=sorted(self.relators), directed_defects=sorted(self.defects),
                    target=self.target, surface=True if self.acyclic else self.abelian_decision(),
                    acyclic=self.acyclic, raw_on_acyclic_component=self.acyclic_raw())


def examples():
    # A length-changing rewrite separated from two scalar events by an edge.
    edges = {'f':('v','v'),'g':('v','v')}
    rules = {'a':('v','',''), 'b':('v','f','gg')}
    q = ['v','fg',[(2,'a'),(2,'a'),(0,'b')],[],[1,1]]
    atom = ['v','',[(0,'a'),(0,'a')],[],[1,1]]
    data = dict(edges=edges,rules=rules,query=q,attachments=[])
    p = Presentation(data)
    assert p.abelian_decision() is False
    data['attachments'] = [atom]
    assert Presentation(data).abelian_decision() is True
    data['query'] = ['v','fg',q[2],[1,1],[]]
    assert Presentation(data).abelian_decision() is False
    # Scalar next to a bubble that first creates and then consumes one wire.
    bubble = dict(edges={'f':('v','v')},rules={'a':('v','',''),'u':('v','','f'),'d':('v','f','')},
                  query=['v','',[(0,'a'),(0,'u'),(0,'d')],[],[1,2,2,1]],attachments=[])
    b = Presentation(bubble)
    assert b.vertices == 4 and len(b.generators) == 1 and not b.relators and len(b.target) == 1
    assert not b.acyclic and b.abelian_decision() is False
    # Three independent nonempty rewrites have a six-vertex cube component.
    h = [(2,'a'),(1,'a'),(0,'a')]
    cube = ['v','fff',h,[2,1,2],[1,2,1]]
    case = dict(edges={'f':('v','v')},rules={'a':('v','f','ff')},query=cube,attachments=[])
    cp = Presentation(case)
    assert cp.acyclic and not cp.generators and cp.acyclic_raw() is False
    case['attachments'] = [cube]
    assert Presentation(case).acyclic_raw() is True
    # Independent scalar-site vector solution in every nontrivial case here.
    checks = 0
    for a0 in range(4):
        for a1 in range(4):
            for d in (1,2,3):
                data['query'] = ['v','fg',q[2],[1]*a0,[1]*a1]
                data['attachments'] = [['v','',atom[2],[],[1]*d]]
                assert Presentation(data).abelian_decision() == (a1>=a0 and (a1-a0)%d == 0)
                checks += 1
    from semistrict_surface_three_axis_paths import Chart
    for sizes in product(range(4),repeat=3):
        generators = tuple((x,'f'*(v//2),'f'*(v%2)) for x,v in zip('abc',sizes))
        for gaps in product(('', 'f'),repeat=2):
            chart = Chart(generators,gaps)
            data = dict(edges={'f':('v','v')},rules={x:('v',u,v) for x,u,v in generators},
                        query=['v',chart.start_word(),chart.reading((2,1,0)),[2,1,2],[1,2,1]],
                        attachments=[])
            model = Presentation(data)
            assert model.acyclic == (not model.generators)
            if model.acyclic:
                assert not model.acyclic_raw()
            assert model.target == ()
    # The bubble component is a single four-edge circuit. Its possible
    # loops are independently the powers of 1221, so test both directions.
    tested = 0
    origin = b.query.history
    loop = (1,2,2,1)
    for length in range(6):
        for w in product((1,-1,2,-2),repeat=length):
            exp = sum(1 if x>0 else -1 for x in w)
            power = (loop if exp >= 0 else inv(loop))*(abs(exp)//4)
            want = exp%4 == 0 and braid_image(3,w) == braid_image(3,power)
            answer = realize(origin,origin,w,b.marks)
            assert (answer is not None) == want
            if answer is not None:
                assert b.read(origin,answer)[0] == origin and braid_image(3,w) == braid_image(3,answer)
            tested += 1
    # Nonabelian component: all three scalar occurrences have the same site.
    one = dict(edges={},rules={'a':('v','','')},query=['v','',[(0,'a')]*3,[],[1]],attachments=[])
    assert Presentation(one).abelian_decision() is None
    return p,b,checks,tested


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--presentation',type=Path)
    ap.add_argument('--realize',help='comma-separated signed braid, tested at the query face endpoints')
    args = ap.parse_args()
    if args.presentation:
        model = Presentation(json.loads(args.presentation.read_text()))
        if args.realize is None:
            print(json.dumps(model.result()))
        else:
            w = tuple(map(int,args.realize.split(','))) if args.realize else ()
            origin = model.query.history
            end = follow(origin,model.query.left,model.marks)
            print('legal signed path',realize(origin,end,w,model.marks))
    else:
        p,b,n,tested = examples()
        print('length-changing component',p.result())
        print('birth/death component',b.result())
        print(n,'directed attachment comparisons, 256 typed components and',tested,'ambient braid tests')
