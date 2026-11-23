"""Decide positioned raw private movies via per-strand orders and bounded SMT."""
from argparse import ArgumentParser
from collections import Counter,defaultdict
from itertools import combinations,product
import json
from pathlib import Path

from semistrict_surface_acyclic_private_movies import Traces
from semistrict_surface_penultimate_intervals import check
from semistrict_surface_private_histories import closure,solve as validate


class Reading:
    def __init__(self,n,steps):
        self.ops = []
        self.lines = [[] for _ in range(n)]
        self.gaps,self.labels = {},{}
        self.height = [0,0]
        order = list(range(n))
        counts = Counter()
        for name,i in steps:
            if name=='X':
                a,b = order[i:i+2]
                pair = min(a,b),max(a,b)
                node = (*pair,counts[pair])
                counts[pair] += 1
                self.lines[a].append((node,1))
                self.lines[b].append((node,-1))
                order[i:i+2] = b,a
                self.height[0] += i
            else:
                e = order[i]
                node = e,counts[e]
                counts[e] += 1
                self.gaps[node] = len(self.lines[e])
                self.labels[node] = name
                self.height[1] += i
            self.ops.append(node)


def footprint(node):
    return node[:2] if len(node)==3 else node[:1]


def fixed_order(a,b):
    """Holds when both have the same per-strand crossing lists."""
    for key,start in a.gaps.items():
        finish = b.gaps[key]
        if start==finish:
            continue
        sign = 1 if start<finish else -1
        if any(side!=sign for _,side in a.lines[key[0]][min(start,finish):max(start,finish)]):
            return False
    return True


def packets(ops):
    """Possible directed replacements, with crossing identities fixed throughout."""
    index = {op:k for k,op in enumerate(ops)}
    crosses = defaultdict(list)
    private = defaultdict(list)
    for op in ops:
        if len(op)==2:
            private[op[0]].append(index[op])
            continue
        a,b,repetition = op
        left,right = (a,b) if repetition%2==0 else (b,a)
        crosses[left,right].append(index[op])
    for (a,b),choices in crosses.items():
        for c in choices:
            for m in private[a]:
                yield (m,c)
            for m in private[b]:
                yield (c,m)
    names = {e for pair in crosses for e in pair}
    for a,b in list(crosses):
        for c in names:
            if (a,c) in crosses and (b,c) in crosses:
                yield from product(crosses[a,b],crosses[a,c],crosses[b,c])


def formula(a,b,length):
    ops = a.ops
    index = {op:k for k,op in enumerate(ops)}
    final = {index[op]:i for i,op in enumerate(b.ops)}
    choices = list(packets(ops))
    depends = [(i,j) for i,j in combinations(range(len(ops)),2)
               if set(footprint(ops[i])) & set(footprint(ops[j]))]
    flips = defaultdict(list)
    for k,nodes in enumerate(choices):
        for pair in combinations(sorted(nodes),2):
            flips[pair].append(k)
    lines = ['(set-logic QF_LIA)']
    def require(term):
        lines.append(f'(assert {term})')
    def place(t,i):
        return f'p{t}_{i}'
    for t in range(length+1):
        row = [place(t,i) for i in range(len(ops))]
        for name in row:
            lines.append(f'(declare-const {name} Int)')
            require(f'(and (<= 0 {name}) (< {name} {len(row)}))')
        if len(row)>1:
            require('(distinct '+' '.join(row)+')')
    for i,j in depends:
        require(f'(< {place(0,i)} {place(0,j)})')
        cmp = '<' if final[i]<final[j] else '>'
        require(f'({cmp} {place(length,i)} {place(length,j)})')
    for t in range(length):
        action = f'action{t}'
        lines.append(f'(declare-const {action} Int)')
        require(f'(and (<= 0 {action}) (< {action} {len(choices)}))')
        for k,nodes in enumerate(choices):
            for i,j in zip(nodes,nodes[1:]):
                require(f'(=> (= {action} {k}) (= {place(t,j)} (+ 1 {place(t,i)})))')
        for i,j in depends:
            ids = flips[i,j]
            cond = 'false' if not ids else '(or '+' '.join(f'(= {action} {k})' for k in ids)+')'
            before = f'(< {place(t,i)} {place(t,j)})'
            after = f'(< {place(t+1,i)} {place(t+1,j)})'
            require(f'(= {after} (xor {before} {cond}))')
    return '\n'.join([*lines,'(check-sat)'])


def solve(data,emit=None):
    h = tuple(map(tuple,data['history']))
    validate({**data,'source':h,'target':h})
    layers = data.get('higher',[])+[{},{}]
    if 'X' in layers[0]:
        raise ValueError('reserved exchange label')
    chart = Traces(data['marks'],*layers[:2])
    if chart.read(h,data['source'])[0]!=chart.read(h,data['target'])[0]:
        raise ValueError('nonparallel old readings')
    a,b = (Reading(len(h),data[k]) for k in ('source','target'))
    if set(a.ops)!=set(b.ops):
        return dict(raw_filler=False,obstruction='occurrence mismatch')
    changes = defaultdict(set)
    for p,q in layers[1].values():
        changes[p].add(q)
    if any(b.labels[m] not in closure(p,lambda x:changes[x]) for m,p in a.labels.items()):
        return dict(raw_filler=False,obstruction='private labels')
    cubes,prisms = (y-x for x,y in zip(a.height,b.height))
    if min(cubes,prisms)<0:
        return dict(raw_filler=False,obstruction='directed height')
    same = a.lines==b.lines
    result = dict(cubes=cubes,prisms=prisms,fixed_crossing_orders=same)
    if emit is None and (same or not cubes):
        return dict(result,raw_filler=same and fixed_order(a,b))
    query = formula(a,b,cubes+prisms)
    if emit is not None:
        emit.write_text(query+'\n')
    answer = check(query)
    if answer not in ('sat','unsat'):
        raise RuntimeError(answer)
    return dict(result,raw_filler=answer=='sat')


def checks():
    from semistrict_surface_positive_movies import moves
    h = ((0,'s'),)*2
    data = dict(edges={},initial=[],start_vertex=0,marks={'s':[[],[]]},scalar_at={'s':0},
                higher=[{'p':['s','s']}],history=h)
    n=0
    for k in range(2,5):
        words = set()
        for positions in combinations(range(k+2),2):
            for left,right in product(range(2),repeat=2):
                w = [('X',0)]*(k+2)
                w[positions[0]],w[positions[1]] = ('p',left),('p',right)
                words.add(tuple(w))
        for a in words:
            reached = closure(a,lambda w:(q for _,q in moves(h,w,{'p':(('s',),('s',))})))
            ra=Reading(2,a)
            for b in words:
                rb=Reading(2,b)
                assert ((set(ra.ops)==set(rb.ops) and fixed_order(ra,rb)) == (b in reached))
                n+=1
    # Compare the symbolic solver with physical closure on genuinely nonsimple
    # three-strand words, including visits to the same pair after a full twist.
    data['history']=[(0,'s')]*3
    from semistrict_surface_single_power import spellings
    words=[]
    for pure in spellings((1,2,1,1,2,1)):
        for where in (0,2,len(pure)):
            for i in (0,2):
                w=tuple(('X',j-1) for j in pure)
                words.append(w[:where]+(('p',i),)+w[where:])
    tests=used=0
    for a in words[::5]:
        reached=closure(a,lambda w:(q for _,q in moves(data['history'],w,{'p':(('s',),('s',))})))
        for b in words[::4]:
            result=solve(dict(data,source=a,target=b))
            assert result['raw_filler']==(b in reached)
            tests+=1
            used+=int(not result.get('fixed_crossing_orders',True) and result.get('cubes',0)>0)
    assert used
    print(f'{n} two-strand comparisons and {tests} three-strand full-twist comparisons '
          f'agree with native reachability ({used} nontrivial SMT calls)')


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--faces',type=Path)
    p.add_argument('--emit',type=Path,help='write the bounded SMT problem when occurrence and grade tests pass')
    args=p.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()),args.emit)))
    else:
        checks()
