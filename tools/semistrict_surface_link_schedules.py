"""Decide signed polygon schedules with abelian named seam groups, allowing changing arities."""
from argparse import ArgumentParser
from collections import Counter, deque
from itertools import combinations
import json
from pathlib import Path

from semistrict_surface_component_braids import Components, cabling
from semistrict_surface_history_group import inv
from semistrict_surface_packet_meetings import cut
from semistrict_surface_polygon_grades import resolution
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_signed_width_two import Movies, Presentation, Rule
from semistrict_surface_transfer_cables import cables


def plus(a, b, sign=1):
    c = Counter(a)
    for k,v in b.items():
        c[k] += sign*v
    return {k:v for k,v in c.items() if v}


def possible(equations):
    """Integer consistency by unimodular column operations and substitution."""
    variables = sorted({k for row in equations for k in row if k >= 0})
    rows = [[-row.get(-1,0),*(row.get(k,0) for k in variables)] for row in equations]
    while rows:
        base = rows.pop()
        while True:
            live = [i for i in range(1,len(base)) if base[i]]
            if len(live) <= 1:
                break
            i = min(live,key=lambda j:abs(base[j]))
            j = next(k for k in live if k != i)
            div = base[j]//base[i]
            for row in rows:
                row[j] -= div*row[i]
            base[j] -= div*base[i]
        if not live:
            if base[0]:
                return False
            continue
        i, = live
        value, rem = divmod(base[0],base[i])
        if rem:
            return False
        for row in rows:
            row[0] -= row.pop(i)*value
    return True


def advance(form, vector, var=-1):
    out = form.copy()
    for pair,value in vector.items():
        out[pair] = plus(out.get(pair,{}),{var:value})
    return out


def equalities(a,b):
    return [row for pair in a.keys() | b.keys() if (row := plus(a.get(pair,{}),b.get(pair,{}),-1))]


class Schedules:
    def __init__(self,model,source,resolved):
        _,flow,self.graph,_ = resolved
        self.units = cables(list(flow),self.graph,self.graph)
        self.root = tuple((off,(-1,i)) for i,(off,_) in enumerate(source))
        labels = {e:c for (_,e),(_,c) in zip(self.root,source)}
        rules = []
        for rid,ins,outs in self.graph.values():
            r = model.pres.rules[rid]
            for (_,c),e in zip(r.source,ins):
                assert labels[e] == c
            labels.update((e,c) for e,(_,c) in zip(outs,r.target))
            rules.append(Rule(r.path,tuple((i,e) for (i,_),e in zip(r.source,ins)),
                              tuple((i,e) for (i,_),e in zip(r.target,outs))))
        marks = {e:model.pres.marks[c] for e,c in labels.items()}
        roots = {e:model.pres.mark_roots[c] for e,c in labels.items()}
        self.model = Movies(Presentation(model.pres.edges,marks,rules,roots),model.start)
        self.passives = {}
        self.factors = {}
        self.nonabelian_guards = 0
        self.gain_visits = self.meet_visits = 0

    def crossing(self,h,j,sign):
        return {tuple(sorted((u,v))):sign for u in self.units[h[j][1]] for v in self.units[h[j+1][1]]}

    def read(self,word,order):
        value,records,forms = {},{},{}
        h = self.root
        for (name,i),(_,p) in zip(word,order):
            if p is None:
                value = plus(value,self.crossing(h,i,1))
                h = self.model.swap(h,i,True)
            else:
                records[p] = (h,i)
                forms[p] = advance({},value)
                h,_ = self.model.named(h,p,i)
        return h,records,forms,value

    def passive(self,p,h,i):
        """Signed exterior paths: tree offsets and an integral lattice of loops."""
        key = p,h,i
        if key not in self.passives:
            offsets,cycles = {h:{}},set()
            todo = deque([h])
            while todo:
                v = todo.popleft()
                for j in range(len(v)-1):
                    if not (j+2<=i or j>=i+len(self.graph[p][1])):
                        continue
                    for s in (-1,1):
                        w = self.model.swap(v,j,s>0)
                        if w is None:
                            continue
                        shift = plus(offsets[v],self.crossing(v,j,s))
                        if w not in offsets:
                            offsets[w] = shift
                            todo.append(w)
                        else:
                            cycle = plus(shift,offsets[w],-1)
                            if cycle:
                                if cycle[min(cycle)]<0:
                                    cycle = {k:-v for k,v in cycle.items()}
                                cycles.add(tuple(sorted(cycle.items())))
            self.passives[key] = offsets,[dict(c) for c in sorted(cycles)]
        return self.passives[key]

    def align(self,p,rec,form,var):
        h,i = rec[p]
        offsets,cycles = self.passive(p,h,i)
        f = form[p]
        for j,c in enumerate(cycles,var):
            f = advance(f,c,j)
        for v,delta in offsets.items():
            yield {**rec,p:(v,i)},{**form,p:advance(f,delta)},var+len(cycles)

    def nonabelian_factors(self,h):
        """True pure sibling braid generators, transported to this history."""
        if h in self.factors:
            return self.factors[h]
        marks = self.model.pres.marks
        parts = Components(h,marks,len(self.model.start))
        result = []
        if any(len(face)>2 for face in parts.faces):
            queue = deque([(h,())])
            seen = {h}
            while queue:
                root,path = queue.popleft()
                packets = parts.packets(root,marks)
                if packets is not None:
                    break
                for i in range(len(root)-1):
                    for sign in (-1,1):
                        v = self.model.swap(root,i,sign>0)
                        if v is not None and v not in seen:
                            seen.add(v)
                            queue.append((v,path+(sign*(i+1),)))
            else:
                raise ValueError('no grouped history in a named component')
            for face in packets:
                if len(face)<3:
                    continue
                images = []
                for i,j in combinations(range(len(face)),2):
                    around = tuple(range(j,i+1,-1))
                    twist = around+(i+1,i+1)+inv(around)
                    images.append(braid_image(len(h),path+cabling(face,twist)+inv(path)))
                result.append(images)
        self.factors[h] = result
        return result

    def absorbs(self,h,slots):
        root = tuple((j+1,) for j in range(len(h)))
        factors = self.nonabelian_factors(h)
        ok = all(any(all(cut(f,i,k) == cut(root,i,k) for f in generators)
                     for i,k in slots) for generators in factors)
        if ok and factors:
            self.nonabelian_guards += 1
        return ok

    def terminal_exact(self):
        # Straighten from both ends up to a single connector. The exact
        # common unit total then determines this connector without a guard.
        split = len(self.target_order)
        for j,p in enumerate(self.target_order):
            h,i = self.target[p]
            if not self.absorbs(h,[(i,len(self.graph[p][1]))]):
                split = j
                break
        for p in self.target_order[split:]:
            h,i = self.target[p]
            out,_ = self.model.named(h,p,i)
            if not self.absorbs(out,[(i,len(self.graph[p][2]))]):
                return False
        return True

    def branches(self,order,rec,form,var,eqs,visited,safe):
        if order == self.target_order:
            f, equations, j = form.copy(), list(eqs), var
            for p in order:
                h,i = rec[p]
                t,k = self.target[p]
                if i!=k:
                    break
                offsets,loops = self.passive(p,h,i)
                if t not in offsets:
                    break
                z = advance(f[p],offsets[t])
                for c in loops:
                    z = advance(z,c,j)
                    j += 1
                equations.extend(equalities(z,self.goal[p]))
            else:
                if possible(equations):
                    yield True if safe and self.terminal_exact() else None
        for p in order:
            initial,i = rec[p]
            if not self.before(initial,i) < self.target_before[p]:
                continue
            for r,f,j in self.align(p,rec,form,var):
                h,i = r[p]
                _,off = self.model.named(h,p,i)
                for block in self.model.prism_words(h,p,i,off):
                    k = h
                    delta = {}
                    for g in block:
                        at = abs(g)-1
                        delta = plus(delta,self.crossing(k,at,1 if g>0 else -1))
                        k = self.model.swap(k,at,g>0)
                    if not self.before(k,i+1) <= self.target_before[p]:
                        continue
                    self.gain_visits += 1
                    yield order,{**r,p:(k,i+1)},{**f,p:advance(f[p],delta)},j,eqs,{order},safe
        for index,(p,q) in enumerate(zip(order,order[1:])):
            changed = order[:index]+(q,p)+order[index+2:]
            if changed in visited:
                continue
            for r,f,j in self.align(p,rec,form,var):
                h,i = r[p]
                mid,_ = self.model.named(h,p,i)
                for t,z,l in self.align(q,r,f,j):
                    k,b = t[q]
                    if k != mid:
                        continue
                    a,c = map(len,self.graph[p][1:])
                    d,e = map(len,self.graph[q][1:])
                    if b+d<=i:
                        b0,i1 = b,i+e-d
                    elif b>=i+c:
                        b0,i1 = b+a-c,i
                    else:
                        continue
                    equations = eqs+equalities(z[p],z[q])
                    if not possible(equations):
                        continue
                    new,_ = self.model.named(h,q,b0)
                    self.meet_visits += 1
                    yield (changed,{**t,q:(h,b0),p:(new,i1)},z,l,equations,
                           visited|{changed},safe and self.absorbs(mid,[(i,c),(b,d)]))

    def before(self,h,i):
        return frozenset(u for _,e in h[:i] for u in self.units[e])

    def solve(self,first,second,readings):
        h,rec,form,total = self.read(first,readings[0])
        t,self.target,self.goal,final = self.read(second,readings[1])
        if h != t or total != final:
            return False
        self.target_before = {p:self.before(k,i) for p,(k,i) in self.target.items()}
        if any(not self.before(k,i)<=self.target_before[p] for p,(k,i) in rec.items()):
            return False
        self.target_order = tuple(self.target)
        order = tuple(rec)
        stack = [self.branches(order,rec,form,0,[],{order},True)]
        maybe = False
        while stack:
            step = next(stack[-1],False)
            if step is False:
                stack.pop()
            elif step is True:
                return True
            elif step is None:
                maybe = True
            else:
                stack.append(self.branches(*step))
        return None if maybe else False


def decide(model,source,first,second):
    if model.attachments or model.parse(source,first)[1] != model.parse(source,second)[1]:
        raise ValueError('expected parallel positive 3-computad readings')
    arities = [(len(r.source),len(r.target)) for r in model.pres.rules]
    resolved = resolution(source,(first,second),arities,'swap')
    if resolved is None:
        return dict(surface=False,obstruction='named incidence')
    from semistrict_surface_joint_labels import positive_normal
    from semistrict_surface_serial_polygons import frames
    widths,flow,graph,readings = resolved
    totals = [positive_normal(sum(widths),frames(source,graph,flow,r,model.parse(source,w)[0])[0])
              for r,w in zip(readings,(first,second))]
    if totals[0] != totals[1]:
        return dict(surface=False, obstruction='resolved total braid')
    if not graph:
        return dict(surface=True, gain_branches=0, meeting_branches=0, passive_charts=0)
    chart = Schedules(model,source,resolved)
    yes = chart.solve(first,second,resolved[-1])
    return dict(surface=yes, gain_branches=chart.gain_visits,
                meeting_branches=chart.meet_visits, passive_charts=len(chart.passives),
                absorbed_nonabelian_guards=chart.nonabelian_guards)


def nonabelian_checks():
    from semistrict_surface_one_step_reflection import reverse_signed
    from semistrict_surface_polygon_cabling import rectangle
    from semistrict_surface_raw_movie_graph import raw_compare,steps
    s = ((0,'s'),)
    mark = ((0,'a'),)
    m = Movies(Presentation({'k':(0,1),'f':(1,2),'g':(2,3),'u':(1,1)},
                            {'s':('',''),'a':('f','f'),'b':('g','g'),
                             'birth':('','u'),'death':('u','')},
                            [Rule('f',mark,((0,'birth'),(0,'death'))),Rule('f',mark,mark)],
                            {'s':0}), 'kfg')
    h = s*3+((2,'b'),)*2+((1,'a'),)*2
    a,b = (1,1,2,2),(2,2,1,1)
    z = reverse_signed(inv(a)+b)
    k = next((i for i,g in enumerate(z) if g<0),len(z))
    def cross(word): return steps(g-1 for g in word)
    x = cross(a)+((1,6),)+steps(rectangle(3,2,1))+((0,3),)+cross(z[:k])
    y = cross(b)+((0,5),)+steps(rectangle(3,2,2))+((1,7),)+cross(inv(z[k:]))
    result = decide(m,h,x,y)
    assert braid_image(3,a) != braid_image(3,b) and not raw_compare(m,h,x,y)['raw']
    assert result['surface'] and result['absorbed_nonabelian_guards'] >= 2
    # At two occupied gaps, each three-sibling group sees the other slot
    # as exterior. Assigning all of them to one polygon would fail.
    pure = Movies(Presentation({'f':(0,0)}, {'s':('','')},[],{'s':0}), 'f')
    source = s*3+((1,'s'),)*3
    resolved = resolution(source,((),()),[],'swap')
    chart = Schedules(pure,source,resolved)
    slots = [(1,1),(4,1)]
    assert len(chart.nonabelian_factors(chart.root)) == 2
    assert chart.absorbs(chart.root,slots)
    assert not any(chart.absorbs(chart.root,[slot]) for slot in slots)
    return dict(nonabelian_surface_only=result,split_factor_guard=True)


def checks():
    from itertools import product
    from random import Random
    from semistrict_surface_one_gain import positive_steps
    from semistrict_surface_polygon_cabling import rectangle
    from semistrict_surface_raw_movie_graph import raw_compare, steps
    from semistrict_surface_single_polygon import decide as single
    rng = Random(619)
    linear = 0
    for _ in range(1800):
        a,b,c,d,e,f = [rng.randrange(-2,3) for _ in range(6)]
        witness = any(a*x+b*y==c and d*x+e*y==f for x,y in product(range(-8,9),repeat=2))
        assert possible([{0:a,1:b,-1:-c},{0:d,1:e,-1:-f}]) == witness
        linear += 1
    s = ((0,'s'),)
    bubble = ((0,'b'),(0,'d'))
    ports = {'s':('',''),'b':('','f'),'d':('f','')}
    m = Movies(Presentation({'f':(0,0)},ports,[Rule('',s,bubble)],{'s':0,'b':0}),'f')
    h = ((1,'s'),)*2+s*2
    x = steps((2,1,2))+((0,3),)+steps(rectangle(0,2,1))+((0,0),)
    y = steps((1,2,1))+((0,2),)+steps(rectangle(0,2,2))+((0,4),)
    crossing = decide(m,h,x,y)
    assert crossing['surface'] and crossing['meeting_branches'] and not raw_compare(m,h,x,y)['raw']
    assert decide(m,h,y,x)['surface'] is False
    # Independent exact one-polygon signed answer on mixed bubbling sites.
    single_queries = 0
    for letter in (0,1):
        src = ((letter,'s'),)*2+((1-letter,'s'),)
        for w in ((),steps((0,0)),steps((1,1))):
            for a,b in ((((0,0),)+steps((1,0)),steps((0,))+((0,1),)),
                        (steps((0,))+((0,0),),((0,1),)+steps((0,1)))):
                for left,right in ((w+a,w+b),(w+b,w+a)):
                    try:
                        m.parse(src,left)
                        m.parse(src,right)
                    except ValueError:
                        continue
                    answer = single(m,src,left,right,radius=4)['surface']
                    assert answer is not None and decide(m,src,left,right)['surface']==answer
                    single_queries += 1
    trajectories = 0
    for _ in range(100):
        h = s*2+((1,'s'),)
        k,first = h,()
        changes = 0
        for _ in range(rng.randint(2,5)):
            opts = [(('swap',i),m.swap(k,i,True)) for i in range(len(k)-1)]
            if changes<2:
                opts += [((0,i),r[0]) for i in range(len(k)) if (r:=m.named(k,0,i))]
            opts = [(op,t) for op,t in opts if t is not None]
            if not opts: break
            op,k = rng.choice(opts)
            changes += op[0]!='swap'
            first += (op,)
        last = first
        for _ in range(3):
            choices = list(positive_steps(m,h,last))
            if not choices: break
            last,_ = rng.choice(choices)
        assert decide(m,h,first,last)['surface'] is True
        trajectories+=1
    # The endpoint records agree after forgetting winding. A required
    # polygon exchange would have to pass a nonzero two-strand loop.
    pure = Movies(Presentation({}, {'s':('','')},[Rule('',s,s)],{'s':0}),'')
    first = ((0,0),)+steps((0,0))+((0,1),)
    last = ((0,1),)+steps((0,0))+((0,0),)
    assert decide(pure,s*2,first,last)['surface'] is False
    # Equal linking on unequal prefixes, with the same full positive braid.
    from semistrict_surface_history_group import inv
    from semistrict_surface_one_step_reflection import reverse_signed
    a,b = (1,1,2,2),(2,2,1,1)
    fraction = reverse_signed(inv(a)+b)
    at = next((k for k,g in enumerate(fraction) if g<0),len(fraction))
    def marked(u,v):
        return steps(g-1 for g in u)+((0,1),)+steps(g-1 for g in v)
    left,right = marked(a,fraction[:at]),marked(b,inv(fraction[at:]))
    assert decide(pure,s*3,left,right)['surface'] is None
    from semistrict_surface_stationary_polygons import decide as stationary
    assert stationary(pure,s*3,left,right)['surface'] is False
    # Width two gives an independent full decision even when sliding one
    # scalar between the two ends of f changes the named history group.
    moving = Movies(Presentation({'f':(0,0)},{'s':('','')},
                     [Rule('f',s,((1,'s'),)),Rule('f',((1,'s'),),s)],{'s':0}),'f')
    src = s*2
    grouped = {}
    todo = [(src,())]
    while todo:
        h,w = todo.pop()
        grouped.setdefault(h,[]).append(w)
        if len(w)==4: continue
        t = moving.swap(h,0,True)
        if t is not None: todo.append((t,w+(('swap',0),)))
        for i,p in product(range(2),repeat=2):
            r = moving.named(h,p,i)
            if r is not None: todo.append((r[0],w+((p,i),)))
    width_tests = accepted = 0
    for group in grouped.values():
        for first in group:
            for last in rng.sample(group,min(4,len(group))):
                exact = moving.compare(src,first,last)['surface']
                assert decide(moving,src,first,last)['surface'] == exact
                width_tests+=1
                accepted+=exact
    return dict(integer_systems=linear,signed_single_queries=single_queries,
                placed_trajectories=trajectories, changing_order_surface_only=crossing,
                winding_guard_rejected=True, nonabelian_uncertified=True,
                width_two_queries=width_tests,width_two_positives=accepted,**nonabelian_checks())


if __name__ == '__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        if q.get('attachments'): raise ValueError('expected a 3-computad')
        rules=[Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target'])))
               for r in q['rules']]
        model=Movies(Presentation(q['edges'],q['marks'],rules,q.get('mark_roots')),q['start'])
        source=tuple(map(tuple,q['source']))
        model.pres.walk(model.start,source,q.get('vertex'))
        result=decide(model,source,q['first'],q['second'])
    else:
        result=checks()
    print(json.dumps(result))
