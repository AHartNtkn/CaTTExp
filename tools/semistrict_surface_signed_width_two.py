"""Test degree-four Gray surface comparisons for positive 3-computads using signed exchanges."""
from argparse import ArgumentParser
from collections import Counter, deque
from dataclasses import dataclass
import json
from itertools import chain, permutations
from pathlib import Path

from semistrict_surface_return_gaps import Presentation, Rule, exchange_at


@dataclass
class Attachment:
    path: str
    source: tuple  # temporal input history shared by its two 3-faces
    first: list
    second: list


class Movies:
    def __init__(self,pres,start,attachments=()):
        self.pres=pres
        self.start=start
        self.patch_ends=[pres.walk(r.path,r.source)[-1] for r in pres.rules]
        self.globally_thin = (all(s for s,_ in pres.marks.values()) or
                              all(t for _,t in pres.marks.values()))
        self.thin_components = {}
        self.attachments = []
        self.deltas = set()
        for tile in attachments:
            pres.walk(tile.path,tile.source)
            local = Movies(pres,tile.path)
            left,h = local.parse(tile.source,tile.first)
            right,k = local.parse(tile.source,tile.second)
            if h != k:
                raise ValueError('a 4-rule requires parallel faces')
            if not tile.source:
                continue  # Both faces are identities by temporal positivity.
            self.attachments.append((tile,len(left)))
            self.deltas.add(len(right)-len(left))
        if any(d>0 for d in self.deltas) and any(d<0 for d in self.deltas):
            raise ValueError('4-rules must be jointly nondecreasing or jointly nonincreasing in polygon count')

    def swap(self,h,k,positive):
        if k<0 or k+1>=len(h):
            return None
        if positive:
            return exchange_at(h,k,self.pres.marks)
        (i,a),(j,b)=h[k:k+2]
        source,target=self.pres.marks[a]
        if i+len(target)>j:
            return None
        out=h[:k]+((j+len(source)-len(target),b),(i,a))+h[k+2:]
        assert exchange_at(out,k,self.pres.marks)==h
        return out

    def thin(self, history):
        if self.globally_thin:
            return True
        if history in self.thin_components:
            return self.thin_components[history]
        # Explore both directions, including distinct oriented loops at empty
        # sites. The positive graph has a cycle exactly for nontrivial isotropy.
        outgoing = {}
        incoming = Counter()
        todo = [history]
        while todo:
            h = todo.pop()
            if h in outgoing:
                continue
            outgoing[h] = []
            for j in range(len(h)-1):
                for positive in (True, False):
                    dest = self.swap(h,j,positive)
                    if dest is None:
                        continue
                    if positive:
                        outgoing[h].append(dest)
                        incoming[dest] += 1
                    if dest not in outgoing:
                        todo.append(dest)
        ready = [h for h in outgoing if not incoming[h]]
        count = 0
        while ready:
            h = ready.pop()
            count += 1
            for dest in outgoing[h]:
                incoming[dest] -= 1
                if not incoming[dest]:
                    ready.append(dest)
        acyclic = count == len(outgoing)
        self.thin_components.update(dict.fromkeys(outgoing,acyclic))
        return acyclic

    def named(self,h,rid,i):
        rule=self.pres.rules[rid]
        if i<0 or i+len(rule.source)>len(h):
            return None
        off=h[i][0]-rule.source[0][0]
        if off<0 or not self.pres.walk(self.start,h[:i])[-1].startswith(rule.path,off):
            return None
        left=tuple((p+off,n) for p,n in rule.source)
        if h[i:i+len(left)]!=left:
            return None
        right=tuple((p+off,n) for p,n in rule.target)
        return h[:i]+right+h[i+len(left):],off

    def parse(self,source,actions):
        h=source
        records=[]
        for name,i in actions:
            if name=='swap':
                out=self.swap(h,i,True)
                if out is None:
                    raise ValueError('expected a native positive swap')
                h=out
            else:
                if not isinstance(name, int) or not 0 <= name < len(self.pres.rules):
                    raise ValueError('expected a zero-based rule index')
                result=self.named(h,name,i)
                if result is None:
                    raise ValueError('unavailable declared rule')
                records.append((h,name,i))
                h=result[0]
        return tuple(records),h

    def prism_words(self,h,rid,i,off):
        size = len(self.pres.rules[rid].source)
        if i+size >= len(h):
            return
        pos,event = h[i+size]
        # The spectator must clear the entire spatial window, including padding.
        if pos+len(self.pres.marks[event][0]) <= off:
            yield tuple(range(i+size,i,-1))
        if pos >= off+len(self.patch_ends[rid]):
            yield tuple(-j for j in range(i+size,i,-1))

    def updates(self,state):
        for k,(h,rid,i) in enumerate(state):
            r=self.pres.rules[rid]
            size=len(r.source)
            out,off=self.named(h,rid,i)
            for j in range(len(h)-1):
                if j+2<=i or j>=i+size:
                    for positive in (True,False):
                        dest=self.swap(h,j,positive)
                        if dest is not None:
                            yield state[:k]+((dest,rid,i),)+state[k+1:],'disjoint square'
            # Native prism in either spatial order: the polygon moves later in temporal order.
            for word in self.prism_words(h,rid,i,off):
                new=h
                for g in word:
                    new=self.swap(new,abs(g)-1,g>0)
                    assert new is not None
                assert self.named(new,rid,i+1) is not None
                yield state[:k]+((new,rid,i+1),)+state[k+1:],'prism'
            if k+1>=len(state):
                continue
            before,second,j=state[k+1]
            if out!=before:
                continue
            other=self.pres.rules[second]
            if j+len(other.source)<=i:
                j0=j
                i1=i+len(other.target)-len(other.source)
            elif j>=i+len(r.target):
                j0=j+size-len(r.target)
                i1=i
            else:
                continue
            after,_=self.named(h,second,j0)
            assert self.named(after,rid,i1)[0]==self.named(before,second,j)[0]
            yield state[:k]+((h,second,j0),(after,rid,i1))+state[k+2:],'disjoint rules'

    def seam_histories(self, history):
        seen = {history}
        todo = [history]
        while todo:
            h = todo.pop()
            yield h
            for j in range(len(h)-1):
                for positive in (True,False):
                    dest = self.swap(h,j,positive)
                    if dest is not None and dest not in seen:
                        seen.add(dest)
                        todo.append(dest)

    def attachment_updates(self,state,final,limit):
        for tile,count in self.attachments:
            target_count = sum(name!='swap' for name,_ in tile.second)
            if len(state)-count+target_count > limit:
                continue
            width = len(tile.source)
            for k in range(len(state)-count+1):
                seam = state[k][0] if k<len(state) else final
                for h in self.seam_histories(seam):
                    paths = self.pres.walk(self.start,h)
                    for i in range(len(h)-width+1):
                        off = h[i][0]-tile.source[0][0]
                        if off<0 or not paths[i].startswith(tile.path,off):
                            continue
                        if h[i:i+width] != tuple((p+off,n) for p,n in tile.source):
                            continue
                        left,_ = self.parse(h,[(n,i+j) for n,j in tile.first])
                        if left!=state[k:k+count]:
                            continue
                        right,_ = self.parse(h,[(n,i+j) for n,j in tile.second])
                        yield state[:k]+right+state[k+count:], 'declared 4-rule'

    def whole_cuts(self,source,actions,records):
        next_record = iter(records)
        blocks,barriers = [],[]
        start,cut = source,0
        for index,(rid,i) in enumerate(actions):
            if rid=='swap':
                continue
            h,_,_ = next(next_record)
            if len(h)==len(self.pres.rules[rid].source):
                blocks.append((start,actions[cut:index]))
                barriers.append((h,rid))
                start,_ = self.named(h,rid,i)
                cut = index+1
        return blocks+[(start,actions[cut:])],barriers

    def compare(self,source,first,second):
        self.pres.walk(self.start,source)
        u,a=self.parse(source,first)
        v,b=self.parse(source,second)
        if a!=b:
            raise ValueError('expected parallel old readings')
        if not self.attachments and Counter(r for _,r,_ in u)!=Counter(r for _,r,_ in v):
            return dict(surface=False,states=0)
        if ((len(u)<len(v) and not any(d>0 for d in self.deltas)) or
            (len(u)>len(v) and not any(d<0 for d in self.deltas))):
            return dict(surface=False,states=0)
        from semistrict_surface_two_slot_polygons import compare as two_slot_compare, width_at_most_two
        if not self.attachments and any(width_at_most_two(self,source,r) for r in (u,v)):
            return two_slot_compare(self,source,first,second,u,v,True)
        if not self.attachments:
            left,cuts = self.whole_cuts(source,first,u)
            right,other = self.whole_cuts(source,second,v)
            if cuts!=other:
                return dict(surface=False,states=0,obstruction='whole-history polygons')
            if cuts:
                pieces = [self.compare(h,x,y) for (h,x),(_,y) in zip(left,right)]
                answers = [x['surface'] for x in pieces]
                yes = False if False in answers else None if None in answers else True
                return dict(surface=yes,states=sum(x['states'] for x in pieces),pieces=pieces)
        limit = max(len(u),len(v))
        if first==second and not self.globally_thin:
            return dict(surface=True,states=1,moves=[])
        def certified(state):
            return self.thin(b) and all(self.thin(h) for h,_,_ in state)
        # A second visit with certified seams can give a positive result even
        # after an uncertified visit to the same record list.
        u=(u,certified(u))
        previous={u:None}
        queue=deque([u])
        unresolved = False
        while queue:
            current=queue.popleft()
            state,safe = current
            if state==v and safe:
                labels=[]
                while previous[current] is not None:
                    current,label=previous[current]
                    labels.append(label)
                return dict(surface=True,states=len(previous),moves=labels[::-1])
            if state==v:
                unresolved = True
            for nxt,label in chain(self.updates(state),self.attachment_updates(state,b,limit)):
                nxt=(nxt,safe and certified(nxt))
                if nxt not in previous:
                    previous[nxt]=current,label
                    queue.append(nxt)
        if unresolved and not self.attachments and len(v)<=1:
            if not v:
                from semistrict_surface_shared_edge import braid_image
                images = [braid_image(len(source),tuple(i+1 for _,i in face)) for face in (first,second)]
                return dict(surface=images[0]==images[1],states=len(previous),method='pure braid')
            from semistrict_surface_single_polygon import decide
            return dict(states=len(previous),**decide(self,source,first,second))
        if unresolved and not self.attachments:
            from semistrict_surface_stationary_polygons import decide as stationary
            result = stationary(self,source,first,second)
            if result['surface'] is not None:
                return dict(states=len(previous),**result)
            from semistrict_surface_one_gain import decide as one_gain
            result = one_gain(self,source,first,second,result,forced_only=True)
            if result['surface'] is not None:
                return dict(states=len(previous),**result)
            from semistrict_surface_packet_meetings import supported, decide as scalar_packets
            if supported(self,source,(*first,*second)):
                return dict(states=len(previous),**scalar_packets(self,source,first,second))
            from semistrict_surface_order_locks import decide as ordered
            chain_result = ordered(self,source,first,second)
            if chain_result['surface'] is not None:
                return dict(states=len(previous),**chain_result)
            from semistrict_surface_positioned_packets import supported as shape_preserving, decide as packets
            if shape_preserving(self,(*first,*second)):
                return dict(states=len(previous),**packets(self,source,first,second))
            from semistrict_surface_endomorphism_runs import supported as endomorphism_runs, decide as resolved_packets
            if endomorphism_runs(self,(*first,*second)):
                return dict(states=len(previous),**resolved_packets(self,source,first,second))
            from semistrict_surface_padded_packets import decide as padded_packets
            padded = padded_packets(self,source,first,second)
            if padded['surface'] is not None:
                return dict(states=len(previous),**padded)
            from semistrict_surface_link_schedules import decide as link_schedules
            linked = link_schedules(self,source,first,second)
            if linked['surface'] is not None:
                return dict(states=len(previous),**linked)
        if unresolved:
            return dict(surface=None,states=len(previous),reason='nontrivial exchange group on a connector')
        return dict(surface=False,states=len(previous))


def wider_checks():
    from semistrict_surface_raw_movie_graph import raw_compare
    # With a single polygon in a fixed window, a disjoint spectator can move
    # from after to before it. A spectator inside its window cannot pass it.
    # This subset order provides an oracle independent of diagram search.
    path = 'fghi'
    edges = {e: (i,i+1) for i,e in enumerate(path)}
    marks = {e: (e,e) for e in path}
    marks.update(x=('g','g'), y=('g','g'))
    histories = tuple(permutations(tuple(enumerate(path))))
    initial = histories[-1]

    def sorting_steps(word):
        steps = []
        word = list(word)
        while any(a[0] > b[0] for a,b in zip(word,word[1:])):
            k = next(i for i,(a,b) in enumerate(zip(word,word[1:])) if a[0] > b[0])
            word[k:k+2] = reversed(word[k:k+2])
            steps.append(('swap',k))
        return steps

    comparisons = 0
    for left,right in [(1,2),(0,2),(1,4),(0,4)]:
        offset = 1-left
        rule = Rule(path[left:right], ((offset,'g'),), ((offset,'x'),(offset,'y')))
        model = Movies(Presentation(edges,marks,[rule]),path)
        movies = []
        for history in histories:
            index = history.index((1,'g'))
            # Sort the reverse initial word into the selected intermediate order.
            ranks = {event:i for i,event in enumerate(history)}
            before = sorting_steps([(ranks[e],e) for e in initial])
            out,_ = model.named(history,0,index)
            actions = before + [(0,index)] + sorting_steps(out)
            prefix = {p for p,_ in history[:index]}
            movies.append((actions,prefix))
        inside = set(range(left,right))
        for first,src in movies:
            for second,dst in movies:
                expected = src <= dst and (src & inside) == (dst & inside)
                assert model.compare(initial,first,second)['surface'] == expected
                comparisons += 1

    # Enumerate the forward cube faces with unequal spatial lengths. Distinct
    # readings have the same signed endpoints, including each reverse cube query.
    for i,e in enumerate(path):
        u,v = e.upper(),str(i)
        edges[u],edges[v] = (i,5+i),(5+i,i+1)
        marks[e] = (e,u+v)
    model = Movies(Presentation(edges,marks,[]),path)
    sorts = []
    pending = [(initial,[])]
    while pending:
        h,actions = pending.pop()
        successors = [(s,actions+[('swap',j)]) for j in range(len(h)-1)
                      if (s:=model.swap(h,j,True)) is not None]
        if successors:
            pending.extend(successors)
        else:
            sorts.append(actions)
    assert len(sorts) == 16
    raw_positives = 0
    for first in sorts:
        # On this cube all positive readings are reduced words for reversal.
        # Calculate its directed word order independently of positioned events.
        initial_word = tuple(i for _,i in first)
        descendants = {initial_word}
        todo = [initial_word]
        while todo:
            word = todo.pop()
            for j,(x,y) in enumerate(zip(word,word[1:])):
                if abs(x-y)>1:
                    out = word[:j]+(y,x)+word[j+2:]
                elif word[j:j+3] == (x,x+1,x):
                    out = word[:j]+(x+1,x,x+1)+word[j+3:]
                else:
                    continue
                if out not in descendants:
                    descendants.add(out)
                    todo.append(out)
        for second in sorts:
            assert model.compare(initial,first,second)['surface']
            expected = tuple(i for _,i in second) in descendants
            assert raw_compare(model,initial,first,second)['raw'] == expected
            raw_positives += expected
    # Repeated occurrences of the same deletion have distinct spatial inputs.
    # The polygon and the spectator both leave an empty spatial path.
    deleting = Presentation({'f': (0,0)}, {'d': ('f',''), 'l': ('f','f')},
                            [Rule('f',((0,'d'),),((0,'l'),(0,'d')))])
    model = Movies(deleting,'fff')
    initial = ((2,'d'),(1,'d'),(0,'d'))
    movies = []
    for order in permutations(range(3)):
        ranks = {event:i for i,event in enumerate(order)}
        actions = sorting_steps([(ranks[e],e) for e in reversed(range(3))])
        _,history = model.parse(initial,actions)
        i = order.index(1)
        actions.append((0,i))
        after,_ = model.named(history,0,i)
        while True:
            step = next(((j,s) for j in range(len(after)-1)
                         if (s:=model.swap(after,j,True)) is not None), None)
            if step is None:
                break
            j,after = step
            actions.append(('swap',j))
        movies.append((actions,set(order[:i])))
    for first,src in movies:
        for second,dst in movies:
            assert model.compare(initial,first,second)['surface'] == (src <= dst)
    return dict(four_column_polygon_queries=comparisons, changing_path_cube_queries=len(sorts)**2,
                raw_cube_positives=raw_positives, empty_spatial_output_queries=len(movies)**2)


def mixed_port_checks():
    from semistrict_surface_raw_movie_graph import raw_compare
    marks = {'b': ('','f'), 'd': ('g',''), 'l': ('g','g')}
    split = Rule('g', ((0,'d'),), ((0,'l'),(0,'d')))
    edges = {'f': (0,0), 'g': (0,0)}
    initial = ((1,'b'),(0,'d'))
    early = [('swap',0),(0,0),('swap',1),('swap',0)]
    left = [('swap',0),('swap',0),(0,1)]
    right = [(0,1),('swap',0),('swap',1),('swap',1),('swap',0)]
    comparisons = 0
    for add_scalar in (False,True):
        if add_scalar:
            marks['z'] = ('','')
        model = Movies(Presentation(edges,marks,[split],{'z':0} if add_scalar else {}),'g')
        for i,a in enumerate((early,left,right)):
            for j,b in enumerate((early,left,right)):
                assert model.compare(initial,a,b)['surface'] == (i==0 or i==j)
                assert raw_compare(model,initial,a,b)['raw'] == (i==0 or i==j)
                comparisons += 1
        assert model.thin(initial)
    scalar = Rule('', ((0,'z'),), ((0,'z'),))
    model = Movies(Presentation(edges,marks,[scalar],{'z':0}),'')
    initial = ((0,'z'),(0,'z'))
    assert not model.thin(initial)
    assert model.compare(initial, [('swap',0),(0,0)], [(0,0)])['surface'] is False
    assert model.compare(initial, [(0,1)], [(0,0)])['surface'] is False
    return dict(mixed_empty_port_queries=comparisons, cyclic_connector_queries=2)


def guarded_checks():
    from itertools import product
    from semistrict_surface_raw_movie_graph import raw_compare
    ab = ((0,'a'),(1,'b'))
    ba = ab[::-1]
    presentation = Presentation({'f':(0,1),'g':(1,2)}, {'a':('f','f'),'b':('g','g')},
                                [Rule('fg',ab,ab),Rule('fg',ab,ab),Rule('fg',ab,ba)])
    def movie(word):
        return [(int(c),0) for c in word]
    checks = 0
    loose_positives = 0
    for transitions in [(('01','10'),('11','00')), (('','0'),), (('1',''),)]:
        tiles = [Attachment('fg',ba,[('swap',0)]+movie(l),[('swap',0)]+movie(r))
                 for l,r in transitions]
        model = Movies(presentation,'fg',tiles)
        bare = Movies(presentation,'fg',[Attachment('fg',ab,movie(l),movie(r)) for l,r in transitions])
        words = [''.join(w) for n in range(4) for w in product('01',repeat=n)]
        for start in words:
            reachable = {start}
            todo = [start]
            while todo:
                w = todo.pop()
                for l,r in transitions:
                    for i in range(len(w)-len(l)+1):
                        if w.startswith(l,i):
                            dest = w[:i]+r+w[i+len(l):]
                            if len(dest)<=3 and dest not in reachable:
                                reachable.add(dest)
                                todo.append(dest)
            for end in words:
                answer = model.compare(ab,movie(start),movie(end))['surface']
                assert answer == (end in reachable)
                assert raw_compare(model,ab,movie(start),movie(end))['raw'] == (start==end)
                assert raw_compare(bare,ab,movie(start),movie(end))['raw'] == (end in reachable)
                loose_positives += bool(answer and start!=end)
                checks += 1
    return dict(guarded_substring_queries=checks, guarded_surface_only=loose_positives)


def agda_guard(directory):
    from catt import arr, comp2, glue_tree, infer, maximal_vars, src, tgt, tree_ctx, v
    from emit_agda import Emitter
    from semistrict_surface_scalar_cube import exchange
    ctx = tree_ctx(glue_tree(1,0,1))
    def declare(s,t):
        nonlocal ctx
        assert infer(ctx,s)==infer(ctx,t)
        x = v(len(ctx))
        ctx += (arr(infer(ctx,s),s,t),)
        return x
    f,g = map(v,maximal_vars(ctx))
    a,b = declare(f,f),declare(g,g)
    j = exchange(ctx,a,b)
    base = tgt(ctx,j)
    declare(base,src(ctx,j))
    x,y = declare(base,base),declare(base,base)
    w,z = comp2(ctx,2,x,y),comp2(ctx,2,y,x)
    guarded = declare(comp2(ctx,2,j,w),comp2(ctx,2,j,z))
    emitter = Emitter()
    emitter.check_typed('guardedRule',ctx,guarded)
    emitter.check_type('oldSource',ctx,w,infer(ctx,z))
    emitter.check_type('oldTarget',ctx,z,infer(ctx,w))
    module = emitter.module('GuardedPolygonWord','One protected equal-length polygon rule.')
    (directory/'GuardedPolygonWord.agda').write_text(module.replace('open import CaTTExp.Pure',
                                                                     'open import CaTTExp.Gray.Pure'))


def checks():
    from semistrict_surface_raw_movie_graph import raw_compare
    edges={'f':(0,1),'u':(0,2),'v':(2,1),'g':(1,3),'h':(1,4),'k':(4,3)}
    marks={'a':('f','uv'),'x':('f','f'),'y':('f','uv'),
           'b':('g','hk'),'m':('g','g'),'n':('g','hk'),'T':('fg','uvg')}
    rules=[Rule('f',((0,'a'),),((0,'x'),(0,'y'))),
           Rule('g',((0,'b'),),((0,'m'),(0,'n'))),
           Rule('fg',((0,'T'),),((0,'a'),)),
           Rule('fg',((0,'a'),(2,'b')),((1,'b'),(0,'a'))),
           Rule('fg',((0,'a'),),((0,'x'),(0,'y')))]
    pres=Presentation(edges,marks,rules)
    model=Movies(pres,'fg')
    source=((1,'b'),(0,'a'))
    early=[('swap',0),(0,0)]
    late=[(0,1),('swap',0),('swap',1)]
    assert model.compare(source,early,late)['surface']
    assert not model.compare(source,late,early)['surface']
    long_start=((0,'T'),(2,'b'))
    gate=[(2,0),(3,0)]
    assert model.compare(long_start,gate+early,gate+late)['surface']
    assert not model.compare(long_start,gate+late,gate+early)['surface']
    # Same internal split as rule 0. Its declared spatial window includes m.
    overlap=((1,'m'),(0,'a'))
    long_early=[('swap',0),(4,0)]
    long_late=[(4,1),('swap',0),('swap',1)]
    assert not model.compare(overlap,long_early,long_late)['surface']
    assert not model.compare(overlap,long_late,long_early)['surface']
    assert model.compare(overlap,early,late)['surface']
    # Compare against the independent incidence solver inside the two-column subsystem.
    from semistrict_surface_joint_polygons import problem,solution
    from semistrict_surface_planar_cylinder import moves
    words=[('p',('a',),('x','y')),('q',('b',),('m','n')),('gate',('a','b'),('b','a'))]
    rr={'p':0,'q':1,'gate':3,'swap':'swap'}
    pairs=0
    state_count=0
    for original in ['ba','ab']:
        groups={}
        history=source if original=='ba' else ((0,'a'),(2,'b'))
        work=[(tuple(original),[],[],0)]
        while work:
            w,raw,trace,count=work.pop()
            groups.setdefault(w,[]).append((raw,trace))
            for n,i,l,r,out in moves(w,words,{'b','m','n'}):
                used=count+(n!='swap')
                if used<=3:
                    work.append((out,raw+[(rr[n],i)],trace+[(n,i,l,r)],used))
        for group in groups.values():
            for actions,path in group:
                for more,other in group:
                    data=problem(tuple(original),{'b','m','n'},(path,other),())
                    expected=data is not None and solution(data) is not None
                    answer=model.compare(history,actions,more)
                    assert answer['surface']==expected
                    assert raw_compare(model,history,actions,more)['raw']==expected
                    pairs+=1
                    state_count+=answer['states']
    return dict(comparisons=pairs,visited_descriptions=state_count,changing_spatial_queries=7,
                **wider_checks(), **mixed_port_checks(), **guarded_checks())


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    parser.add_argument('--agda-dir',type=Path)
    parser.add_argument('--raw',action='store_true',help='also decide the directed comparison on a query')
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        rules=[Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target']))) for r in q['rules']]
        pres=Presentation(q['edges'],q['marks'],rules,q.get('mark_roots'))
        source=tuple(map(tuple,q['source']))
        pres.walk(q['start'],source,q.get('vertex'))
        tiles=[Attachment(r['path'],tuple(map(tuple,r['source'])),r['first'],r['second'])
               for r in q.get('attachments',[])]
        model=Movies(pres,q['start'],tiles)
        result=model.compare(source,q['first'],q['second'])
        if args.raw:
            from semistrict_surface_raw_movie_graph import raw_compare
            result.update(raw_compare(model,source,q['first'],q['second']))
    else:
        result=checks()
    if args.agda_dir:
        agda_guard(args.agda_dir)
    print(json.dumps(result))
