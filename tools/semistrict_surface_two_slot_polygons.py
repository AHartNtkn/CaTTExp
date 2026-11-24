"""Compare positive polygon movies with at most two live temporal events, retaining signed winding."""
from collections import deque


def width_at_most_two(model,source,records):
    return len(source)<=2 and all(len(h)<=2 and
        len(h)-len(model.pres.rules[n].source)+len(model.pres.rules[n].target)<=2
        for h,n,_ in records)


def checkpoints(records,actions):
    total = 0
    row = iter(records)
    data = []
    for n,_ in actions:
        if n=='swap':
            total += 1
        else:
            data.append((*next(row),total))
    return tuple(data),total


def neighbours(model,state,total,signed):
    for k,(h,n,i,height) in enumerate(state):
        rule = model.pres.rules[n]
        out,off = model.named(h,n,i)
        if len(h)==2 and i==0 and len(rule.source)==len(rule.target)==1:
            pos,event = h[1]
            source = model.pres.marks[event][0]
            for sign,apart in ((1,pos+len(source)<=off),(-1,pos>=off+len(model.patch_ends[n]))):
                target = height+sign
                if not apart:
                    continue
                if not signed and not ((state[k-1][3] if k else 0)<=target<=
                                       (state[k+1][3] if k+1<len(state) else total)):
                    continue
                after = model.swap(h,0,sign==1)
                assert after is not None and model.named(after,n,1) is not None
                yield state[:k]+((after,n,1,target),)+state[k+1:],('prism',k,sign)
        if k+1>=len(state):
            continue
        before,m,j,next_height = state[k+1]
        other = model.pres.rules[m]
        if i==j or height!=next_height or out!=before:
            continue
        if len(rule.source)!=1 or len(rule.target)!=1 or len(other.source)!=1 or len(other.target)!=1:
            continue
        middle,_ = model.named(h,m,j)
        assert model.named(middle,n,i)[0]==model.named(out,m,j)[0]
        yield state[:k]+((h,m,j,height),(middle,n,i,height))+state[k+2:],('commute',k)


def search_checkpoints(model,source,first,second,u,v,signed):
    key = 'surface' if signed else 'raw'
    size = 'states' if signed else 'raw_states'
    if not width_at_most_two(model,source,v):
        return {key:False,size:0}
    start,total = checkpoints(u,first)
    end,other = checkpoints(v,second)
    if total!=other:
        return {key:False,size:0}
    seen = {start:None}
    queue = deque([start])
    while queue:
        current = queue.popleft()
        if current==end:
            path = []
            while seen[current] is not None:
                current,step = seen[current]
                path.append(step)
            return {key:True,size:len(seen),key+'_steps':path[::-1]}
        for nxt,step in neighbours(model,current,total,signed):
            if nxt not in seen:
                seen[nxt] = current,step
                queue.append(nxt)
    return {key:False,size:len(seen)}


def segments(model,source,actions):
    """Read the ordered changes on each strand between whole-history polygons."""
    blocks = []
    barriers = []
    h = source
    def new():
        return [[],[]],[],[],list(range(len(h)))
    rows,crossings,keys,live = new()
    for name,i in actions:
        if name=='swap':
            keys.append(('cross',len(crossings)))
            crossings.append((h,tuple(map(len,rows))))
            h = model.swap(h,i,True)
            live.reverse()
            continue
        r = model.pres.rules[name]
        out,_ = model.named(h,name,i)
        if len(r.source)==len(r.target)==1:
            strand = live[i]
            keys.append(('mark',strand,len(rows[strand])))
            rows[strand].append(name)
            h = out
        else:
            blocks.append((rows,crossings,keys))
            barriers.append((h,name,i))
            h = out
            rows,crossings,keys,live = new()
    return blocks+[(rows,crossings,keys)],barriers


def advance_crossing(model,h,rid,forward):
    rule = model.pres.rules[rid]
    crossed = model.swap(h,0,True)
    if forward:
        # Undo the last update on the earlier strand, then cross its input.
        pos,event = h[0]
        off = pos-rule.target[0][0]
        if event!=rule.target[0][1] or off<0 or not model.start.startswith(rule.path,off):
            return None
        h0 = ((off+rule.source[0][0],rule.source[0][1]),h[1])
        if h[1][0]+len(model.pres.marks[h[1][1]][0])>off:
            return None
        crossing = model.swap(h0,0,True)
        if crossing is None:
            return None
        after = model.named(crossing,rid,1)
        return h0 if after is not None and after[0]==crossed else None
    # Move the first update after the crossing onto its later input strand.
    end = model.named(crossed,rid,0)
    if end is None or crossed[1][0]<end[1]+len(model.patch_ends[rid]):
        return None
    before = model.named(h,rid,1)
    if before is not None and model.swap(before[0],0,True)==end[0]:
        return before[0]
    return None


def crossing_path(model,rows,c,first,last):
    old,low = first
    end,high = last
    a,b = c%2,1-c%2
    start = low[a],low[b],old
    target = high[a],high[b],end
    seen = {start:None}
    queue = deque([start])
    while queue:
        state = queue.popleft()
        i,j,h = state
        if state==target:
            path = []
            while seen[state] is not None:
                state,mark,sign = seen[state]
                path.append((mark,sign))
            return path[::-1],len(seen)
        if i>high[a]:
            out = advance_crossing(model,h,rows[a][i-1],True)
            nxt = i-1,j,out
            if out is not None and nxt not in seen:
                seen[nxt] = state,('mark',a,i-1),1
                queue.append(nxt)
        if j<high[b]:
            out = advance_crossing(model,h,rows[b][j],False)
            nxt = i,j+1,out
            if out is not None and nxt not in seen:
                seen[nxt] = state,('mark',b,j),-1
                queue.append(nxt)
    return None,len(seen)


def raw_schedule(model,source,first,second,u,v):
    if not width_at_most_two(model,source,u) or not width_at_most_two(model,source,v):
        return None,0
    blocks,barriers = segments(model,source,first)
    ends,others = segments(model,source,second)
    if barriers!=others:
        return None,0
    actions = []
    size = offset = 0
    for (rows,crossings,keys),(target,final,wanted) in zip(blocks,ends):
        if rows!=target or len(crossings)!=len(final):
            return None,size
        def gaps(reading):
            count = 0
            result = {}
            for key in reading:
                if key[0]=='cross':
                    count += 1
                else:
                    result[key] = count
            return result
        target_gaps = gaps(wanted)
        for mark,g in gaps(keys).items():
            diff = target_gaps[mark]-g
            if diff and (abs(diff)!=1 or mark[1]!=g%2):
                return None,size
        def commute(j):
            x,y = keys[j:j+2]
            assert x[0]==y[0]=='mark' and x[1]!=y[1],(first,second,keys,j)
            keys[j:j+2] = y,x
            actions.append(('commute',offset+j))
        for c,(left,right) in enumerate(zip(crossings,final)):
            path,visits = crossing_path(model,rows,c,left,right)
            size += visits
            if path is None:
                return None,size
            for mark,sign in path:
                i,j = keys.index(mark),keys.index(('cross',c))
                if sign==1:
                    assert i<j
                    for k in range(i,j-1):
                        commute(k)
                    slot = j-1
                else:
                    assert j<i
                    for k in reversed(range(j+1,i)):
                        commute(k)
                    slot = j
                keys[slot:slot+2] = keys[slot:slot+2][::-1]
                actions.append(('prism',offset+slot,sign))
        for i,key in enumerate(wanted):
            for k in reversed(range(i,keys.index(key))):
                commute(k)
        offset += len(keys)+1
    return actions,size


def compare(model,source,first,second,u,v,signed):
    schedule,size = raw_schedule(model,source,first,second,u,v)
    key = 'surface' if signed else 'raw'
    return {key:schedule is not None,'states' if signed else 'raw_states':size,'raw_steps':schedule}


def checks():
    from collections import defaultdict
    from random import Random
    from semistrict_surface_raw_movie_graph import raw_updates, read
    from semistrict_surface_signed_width_two import Movies,Presentation,Rule
    edges = {'f':(0,0)}
    marks = {'a':('',''),'b':('','')}
    single = ((0,'a'),)
    rules = [Rule('',single,single),
             Rule('ff',((0,'a'),),((1,'a'),)),Rule('ff',((1,'a'),),((2,'a'),)),
             Rule('f',((1,'a'),),((0,'b'),)),Rule('',((0,'b'),),single),
             Rule('ff',((0,'a'),(1,'a')),((2,'a'),(0,'a'))),
             Rule('',single,single*2),Rule('',single*2,single)]
    model = Movies(Presentation(edges,marks,rules,dict.fromkeys(marks,0)),'ff')
    rng = Random(220)
    tested = accepted = signed_states = certified_steps = changing = 0
    for initial in [((1,'a'),)*2,((2,'a'),(0,'a')),single]:
        groups = defaultdict(list)
        todo = [(initial,(),0,0)]
        while todo:
            h,word,n,c = todo.pop()
            tags = tuple(sorted(r for r,_ in word if r!='swap'))
            groups[h,tags,c].append(word)
            for i in range(len(h)):
                if c<3:
                    out = model.swap(h,i,True)
                    if out is not None:
                        todo.append((out,word+(('swap',i),),n,c+1))
                if n<3:
                    for rid in range(len(rules)):
                        step = model.named(h,rid,i)
                        if step is not None and len(step[0])<=2:
                            todo.append((step[0],word+((rid,i),),n+1,c))
        for (_,names,_),group in groups.items():
            if len(group)<2:
                continue
            for first in rng.sample(group,min(3,len(group))):
                literal = {first}
                todo = [first]
                while todo:
                    w = todo.pop()
                    histories,windows = read(model,initial,w)
                    for z in raw_updates(model,w,histories,windows,len(names)):
                        if z not in literal:
                            literal.add(z)
                            todo.append(z)
                u,_ = model.parse(initial,first)
                for second in rng.sample(group,min(3,len(group))):
                    v,_ = model.parse(initial,second)
                    path,_ = raw_schedule(model,initial,first,second,u,v)
                    signed = search_checkpoints(model,initial,first,second,u,v,True)
                    assert (path is not None)==signed['surface']==(second in literal)
                    if path is not None:
                        current = list(first)
                        for kind,i,*arg in path:
                            hist,win = read(model,initial,current)
                            before = tuple(current)
                            l,r = current[i:i+2]
                            if kind=='commute':
                                current[i:i+2] = r,l
                            elif arg==[1]:
                                current[i:i+2] = r,(l[0],1)
                            else:
                                current[i:i+2] = (r[0],1),l
                            assert tuple(current) in raw_updates(model,before,hist,win,len(names))
                        assert tuple(current)==second
                        certified_steps += len(path)
                        accepted += 1
                    changing += any(r in (6,7) for r in names)
                    tested += 1
                    signed_states += signed['states']
    return dict(comparisons=tested,positive=accepted,checkpoint_states=signed_states,
                replayed_raw_steps=certified_steps,arity_changing_queries=changing)


if __name__=='__main__':
    import json
    print(json.dumps(checks()))
