"""Directed degree-four search on literal positive movies with count-monotone attachments."""
from collections import deque


def read(model, source, actions):
    histories = [source]
    windows = []
    for name, index in actions:
        h = histories[-1]
        if name == 'swap':
            out = model.swap(h,index,True)
            if out is None:
                raise ValueError('expected a native positive swap')
            windows.append((2,2))
        else:
            rule = model.pres.rules[name]
            out,_ = model.named(h,name,index)
            windows.append((len(rule.source),len(rule.target)))
        histories.append(out)
    return histories,windows


def steps(indices):
    return tuple(('swap',j) for j in indices)


def raw_updates(model, actions, histories, windows, limit):
    for k,(name,i) in enumerate(actions):
        left,right = windows[k]
        if k+1 < len(actions):
            other,j = actions[k+1]
            before,after = windows[k+1]
            if j+before <= i:
                pair = ((other,j),(name,i+after-before))
                yield actions[:k]+pair+actions[k+2:]
            elif j >= i+right:
                pair = ((other,j+left-right),(name,i))
                yield actions[:k]+pair+actions[k+2:]
        if name == 'swap':
            if actions[k:k+3] == steps((i,i+1,i)):
                yield actions[:k]+steps((i+1,i,i+1))+actions[k+3:]
            continue
        h = histories[k]
        if i+left == len(h):
            continue
        pos,event = h[i+left]
        _,off = model.named(h,name,i)
        if pos >= off+len(model.patch_ends[name]):
            # A left polygon has input crossings on the negative prism face.
            if k >= left and actions[k-left:k] == steps(range(i,i+left)):
                replacement = ((name,i+1),)+steps(range(i,i+right))
                yield actions[:k-left]+replacement+actions[k+1:]
        if pos+len(model.pres.marks[event][0]) <= off:
            # A right polygon has output crossings on the negative prism face.
            if actions[k+1:k+1+right] == steps(reversed(range(i,i+right))):
                replacement = steps(reversed(range(i,i+left)))+((name,i+1),)
                yield actions[:k]+replacement+actions[k+1+right:]

    count = sum(n!='swap' for n,_ in actions)
    for tile,old_count in model.attachments:
        if count-old_count+sum(n!='swap' for n,_ in tile.second) > limit:
            continue
        for k,h in enumerate(histories):
            paths = model.pres.walk(model.start,h)
            for i in range(len(h)-len(tile.source)+1):
                off = h[i][0]-tile.source[0][0]
                if off<0 or not paths[i].startswith(tile.path,off):
                    continue
                if h[i:i+len(tile.source)] != tuple((j+off,n) for j,n in tile.source):
                    continue
                lhs = tuple((n,i+j) for n,j in tile.first)
                if actions[k:k+len(lhs)] == lhs:
                    rhs = tuple((n,i+j) for n,j in tile.second)
                    yield actions[:k]+rhs+actions[k+len(lhs):]


def raw_compare(model, source, first, second):
    first,second = tuple(map(tuple,first)),tuple(map(tuple,second))
    model.pres.walk(model.start,source)
    u,end = model.parse(source,first)
    v,other = model.parse(source,second)
    if end != other:
        raise ValueError('expected parallel old readings')
    from semistrict_surface_two_slot_polygons import compare as two_slot_compare, width_at_most_two
    if not model.attachments and any(width_at_most_two(model,source,r) for r in (u,v)):
        return two_slot_compare(model,source,first,second,u,v,False)
    grades = {}
    if not model.attachments:
        from semistrict_surface_polygon_grades import bound
        grades = bound(model,source,first,second)
        if grades is None:
            return dict(raw=False,raw_states=0)
    limit = max(sum(n!='swap' for n,_ in face) for face in (first,second))
    seen = {first}
    todo = deque(seen)
    cyclic = False
    while todo:
        word = todo.popleft()
        if word == second:
            return dict(raw=True, raw_states=len(seen),**grades)
        histories,windows = read(model,source,word)
        if model.attachments and not all(model.thin(h) for h in histories):
            cyclic = True
            continue
        for nxt in raw_updates(model,word,histories,windows,limit):
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return dict(raw=None if cyclic else False, raw_states=len(seen),**grades)
