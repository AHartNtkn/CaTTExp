"""Compute finite or infinite ranges of a projected prefix product at a named polygon."""
from collections import deque
from functools import lru_cache
from itertools import combinations

from semistrict_surface_component_braids import cabling
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_meridian_transport import prod
from semistrict_surface_phase_gains import substitute
from semistrict_surface_shared_edge import braid_image


def wire_units(calc):
    """The ordered initial unit names carried by each named temporal event."""
    units = {}
    pos = 0
    for _,e in calc.root:
        units[e] = tuple(range(pos,pos+calc.flow[e]))
        pos += calc.flow[e]
    for rule in calc.model.pres.rules:
        packet = [unit for _,e in rule.source for unit in units[e]]
        pos = 0
        for _,e in rule.target:
            units[e] = tuple(packet[pos:pos+calc.flow[e]])
            pos += calc.flow[e]
        assert pos == len(packet)
    return units


def separated_sites(calc,selected):
    """Finite covering list at spatially ordered permanent sites; None if inapplicable."""
    marks = calc.model.pres.marks
    if any(len(s)!=len(t) for s,t in marks.values()):
        return None
    used = {e for rule in calc.model.pres.rules for _,e in rule.source}
    units = wire_units(calc)
    sites = []
    for position,e in calc.root:
        if selected.intersection(units[e]):
            if e in used or len(units[e])!=1:
                return None
            sites.append((position,len(marks[e][0])))
    if len(sites)!=len(selected):
        return None
    empty = [pos for pos,size in sites if size==0]
    if len(set(empty))<len(empty):
        return None
    def sort_word(order):
        current = list(order)
        word = []
        for dest,name in enumerate(sorted(order,key=lambda k:(sites[k],k))):
            src = current.index(name)
            word.extend(range(src,dest,-1))
            current.insert(dest,current.pop(src))
        return tuple(word)
    start = tuple(range(len(sites)))
    initial = sort_word(start)
    return [(reduced(initial+inv(sort_word(chosen+tuple(k for k in start if k not in chosen)))),length)
            for length in range(len(sites)+1) for chosen in combinations(start,length)]


def prefix_values(calc, owner, selected, mandatory=frozenset(), allowed=None):
    """Return product -> (actual projected braid, split), or None for an infinite range.

    selected, mandatory and allowed contain zero-based units of the initial history.
    The latter two bounds constrain the full before-set at the polygon.
    """
    n = len(selected)
    units = wire_units(calc)
    counts = {e:sum(i in selected for i in bundle) for e,bundle in units.items()}
    rules = calc.model.pres.rules
    contacts = [r.source[0][1] for r in rules]
    known = {}

    @lru_cache(maxsize=2048)
    def frame(braid):
        return braid_image(n,braid)

    def word_at(braid,split):
        return prod(*frame(braid)[:split])

    def transform(values,prefix):
        if values is None or not prefix:
            return values
        return {substitute(frame(prefix),v):(reduced(prefix+path),split)
                for v,(path,split) in values.items()}

    def component(mask,entry):
        key = mask,entry
        if key in known:
            value,pre = known[key]
            return transform(value,inv(pre))
        paths = {entry:()}
        queue = deque([entry])
        loops, exits, values = set(),[],{}
        while queue:
            h = queue.popleft()
            path = paths[h]
            face,off = [],0
            for _,e in h:
                size = counts[e]
                face.append((e,off,off+size))
                off += size
            for i in range(len(h)-1):
                for sign in (1,-1):
                    nxt = calc.model.swap(h,i,sign>0)
                    if nxt is None:
                        continue
                    step = cabling(face,(sign*(i+1),))
                    visit = reduced(path+step)
                    if nxt not in paths:
                        paths[nxt] = visit
                        queue.append(nxt)
                    else:
                        loop = reduced(visit+inv(paths[nxt]))
                        if loop:
                            loops.add(loop)
            positions = {e:i for i,(_,e) in enumerate(h)}
            for p,first in enumerate(contacts):
                if mask & (1<<p) or first not in positions:
                    continue
                i = positions[first]
                placement = calc.model.named(h,p,i)
                if placement is None:
                    continue
                if p==owner:
                    before = {u for _,e in h[:i] for u in units[e]}
                    if mandatory<=before and (allowed is None or before<=allowed):
                        split = face[i][1]
                        values[word_at(path,split)] = path,split
                else:
                    exits.append((mask|(1<<p),placement[0],path))
        for next_mask,h,path in exits:
            child = component(next_mask,h)
            if child is None:
                values = None
                break
            values.update(transform(child,path))
        if values and any(substitute(frame(loop),v)!=v for loop in loops for v in values):
            values = None
        for h,path in paths.items():
            known[mask,h] = values,path
        return values

    return component(0,calc.root)


def checks():
    from semistrict_surface_polygon_grades import resolution
    from semistrict_surface_signed_meetings import Signed
    from semistrict_surface_signed_width_two import Movies,Presentation,Rule

    # A distinct site gives a unique signed braid for each final permutation.
    # At a coincident site the whole braid may wind even where the observed
    # partial product is forced to be constant.
    for together in (False,True):
        s = ((0,'s'),)
        model = Movies(Presentation({'f':(0,0)},{'s':('','')},[Rule('',s,s)],{'s':0}),'ff')
        root = ((2,'s'),(0,'s'),(0 if together else 1,'s'))
        face = ((0,0),)
        data = resolution(root,(face,face),[(1,1)],'swap')
        calc = Signed(model,root,data)
        units = wire_units(calc)
        names = frozenset(units[(-1,1)]+units[(-1,2)])
        result = prefix_values(calc,0,names)
        assert (result is None)==together
        assert set(prefix_values(calc,0,names,allowed=frozenset()))=={()}
        assert set(prefix_values(calc,0,names,mandatory=names))=={(1,2)}
        if not together:
            assert len(result)==4
            simple = separated_sites(calc,names)
            expected = {prod(*braid_image(2,w)[:k]) for w,k in simple}
            assert set(result)==expected
        else:
            assert separated_sites(calc,names) is None

    # The marked event is born at a genuine two-output polygon. At its
    # later update the two observed source units might now be at different
    # live events. Project every swap with its actual two cable sizes.
    model = Movies(Presentation({'f':(0,0)},{'a':('',''),'b':('','f'),'d':('f',''),'s':('','')},
                    [Rule('',((0,'a'),),((0,'b'),(0,'d'))),
                     Rule('f',((0,'b'),(0,'d'),(1,'s')),((0,'b'),(0,'d'),(1,'s')))],
                    {'a':0,'b':0,'s':0}),'f')
    root = ((0,'a'),(1,'s'),(1,'s'))
    face = ((0,0),(1,0))
    data = resolution(root,(face,face),[(1,2),(3,3)],'swap')
    calc = Signed(model,root,data)
    selected = frozenset(range(calc.width))
    values = prefix_values(calc,1,selected,allowed=frozenset())
    assert set(values)=={()} and separated_sites(calc,selected) is None
    print('Separated and coincident spectators, constant cuts under infinite winding, '
          'and an arity-changing polygon with a later update passed')


if __name__=='__main__':
    checks()
