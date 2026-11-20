"""Compute pi_1 presentations at three-cell labels from raw typed 2- and 3-rules."""

from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, permutations, product

from fibration_factor_search import Rule, Stage
from fibration_weak_joints import edge_presentation


def unary_signature(stage, label, marker, marker_rule, path):
    """Use the same distinguished slot name in every serialization of a unary chart."""
    rules = {('old', g):r for g,r in stage.rules.items()}
    rules['slot', label] = marker_rule
    typed = Stage(stage.arrows,rules)
    initial = tuple((('slot',label) if g == marker else ('old',g), i) for g,i in path)
    seen, todo = {initial}, [initial]
    while todo:
        for p in typed.exchanges(todo.pop()):
            if p not in seen:
                seen.add(p)
                todo.append(p)
    return tuple((kind,g,i) for (kind,g),i in min(seen))


def comparison_groups(stage, disks, vertex, word, start, end, events):
    """Return the serial writings and group of each component at the given poles/counts.

    A serial writing is a tuple of unary marked 2-contexts. Each entry retains its
    concrete marker position. The computation assumes a bubble-free 3-presentation.
    """
    final, = {tuple(stage.slices(vertex, word, p))[-1] for p in (start, end)}
    tagged = tuple(f'@{i}' for i in range(len(events)))
    assert set(tagged).isdisjoint(stage.rules)
    rules = dict(stage.rules)
    faces = {}
    for m, label in zip(tagged, events):
        v, w, s, t = disks[label]
        out, = {tuple(stage.slices(v, w, p))[-1] for p in (s,t)}
        rules[m] = Rule(v, w, out)
        faces[m] = (s,t)
    marked = Stage(stage.arrows, rules)
    ordinary_bound = len(start) + sum(max(0, len(t)-len(s)) for s,t in faces.values())
    ordinary_counts = Counter(g for g, _ in start)
    for s, t in faces.values():
        ordinary_counts.update(Counter(g for g, _ in t) - Counter(g for g, _ in s))
    nonshrinking = all(len(r.source) <= len(r.target) for r in rules.values())

    representatives = {}

    def canonical(p):
        if p not in representatives:
            orbit, todo = {p}, [p]
            while todo:
                for alt in marked.exchanges(todo.pop()):
                    if alt not in orbit:
                        orbit.add(alt)
                        todo.append(alt)
            best = min(orbit)
            representatives.update(dict.fromkeys(orbit, best))
        return representatives[p]

    def substitute(p, change):
        out = []
        for g, i in p:
            if g in change:
                out.extend((h, i+j) for h, j in faces[g][change[g]])
            else:
                out.append((g,i))
        return canonical(tuple(out))

    charts = {}
    visited = set()
    todo = [(word, (), frozenset(), 0)]
    while todo:
        w, path, used, old = todo.pop()
        p = canonical(path)
        if p in visited:
            continue
        visited.add(p)
        if w == final and used:
            charts[p] = used
        counts = Counter(g for g, _ in p if g not in faces)
        for g, r in rules.items():
            if g not in faces and counts[g] >= ordinary_counts[g]:
                continue
            if g in used or (g not in faces and old == ordinary_bound):
                continue
            if nonshrinking and len(w)+len(r.target)-len(r.source) > len(final):
                continue
            for i in marked.sites(vertex, w, r.source, r.vertex):
                after = w[:i]+r.target+w[i+len(r.source):]
                todo.append((after, p+((g,i),), used|{g} if g in faces else used,
                             old+int(g not in faces)))

    paths = sorted(charts)
    ids = {p:i for i,p in enumerate(paths)}
    by_source = defaultdict(list)
    for i, p in enumerate(paths):
        slots = charts[p]
        a = substitute(p, dict.fromkeys(slots, 0))
        b = substitute(p, dict.fromkeys(slots, 1))
        by_source[a].append((i,slots,b))
    strings = set()
    todo = [((), frozenset(), canonical(start))]
    while todo:
        seq, used, current = todo.pop()
        if len(used) == len(events):
            if current == canonical(end):
                strings.add(seq)
            continue
        for i, slots, b in by_source[current]:
            if not slots & used:
                todo.append((seq+(i,), used|slots, b))

    @cache
    def refinements(seq):
        descendants = set()
        for j, i in enumerate(seq):
            p = paths[i]
            slots = charts[p]
            for n in range(1, len(slots)):
                for early in combinations(sorted(slots), n):
                    a = substitute(p, dict.fromkeys(slots.difference(early), 0))
                    b = substitute(p, dict.fromkeys(early, 1))
                    refined = seq[:j]+(ids[a],ids[b])+seq[j+1:]
                    assert refined in strings
                    descendants.add(refined)
                    descendants.update(refinements(refined))
        return descendants

    # Remove temporary occurrence names by taking orbits of flags, preserving
    # different edge/triangle incidences that can share all their vertex orbits.
    families = defaultdict(list)
    for m,g in zip(tagged, events):
        families[g].append(m)
    groups = tuple(families.values())
    actions = []
    for perm in product(*(permutations(family) for family in groups)):
        rename = {m:h for family, image in zip(groups,perm) for m,h in zip(family,image)}
        action = [ids[canonical(tuple((rename.get(g,g),i) for g,i in p))] for p in paths]
        actions.append(action)

    @cache
    def orbit(*flag):
        return min(tuple(tuple(action[i] for i in seq) for seq in flag) for action in actions)

    vertices = {orbit(x)[0] for x in strings}
    edges, triangles = {}, set()
    for x in vertices:
        for y in refinements(x):
            e = orbit(x,y)
            edges[e] = (x,orbit(y)[0])
            for z in refinements(y):
                triangles.add((e,orbit(y,z),orbit(x,z)))

    neighbors = defaultdict(set)
    for a,b in edges.values():
        neighbors[a].add(b)
        neighbors[b].add(a)
    names = dict(zip(tagged, events))

    @cache
    def signature(c):
        marker, = charts[paths[c]]
        return unary_signature(stage,names[marker],marker,rules[marker],paths[c])

    result = []
    while vertices:
        component = {min(vertices)}
        todo = list(component)
        while todo:
            for v in neighbors[todo.pop()]:
                if v not in component:
                    component.add(v)
                    todo.append(v)
        vertices -= component
        e = {key: ends for key,ends in sorted(edges.items()) if ends[0] in component}
        t = [tri for tri in sorted(triangles) if tri[0] in e]
        gs, rs, _ = edge_presentation(sorted(component),e,t)
        serial = set()
        for seq in component:
            if len(seq) == len(events):
                serial.add(tuple(signature(c) for c in seq))
        result.append((serial, gs, rs, (len(component),len(e),len(t))))
    return result


def example(name, stage, disks, word, start, end, labels, ranks):
    groups = comparison_groups(stage,disks,'x',word,start,end,labels)
    assert all(not rels for _,_,rels,_ in groups)
    assert sorted(len(gs) for _,gs,_,_ in groups) == ranks
    print(name, [(len(w),len(g),size) for w,g,_,size in groups])


def main():
    stage = Stage({c:('x','x') for c in 'gt'}, {n:Rule('x',s,t) for n,s,t in
                  [('u','','t'),('h','','g'),('c','gt','tg')]})
    disks = {'D': ('x','t',(('h',1),),(('h',0),('c',0))),
             'M': ('x','g',(('u',1),('c',0)),(('u',0),))}
    a = (('u',0),('h',1))
    example('Nullary Gray circuit',stage,disks,'',a,a,'DMDM',[0])

    rules = {g:Rule('x',s,t) for g,s,t in
             [('a','f','F'),('b','f','F'),('p','h','H'),('q','h','H')]}
    stage = Stage({c:('x','x') for c in 'fFghH'}, rules)
    start, end = (('a',0),('p',2)), (('b',0),('q',2))
    wide = {'A': ('x','fg',(('a',0),),(('b',0),)), 'B': ('x','gh',(('p',1),),(('q',1),))}
    example('Overlapping idle wire',stage,wide,'fgh',start,end,'AB',[1])
    narrow = {**wide,'A':('x','f',(('a',0),),(('b',0),))}
    example('Disjoint changes',stage,narrow,'fgh',start,end,'AB',[0])

    # A doubly suspended two-loop graph is an admissible fibre at a point.
    # Both changes act on the same generating gate; they cannot be a joint tier.
    loops = {g: ('x','f',(('a',0),),(('a',0),)) for g in 'AB'}
    example('Two strict labels at one boundary',stage,loops,'f',(('a',0),),(('a',0),),'AB',[0,0])

    # Three occurrences of a single generator. The strict 2-poles fix one change
    # on each ordered wire. All six serializations bound the full permutohedron.
    stage = Stage({'f':('x','x'),'F':('x','x')}, {g:Rule('x','f','F') for g in 'ab'})
    disks = {'A':('x','f',(('a',0),),(('b',0),))}
    example('Repeated independent changes',stage,disks,'fff',tuple(('a',i) for i in range(3)),
            tuple(('b',i) for i in range(3)),'AAA',[0])


if __name__ == '__main__':
    main()
