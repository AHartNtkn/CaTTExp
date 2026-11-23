"""Comparison solver on an unrolled globular Gray interval with triangle-free crossings."""
import argparse
from collections import Counter
from itertools import combinations, permutations, product
from semistrict_surface_two_column_tiers import filling


def interval(start, end, columns):
    if len(set(start)) != len(start) or sorted(start) != sorted(end):
        raise ValueError('temporal endpoints must order the same distinct event slots')
    edges = set()
    for a, b in combinations(start, 2):
        if end.index(b) < end.index(a):
            if columns[b] >= columns[a]:
                raise ValueError('these shuffles admit no positive movie')
            edges.add((b, a))
    triangle = any(len({a,b,c}) == 3 and (a,c) in edges
                   for a,b in edges for x,c in edges if x == b)
    if triangle:
        raise ValueError('a triple of required crossings lies outside this test')
    pads = {}
    for a,b in edges:
        vertices = Counter()
        for x in start:
            if columns[x] in (columns[a], columns[b]):
                continue
            ref = b if (x,a) in edges or (a,x) in edges else a
            if start.index(x) < start.index(ref):
                vertices[columns[x]] += 1
        pads[a,b] = tuple(vertices.get(i, 0) for i in range(max(columns.values())+1)
                          if i not in (columns[a], columns[b]))
    return pads


def triangle_facets(start, end, marked):
    """Isolate the chosen reversed triple and return both legal cube-facet readings."""
    rank = {a:i for i,a in enumerate(end)}
    a,b,c = marked
    i,j,k = (start.index(x) for x in marked)
    if not (i < j < k and rank[a] > rank[b] > rank[c]):
        raise ValueError('marked slots must form a reversed triple')
    between = [x for x in start[i:k+1] if x not in marked]
    low = tuple(x for x in between if rank[x] < rank[b])
    high = tuple(x for x in between if rank[x] > rank[b])
    isolated = start[:i]+low+marked+high+start[k+1:]

    def reorder(order, desired):
        steps = []
        for pos,x in enumerate(desired):
            idx = order.index(x)
            while idx > pos:
                assert rank[order[idx-1]] > rank[x]
                steps.append(idx-1)
                order[idx], order[idx-1] = order[idx-1], x
                idx -= 1
        return steps

    prefix = reorder(list(start), isolated)
    offset = i+len(low)
    after = start[:i]+low+marked[::-1]+high+start[k+1:]
    suffix = reorder(list(after), end)
    return tuple(prefix+[offset+t for t in braid]+suffix
                 for braid in ((0,1,0),(1,0,1)))


def readings(start, end, columns, updates):
    goal = {x:i for i,x in enumerate(end)}

    def visit(order, done, word):
        if order == end and done == updates:
            yield word
        for a, n in enumerate(done):
            if n < updates[a]:
                nxt = done[:a]+(n+1,)+done[a+1:]
                yield from visit(order, nxt, word+(('U',a,n),))
        for i,(b,a) in enumerate(zip(order, order[1:])):
            if columns[b] > columns[a] and goal[a] < goal[b]:
                nxt = order[:i]+(a,b)+order[i+2:]
                yield from visit(nxt, done, word+(('C',a,b),))
    yield from visit(start, (0,)*len(updates), ())


def moved(token):
    return set(token[1:] if token[0] == 'C' else token[1:2])


def exchange(u, v):
    if moved(u).isdisjoint(moved(v)):
        return True
    if u[0] == 'C' and v[0] == 'U':
        return u[1] == v[1]
    if u[0] == 'U' and v[0] == 'C':
        return u[1] == v[2]
    return False


def comparison(word, target):
    """For legal readings of the two faces, construct the positive adjacent moves."""
    if Counter(word) != Counter(target):
        return None
    w = list(word)
    certificate = []
    for j,v in enumerate(target):
        i = w.index(v, j)
        while j < i:
            if not exchange(w[i-1], v):
                return None
            certificate.append(i-1)
            w[i], w[i-1] = w[i-1], v
            i -= 1
    return certificate


def observations(start, word, columns, pads):
    order = list(start)
    bits = set()
    for token in word:
        kind,a,b = token
        if kind == 'U':
            bits.update((token,x) for x in order[:order.index(a)])
        else:
            j = order.index(b)
            assert order[j+1] == a
            other = [i for i in range(max(columns.values())+1) if i not in (columns[a],columns[b])]
            assert pads[a,b] == tuple(sum(columns[x] == i for x in order[:j]) for i in other)
            order[j:j+2] = [a,b]
    return frozenset(bits)


def top_filling(pads, updates, difference):
    """Sparse prism difference keys are (crossing, stationary vertices, binary prism key).

    Each binary prism is on the indicated *pair of slots* and uses local slot zero.
    The output indexes actual pair-of-update atoms of the full tensor.
    """
    answer = {}
    by_edge = {}
    for (edge, vertices, prism), coefficient in difference.items():
        if coefficient:
            if edge not in pads or pads[edge] != vertices:
                return None
            by_edge.setdefault(edge,{})[prism] = coefficient
    for (a,b), local in by_edge.items():
        chain = filling([updates[a]], [updates[b]], local)
        if chain is None:
            return None
        for (_,k,_,h), value in chain.items():
            answer[a,k,b,h] = value
    return answer


def checks():
    charts = contexts = checked = chains = 0
    for n in range(2, 7):
        columns = {x:x for x in range(n)}
        end = tuple(range(n))
        for start in permutations(end):
            try:
                pads = interval(start,end,columns)
            except ValueError:
                continue
            charts += 1
            for w in readings(start,end,columns,(0,)*n):
                observations(start,w,columns,pads)
                contexts += sum(t[0]=='C' for t in w)
    # Several spatial columns, including two temporal slots on a single column.
    for columns, start, updates in [
        ((0,1,2), (2,0,1), (1,1,1)),
        ((0,1,2,3), (2,3,0,1), (1,0,1,0)),
        ((0,0,1,2), (3,0,1,2), (0,1,1,1)),
        ((0,1,2,3), (1,3,0,2), (1,1,0,1))]:
        end = tuple(range(len(start)))
        columns = dict(enumerate(columns))
        pads = interval(start,end,columns)
        words = list(readings(start,end,columns,updates))
        marks = {w:observations(start,w,columns,pads) for w in words}
        for w in words:
            seen, todo = {w}, [w]
            while todo:
                v = todo.pop()
                for j,(a,b) in enumerate(zip(v,v[1:])):
                    if exchange(a,b):
                        u = v[:j]+(b,a)+v[j+2:]
                        assert u in marks
                        if u not in seen:
                            seen.add(u)
                            todo.append(u)
            for u in words:
                cert = comparison(w,u)
                assert (cert is not None) == (u in seen) == (marks[w] <= marks[u])
                if cert:
                    v = list(w)
                    for j in cert:
                        assert exchange(v[j], v[j+1])
                        v[j],v[j+1] = v[j+1],v[j]
                    assert tuple(v) == u
                checked += 1
        # Compute the tensor differential directly on the full padded basis.
        depths = tuple(2+(i%2) for i in end)
        for seed in range(6):
            original, diff = {}, Counter()
            for (a,b), vertices in pads.items():
                for k,h in product(range(depths[a]),range(depths[b])):
                    c = (a+b+2*k+3*h+seed)%5-2
                    if c:
                        original[a,k,b,h] = c
                        for side,own,phase in [('L',k,h),('R',h,k)]:
                            for shift,sign in [(0,-1),(1,1)]:
                                diff[(a,b),vertices,(side,0,own,0,phase+shift)] += sign*c
            assert top_filling(pads,depths,diff) == original
            chains += 1
    isolated = 0
    for n in range(3,7):
        end = tuple(range(n))
        for start in permutations(end):
            for marked in combinations(start,3):
                if marked[0] > marked[1] > marked[2]:
                    projected = []
                    for word in triangle_facets(start,end,marked):
                        order, kept = list(start), []
                        for j in word:
                            a,b = order[j:j+2]
                            assert a>b
                            if a in marked and b in marked:
                                kept.append((a,b))
                            order[j:j+2] = b,a
                        assert tuple(order) == end and len(kept) == 3
                        projected.append(kept)
                    assert projected[0] == projected[1][::-1]
                    isolated += 1
    print(f'{charts} triangle-free charts, {contexts} observed crossing contexts, '
          f'{checked} directed comparisons, {chains} full tensor boundary recoveries, '
          f'{isolated} reversed triples isolated')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--start', help='comma-separated chronological slot IDs')
    parser.add_argument('--end', help='comma-separated chronological slot IDs')
    parser.add_argument('--columns', help='column for each slot ID, starting at zero')
    args = parser.parse_args()
    if args.start:
        seq = lambda s: tuple(map(int,s.split(',')))
        cols = dict(enumerate(seq(args.columns)))
        print('crossing pairs and stationary tensor vertices',
              interval(seq(args.start),seq(args.end),cols))
    else:
        checks()
