"""Build the permutohedron-product cellular chains in the localized Gray hom.

Charts include empty-sided rules. A cell is stored by its descending serial
history and the positive sizes of its successive simultaneous tiers.
"""
from collections import Counter
import argparse
import json

from semistrict_surface_scalar_lift import cube
from semistrict_surface_return_gaps import exchange_at


def signed_neighbours(h, marks):
    for i,((p,a),(q,b)) in enumerate(zip(h,h[1:])):
        target = exchange_at(h,i,marks)
        if target is not None:
            yield target
        src,dst = marks[a]
        if p+len(dst) <= q:
            yield h[:i]+((q+len(src)-len(dst),b),(p,a))+h[i+2:]


def components(h, marks):
    seen,todo = {h},[h]
    while todo:
        for v in signed_neighbours(todo.pop(),marks):
            if v not in seen:
                todo.append(v)
                seen.add(v)
    return seen


def compositions(n):
    if n == 0:
        yield ()
    for size in range(1,n+1):
        for rest in compositions(n-size):
            yield (size,)+rest


def all_cells(h, marks):
    by_degree = [[] for _ in range(max(1,len(h)))]
    for u in components(h,marks):
        for sizes in compositions(len(u)):
            start = 0
            for size in sizes:
                if size >= 2 and cube(u,marks,start,size) is None:
                    break
                start += size
            else:
                by_degree[len(u)-len(sizes)].append((u,sizes))
    return by_degree


def boundary(cell, marks):
    history,sizes = cell
    result = Counter()
    start = degree = 0
    for i,size in enumerate(sizes):
        for mask in range(1,2**size-1):
            first = [x for x in range(size) if mask>>x&1]
            second = [x for x in range(size) if not mask>>x&1]
            earliest = first+second
            order = list(range(size))
            u = history
            parity = degree+len(first)-1
            for j,x in enumerate(earliest):
                k = order.index(x)
                while k>j:
                    u = exchange_at(u,start+k-1,marks)
                    assert u is not None
                    order[k-1],order[k] = order[k],order[k-1]
                    k -= 1
                    parity += 1
            refined = sizes[:i]+(len(first),len(second))+sizes[i+1:]
            result[u,refined] += (-1)**parity
        start += size
        degree += size-1
    return {k:v for k,v in result.items() if v}


def betti_mod2(cells,maps):
    ranks = [0]
    for d in range(1,len(cells)):
        ids = {c:i for i,c in enumerate(cells[d-1])}
        basis = {}
        for cell in cells[d]:
            row = sum(1<<ids[c] for c,a in maps[cell].items() if a%2)
            while row:
                pivot = row.bit_length()-1
                if pivot not in basis:
                    basis[pivot] = row
                    break
                row ^= basis[pivot]
        ranks.append(len(basis))
    ranks.append(0)
    return tuple(len(cs)-ranks[d]-ranks[d+1] for d,cs in enumerate(cells))


def compute(h, marks):
    cells = all_cells(h,marks)
    maps = {cell:boundary(cell,marks) for cs in cells for cell in cs}
    for d,cs in enumerate(cells):
        for cell in cs:
            squared = Counter()
            for face,c in maps[cell].items():
                assert d and face in maps
                for ridge,coef in maps[face].items():
                    squared[ridge] += c*coef
            assert not any(squared.values())
    return sum(map(len,cells)), betti_mod2(cells,maps)


def checks():
    total = 0
    expected = [1]
    for n in range(1,6):
        if n>1:
            expected = [a+(n-1)*b for a,b in zip(expected+[0],[0]+expected)]
        marks = {str(i):('','') for i in range(n)}
        count,betti = compute(tuple((0,str(i)) for i in range(n)),marks)
        assert betti == tuple(expected)
        total += count
    count,betti = compute(((0,'s'),)*3,{'s':('','')})
    assert betti == (1,1,0)
    total += count
    marks = {'b':('','x'),'d':('x',''),'s':('','')}
    count,betti = compute(((0,'b'),(0,'d'),(0,'s')),marks)
    assert betti == (1,1,0)
    total += count
    # All boxes stay attached to external wires in this length-changing example.
    marks = {'f':('x','xx'),'m':('xx','x'),'l':('x','x')}
    count,betti = compute(((1,'f'),(0,'l'),(1,'m')),marks)
    assert betti == (1,0,0)
    total += count
    print(f'{total} integral cellular boundaries squared to zero; '
          'five named scalar homologies, folded scalars, a floating bubble and anchored rewrites checked')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--chart',help='JSON with initial edge word, marks and [offset,name] history')
    args = parser.parse_args()
    if args.chart:
        with open(args.chart) as handle:
            data = json.load(handle)
        word = data['initial']
        history = tuple(map(tuple,data['history']))
        for pos,name in history:
            before,after = data['marks'][name]
            if not 0 <= pos <= len(word) or not word.startswith(before,pos):
                raise ValueError('invalid initial history')
            word = word[:pos]+after+word[pos+len(before):]
        print('cells, mod-two Betti numbers', compute(history,data['marks']))
    else:
        checks()
