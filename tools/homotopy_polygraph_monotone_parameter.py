"""Fixed-parameter whole-presentation decision in the total resource count."""

from collections import defaultdict
from itertools import combinations_with_replacement, product
from math import perm

from homotopy_polygraph_mask_catalogue import catalogue
from homotopy_polygraph_monotone import record_homology, reduced_axis
from homotopy_polygraph_parking import acquisition_before_release
from homotopy_polygraph_transfer_complexity import match_processes


def support_bound(resources):
    types = (1<<resources)*sum(perm(resources,k) for k in range(resources+1))
    return (resources+1)*types+2*resources


def parameter_decision(controls, resources):
    available = defaultdict(list)
    for i,(vertices,edges) in enumerate(controls):
        for r in range(resources):
            p,v = ('P',r),('V',r)
            if acquisition_before_release(edges,p,v) or acquisition_before_release(edges,v,p):
                raise ValueError("one walk changes a resource in both directions")
        types = {reduced_axis(x) for x in catalogue(vertices,edges,resources)}-{(0,)}
        for typ in types:
            available[typ].append(i)
    limit = min(len(controls),support_bound(resources))
    # Any matching of size <= limit can replace an omitted supplier using
    # one of the limit retained suppliers of the same type.
    available = {typ:actors[:limit] for typ,actors in available.items()}
    types = sorted(available)
    for size in range(1,limit+1):
        for axes in combinations_with_replacement(types,size):
            if any(axes.count(t)>len(available[t]) for t in set(axes)):
                continue
            matched = match_processes(axes,available)
            if matched and record_homology(axes,resources)[1]:
                return False, matched
    return True,None


def projected_components(factors,corners,project):
    remaining = set(corners)
    parts = []
    while remaining:
        start = remaining.pop()
        stack, q = [start], {project(start)}
        while stack:
            v = stack.pop()
            for i,f in enumerate(factors):
                for w in f:
                    neighbor = v[:i]+(w,)+v[i+1:]
                    if neighbor in remaining:
                        remaining.remove(neighbor)
                        stack.append(neighbor)
                        q.add(project(neighbor))
        parts.append(frozenset(q))
    assert len(set(parts)) == len(parts)
    return frozenset(parts)


def transfer_parts(n,m,clipped,omit):
    # Actors A go from guard 0 to guard 1; actors B in the other direction.
    # An infeasible corner closes a cycle using the very same A and same B.
    factors = [range(n),range(n),range(m),range(m)]
    corners = [v for v in product(*factors) if (v[0]!=v[1] or v[2]!=v[3])
               and all(v[i]!=0 for i in omit)]
    def project(v):
        return tuple(-1 if i in clipped and x!=0 else x for i,x in enumerate(v))
    return projected_components(factors,corners,project)


def check():
    slots = 4
    for m in (1,2,3):
        for mask in range(1<<slots):
            omit = [j for j in range(slots) if mask & (1<<j)]
            clipped = (0,1)
            full = transfer_parts(9,m,clipped,omit)
            assert full == transfer_parts(4,m,clipped,omit)
    print('48 restriction diagrams agree on all projected connected components after truncation.')
    def neq(q):
        factors = [range(q)]*2
        return projected_components(factors,(v for v in product(*factors) if v[0]!=v[1]),lambda v:v)
    assert len(neq(2))==2 and len(neq(3))==1
    print('Two distinct allocations have two components on two names and one component on three.')
    def graph(t,h):
        return range(3),[(0,('P',t),1),(1,('V',h),2)]
    a,b = graph(0,1),graph(1,0)
    for pool,expected in [([a,b,b],True),([a,a,b,b],False),([a]*24+[b]*24,False)]:
        passed,witness = parameter_decision(pool,2)
        assert passed == expected
        if witness:
            assert len(witness)==len({i for i,_ in witness})==4
        print(f'{len(pool)} controls, homotopical {passed}, certificate size {len(witness or [])}.')


if __name__ == '__main__':
    check()
