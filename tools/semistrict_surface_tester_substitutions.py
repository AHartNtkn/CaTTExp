"""Minimize rank-two primary comparisons using maps between their four-complexes."""
from argparse import ArgumentParser
from functools import cache
from itertools import combinations, product
from math import gcd

from semistrict_surface_finite_bottom import primary, rank_two
from semistrict_surface_four_complex_operations import operation_presentation, solve, subgroup
from semistrict_surface_quadratic_image import reduction


def table(n, character):
    hx,h,hy,u,v = character
    correction = (n//2)*h
    return ((hx,0,(correction-u)%n),(h,u,v),(hy,(correction-v)%n,0))


def dual_value(n, character, face):
    return ((n//2)*sum(x*y for x,y in zip(character[:3],face[:3]))
            + character[3]*face[3] + character[4]*face[4]) % n


def pullbacks(n, source, target, matrices):
    p,_ = primary([n])
    parity = 2 if p == 2 else 1
    qs,qt = table(n,source),table(n,target)
    # Each target middle coordinate extends independently across the source
    # relations iff its three specified quadratic entries come from a hom.
    def attainable(m):
        return {tuple(sum(x*y for x,y in zip(q,col))%m for q in qs)
                for col in product(range(0,m,m//gcd(m,parity)),range(m),range(m))}
    allowed = [attainable(parity),attainable(n)]
    hx,h,hy,u,v = target
    readings = set()
    for a,b,c,d in matrices:
        det = a*d-b*c
        read = ((a*a*hx+a*b*h+b*b*hy)%parity, det*h%parity,
                (c*c*hx+c*d*h+d*d*hy)%parity, det*(a*u-b*v)%n, det*(-c*u+d*v)%n)
        if read in readings or not any(read):
            continue
        basis = ((a*a,a*b,b*b),(2*a*c,a*d+b*c,2*b*d),(c*c,c*d,d*d))
        for j,m in enumerate((parity,n,n)):
            values = tuple(sum(k*q[j] for k,q in zip(row,qt))%m for row in basis)
            if values not in allowed[int(j != 0)]:
                break
        else:
            readings.add(read)
    return readings


def minimize(n):
    p,_ = primary([n])
    parity = 2 if p == 2 else 1
    reps = [r['character'] for r in rank_two(n)]
    matrices = list(product(range(n),repeat=4))
    faces = list(product(range(parity),range(parity),range(parity),range(n),range(n)))

    @cache
    def detected(reading):
        return sum(1<<i for i,face in enumerate(faces) if dual_value(n,reading,face))

    constraints = set()
    for i,source in enumerate(reps):
        required = detected(source)
        coverage = []
        for target in reps:
            covered = 0
            for read in pullbacks(n,source,target,matrices):
                covered |= detected(read)
            coverage.append(covered)
        assert coverage[i] & required == required
        for j in range(len(faces)):
            if required & (1<<j):
                constraints.add(sum(1<<k for k,c in enumerate(coverage) if c & (1<<j)))
    minimal = [c for c in constraints if not any(d != c and d & c == d for d in constraints)]
    # Find all smallest hitting sets; singleton constraints usually force most
    # of the selected testers before there is any branching.
    forced = 0
    for c in minimal:
        if c.bit_count() == 1:
            forced |= c
    optional = [i for i in range(len(reps)) if not forced & (1<<i)]
    for size in range(len(optional)+1):
        solutions = []
        for extra in combinations(optional,size):
            selected = forced | sum(1<<i for i in extra)
            if all(c & selected for c in minimal):
                solutions.append([i for i in range(len(reps)) if selected & (1<<i)])
        if solutions:
            return reps,minimal,solutions


def audit():
    n = 4
    reps = [r['character'] for r in rank_two(n)]
    matrices = list(product(range(n),repeat=4))
    group = list(product(range(2),range(n),range(n)))
    # Independently tabulate images under actual middle-group homomorphisms.
    # Each entry in images realizes one simultaneous assignment on all three
    # relation disks, including the two-torsion restriction on the first input.
    for source in reps:
        qs = table(n,source)
        images = set()
        for basis in product([g for g in group if all(2*x%n == 0 for x in g[1:])],group,group):
            images.add(tuple(tuple(sum(c*z for c,z in zip(q,col))%m
                                   for col,m in zip(zip(*basis),(2,n,n))) for q in qs))
        for target in reps:
            qt = table(n,target)
            expected = set()
            for a,b,c,d in matrices:
                polys = ((a*a,a*b,b*b),(2*a*c,a*d+b*c,2*b*d),(c*c,c*d,d*d))
                pasted = tuple(tuple(sum(k*z for k,z in zip(row,col))%m
                                     for col,m in zip(zip(*qt),(2,n,n))) for row in polys)
                if pasted in images:
                    (qx,bxy,qy) = pasted
                    reading = (qx[0],bxy[0],qy[0],(a*bxy[1]+b*bxy[2])%n,
                               (c*bxy[1]+d*bxy[2])%n)
                    if any(reading):
                        expected.add(reading)
            assert expected == pullbacks(n,source,target,matrices)
    for a in range(2,11):
        n = 2**a
        half = n//2
        q = [[1,half],[1,half],[1,0]]
        for v in [0]+[2**i for i in range(a)]:
            qs = table(n,(1,1,1,0,v))
            if v != half:
                d = gcd(half-v,n)
                c = (-(half//d)*pow((half-v)//d,-1,n//d))%(n//d)
                assert [[h,(half*h+c*x)%n] for h,x,y in qs] == q
            else:
                assert [[h,y] for h,x,y in qs] == q
        for middle,quad in (([2],[[0],[1],[0]]),([2,n],q)):
            shell = [quad[1]] + [[0]*len(middle)]*2
            data = solve([n,n],middle,quad,shell)
            assert data['bottom_image'] == [2] and data['raw_order'] == 2
        for bottom in ([n,n],[2,n]):
            difference = [[1,0],[0,0],[0,-half]]
            assert solve(bottom,[2,n],q,difference)['raw_order'] == 1
            assert solve(bottom,[2,n],q,[[0,0],[0,0],[0,1]])['raw_order'] == n
        assert all(tuple((a*c,(a*d+b*c)%2,b*d)) != (1,1,1)
                   for a,b,c,d in product(range(2),repeat=4))
        for b in range(1,a+1):
            k = 2**(a-b)
            quad = [[0,0],[0,k],[-k,0]]
            rows,gens,hopfs = operation_presentation([n,n],[n,n],quad)
            assert subgroup(rows+hopfs,6,gens) == [2**b]
            face = [0,0,0,0,0,half]
            assert reduction(rows+hopfs,6)[1](face) == 2
    for n,minimum in ((2,1),(4,4),(8,5),(9,2)):
        _,_,solutions = minimize(n)
        assert all(len(s) == minimum for s in solutions)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('order',type=int,nargs='?',default=4)
    parser.add_argument('--audit', action='store_true')
    args = parser.parse_args()
    if args.audit:
        audit()
        print('All 225 orbit pairs at order four, explicit families through order 1024, '
              'and four minimum-cover computations checked.')
    else:
        reps,obligations,solutions = minimize(args.order)
        print(f'{len(reps)} orbits, {len(obligations)} minimal coverage constraints.')
        for solution in solutions:
            print('Smallest sufficient family:', [reps[i] for i in solution])
