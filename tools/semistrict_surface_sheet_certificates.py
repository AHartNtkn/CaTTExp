"""Find the least cyclic period disproving a finite-exponent placement.

Uses the input of semistrict_surface_finite_placements.py --cyclic.
--period tests a single periodic quotient. --local-root verifies a periodic
placement in the integral example having no placement on the infinite sheet.
"""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path
import json

from semistrict_surface_cyclic_placements import compile_circuit, translate
from semistrict_surface_divisible_squares import diagonalize
from semistrict_surface_finite_placements import cyclic


def periodic(period, modulus, rank, steps, face, relations):
    if period < 1 or rank < 1 or modulus < 2:
        raise ValueError('use positive period and rank and a modulus >= 2')
    size = period*rank
    def vector(col, shift):
        v = [0]*size
        for j,k,c in col:
            if not 0 <= k < rank:
                raise ValueError('invalid free module coordinate')
            v[((j+shift)%period)*rank+k] += c
        return v
    orbit_relations = [vector(col,j) for col in relations for j in range(period)]
    for i in range(size):
        row = [0]*size
        row[i] = modulus
        orbit_relations.append(row)
    matrix, change, pivots = diagonalize(orbit_relations,0,size)
    assert pivots == size
    keep = [j for j in range(size) if abs(matrix[j][j]) > 1]
    moduli = [abs(matrix[j][j]) for j in keep]
    def reading(v):
        return tuple(sum(a*change[i][j] for i,a in enumerate(v)) % m for j,m in zip(keep,moduli))
    target = reading(vector(face,0))
    # Keep one placement per reachable finite-group value through each token.
    reached = {(0,)*len(keep): ()}
    for col in steps:
        options = [reading(vector(col,z)) for z in range(period)]
        after = {}
        for state, path in reached.items():
            for z, v in enumerate(options):
                dest = tuple((a+b)%m for a,b,m in zip(state,v,moduli))
                after.setdefault(dest,path+(z,))
        reached = after
    return reached.get(target)


def certificate(data):
    sheets = cyclic(**data)
    if sheets is not None:
        return dict(sheets=sheets)
    n = 1
    while periodic(n,**data) is not None:
        n += 1
    return dict(least_obstructing_period=n)


def local_root(n):
    if n < 1:
        raise ValueError('period must be positive')
    def value(x):
        return (x*x-2)*(x*x-17)*(x*x-34)
    x = next(a for a in range(n) if value(a)%n == 0)
    gates = [['mul','x','x','sq']]
    vals = {'x':x,'sq':x*x,'@sum0':2*x}
    for c in (2,17,34):
        k,y = f'k{c}',f'y{c}'
        gates.extend([['set',k,-c],['add','sq',k,y]])
        vals[k],vals[y] = -c,x*x-c
    for a,b,out in [('y2','y17','ab'),('ab','y34','v')]:
        vals[f'@sum{len(gates)}'] = vals[a]+vals[b]
        gates.append(['mul',a,b,out])
        vals[out] = vals[a]*vals[b]
    gates.append(['set','v',0])
    ctx = compile_circuit(gates)
    placed = [translate(ctx['blocks'],step,vals[name]) for name,step in zip(ctx['wires'],ctx['steps'])]
    error = [sum(row[j] for row in placed)-v for j,v in enumerate(ctx['face'])]
    i = 0
    for size in ctx['blocks']:
        rows = []
        for j in range(size):
            basis = [int(j==k) for k in range(size)]
            rows.append([a-b for a,b in zip(translate([size],basis,n),basis)])
        matrix,change,pivots = diagonalize(rows,0,size)
        for j in range(size):
            coeff = sum(error[i+k]*change[k][j] for k in range(size))
            assert (coeff % matrix[j][j] == 0) if j < pivots else (coeff == 0)
        i += size
    assert any(error)
    return dict(period=n, input_sheet=x, integral_polynomial=value(x))


def cut_example(n, site, phase):
    # Over F2 the source 1 at site+1 and the target 1+t^2 at site
    # differ by the relator 1+t+t^2. A nonzero homogeneous period-three
    # multiplier has been superimposed on the local certificate.
    marked = {site, (site+1)%n}
    rows = [(int(j==(site+1)%n) ^ int(j==site), 0, int(j==site)) for j in range(n)]
    multipliers = [int((j+phase)%3!=0) ^ int(j==site) for j in range(n)]
    def carries(rows, coeffs):
        terms = [tuple(x ^ c for x in row) for row,c in zip(rows,coeffs)]
        return [(terms[(j-1)%n][1] ^ terms[(j-2)%n][2], terms[(j-1)%n][2]) for j in range(n)]
    carry = carries(rows,multipliers)
    seen = {}
    j = site+2
    while j%n not in marked:
        val = carry[j%n]
        assert val != (0,0)  # The unmarked gap has a genuine background.
        if val in seen:
            start = seen[val]
            period = j-start
            break
        seen[val] = j
        j += 1
    else:
        raise AssertionError('no repeated carry in the unmarked gap')
    assert n%period == 0
    background = [multipliers[(start+(k-start)%period)%n] for k in range(n)]
    cleaned = [a^b for a,b in zip(multipliers,background)]
    assert carries(rows,cleaned)[start%n] == (0,0)
    # Unroll, with no wrap permitted at the two ends.
    line = [0]*(n+2)
    for a in range(n):
        k = (a+start)%n
        for b in range(3):
            line[a+b] ^= rows[k][b] ^ cleaned[k]
    assert not any(line)


def audit():
    for site,phase in product(range(18),range(3)):
        cut_example(18,site,phase)
    for n in range(1,101):
        assert local_root(n)['integral_polynomial']%n == 0
    for gap in range(1,10):
        data = dict(modulus=2,rank=1,steps=[[(0,0,1)]],
                    face=[(0,0,1),(gap,0,1),(2*gap,0,1)],relations=[])
        n = 1
        while (2*gap)%n == 0:
            n += 1
        assert certificate(data)==dict(least_obstructing_period=n)
    # The three-cycle relation becomes a unit in every wrap of period
    # coprime to three over F2. Such wraps cannot certify this negative.
    rotor = dict(modulus=2,rank=1,steps=[],face=[(0,0,1)],
                 relations=[[(0,0,1),(1,0,1),(2,0,1)]])
    for n in range(1,13):
        assert (periodic(n,**rotor) is None) == (n%3==0)
    # Width one gives two carry states and the theorem permits period 10
    # for up to three tokens (including the target).
    count = 0
    for a,b,c in product(range(4),repeat=3):
        def col(v):
            return [(j,0,1) for j in range(2) if v & (1<<j)]
        data=dict(modulus=2,rank=1,steps=[col(a),col(b)],face=col(c),relations=[])
        assert (periodic(10,**data) is None) == (cyclic(**data) is None)
        count += 1
    return count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--period',type=int)
    parser.add_argument('--local-root',type=int)
    args = parser.parse_args()
    if args.local_root is not None:
        print(json.dumps(local_root(args.local_root)))
    elif args.input:
        data = json.loads(args.input.read_text())
        print(json.dumps(certificate(data) if args.period is None else dict(sheets=periodic(args.period,**data))))
    elif args.period is not None:
        parser.error('--period needs an input')
    else:
        print(f'{audit()} single-period equivalences, 9 minimum obstructions, 12 periodic relation tests, '
              '54 periodic background cuts and 100 integral local placements verified.')
