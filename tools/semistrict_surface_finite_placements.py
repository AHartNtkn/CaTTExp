"""Finite-exponent placements over a cyclic deck using a finite carry automaton.

Input keys: modulus, rank, steps, face, relations. Each vector is a list
of [power, coordinate, coefficient] triples in (Z/modulus)[t,t^-1]^rank.
Each step is used once. The solver returns signed sheets relative to the face.
--plane compiles addition, constant and prime-power gates for a two-dimensional
deck. With --sheets it evaluates the resulting Laurent module rows.
"""
from argparse import ArgumentParser
from collections import deque
from itertools import product
from math import comb, isqrt
from pathlib import Path
import json


def cyclic(modulus, rank, steps, face, relations):
    if modulus < 2 or rank < 1:
        raise ValueError('use a modulus >= 2 and positive module rank')
    columns = [[(j, k, -c) for j,k,c in face], *steps, *relations]
    # A monomial factor moves only the origin of its column. Keep those
    # origins for the answer and store just each column's internal width.
    origins = [min((j for j,_,c in col if c%modulus),default=0) for col in columns]
    columns = [[(j-base,k,c) for j,k,c in col if c%modulus] for base,col in zip(origins,columns)]
    length = (1+max((j for col in columns for j,_,_ in col),default=0))*rank
    def pack(column):
        out = [0]*length
        for j,k,c in column:
            if not 0 <= k < rank:
                raise ValueError('coordinate outside the specified free module')
            i = j*rank+k
            out[i] = (out[i]+c) % modulus
        return tuple(out)
    cols = list(map(pack,columns))
    tokens = len(steps)+1
    full = (1 << tokens)-1
    # Each possible new relation coefficient is independent at this site.
    def weighted(weights, vectors):
        return tuple(sum(w*v[j] for w,v in zip(weights,vectors)) % modulus for j in range(length))
    multipliers = {weighted(cs,cols[tokens:]) for cs in product(range(modulus),repeat=len(relations))}
    emissions = []
    for mask in range(full+1):
        word = weighted([(mask>>i)&1 for i in range(tokens)],cols[:tokens])
        emissions.append([tuple((x+y)%modulus for x,y in zip(word,v)) for v in multipliers])
    zero = (0,)*(length-rank)
    start = (0,zero)
    queue = deque([start])
    parents = {start:None}
    while queue:
        state = queue.popleft()
        used,carry = state
        if used == full and carry == zero:
            events = []
            while parents[state] is not None:
                state,mask = parents[state]
                events.append(mask)
            at = {i:j for j,mask in enumerate(reversed(events)) for i in range(tokens) if mask & (1<<i)}
            return [at[i]-at[0]+origins[0]-origins[i] for i in range(1,tokens)]
        free = full ^ used
        mask = free
        while True:
            for emission in emissions[mask]:
                out = tuple((x+y)%modulus for x,y in zip(carry+(0,)*rank, emission))
                if any(out[:rank]):
                    continue
                nxt = used|mask, out[rank:]
                if nxt not in parents:
                    queue.append(nxt)
                    parents[nxt] = state,mask
            if not mask:
                break
            mask = (mask-1)&free
    return None


def prime(p):
    return type(p) is int and p >= 2 and all(p%d for d in range(2,isqrt(p)+1))


def plane(gates, control_prime=2):
    # coordinate, coefficient pairs become increments in a direct sum of cyclic
    # modules. A row's mode specifies the actions of the two deck generators.
    if not prime(control_prime):
        raise ValueError('use a prime for the equality rows')
    wires = {}
    rows = []
    def row(mode, entries, target=None, p=control_prime):
        rows.append(dict(mode=mode, prime=p, entries=entries, target=target or []))
    for i, gate in enumerate(gates):
        op,*args = gate
        if op in ('power','set') and len(args)==2:
            names = args[:1]
            if type(args[1]) is not int or (op=='power' and not prime(args[1])):
                raise ValueError('set takes an integer and power takes a prime')
        elif op=='add' and len(args)==3:
            names = args
        else:
            raise ValueError('use add, power or set gates')
        for name in names:
            if not isinstance(name,str) or not name:
                raise ValueError('use nonempty wire names')
            if name not in wires:
                h,v = f'h/{name}',f'v/{name}'
                wires[name] = (h,v)
                row('second',[(h,1)],[(0,1)])
                row('first',[(v,1)],[(0,1)])
                row('sum',[(h,1),(v,-1)])
        h,v = wires[names[0]]
        if op=='set':
            row('first',[(h,1)],[(args[1],1)])
        elif op=='power':
            row('frobenius',[(v,1),(h,-1)],[(0,1)],args[1])
        else:
            (hx,_),(_,vy),(hz,_) = (wires[n] for n in names)
            pair = f'add/{i}'
            row('first',[(pair,1),(hx,-1)])
            row('second',[(pair,1),(vy,-1)])
            row('sum',[(pair,1),(hz,-1)])
    return rows


def reads(rows, sheets):
    for row in rows:
        terms = [(sheets[n][0],sheets[n][1],c) for n,c in row['entries']]
        target = [(j,-c) for j,c in row['target']]
        if row['mode']=='frobenius':
            terms += [(j,0,c) for j,c in target]
            a = min(x for x,_,_ in terms)
            b = min(y for _,y,_ in terms)
            coeffs = {}
            for x,y,c in terms:
                for j in range(y-b+1):
                    k = x-a+j
                    coeffs[k] = coeffs.get(k,0)+c*comb(y-b,j)
        else:
            coeffs = {}
            for x,y,c in terms:
                k = {'first':x,'second':y,'sum':x+y}[row['mode']]
                target.append((k,c))
            for j,c in target:
                coeffs[j] = coeffs.get(j,0)+c
        if any(v%row['prime'] for v in coeffs.values()):
            return False
    return True


def audit():
    # In Z/6[t,t^-1]/(t^2+1), multiplication by t takes (x,y)
    # to (-y,x), so all sheets are represented by four matrix powers.
    ring = [(1,0),(0,1),(-1,0),(0,-1)]
    possible = {((a+2*c)%6,(b+2*d)%6) for (a,b),(c,d) in product(ring,repeat=2)}
    cases = 0
    for x,y in product(range(6),repeat=2):
        shifts = cyclic(6,1,[[(0,0,1)],[(0,0,2)]],[(0,0,x),(1,0,y)],[[(0,0,1),(2,0,1)]])
        assert (shifts is not None) == ((x,y) in possible)
        if shifts is not None:
            (a,b),(c,d) = [ring[i%4] for i in shifts]
            assert ((a+2*c)%6,(b+2*d)%6)==(x,y)
        cases += 1
    # A free, infinite module after eliminating its second generator.
    for offset in range(-8,9):
        shifts = cyclic(3,2,[[(0,1,1)]],[(offset,0,1),(offset+1,0,1),(offset+2,0,-1)],
                        [[(0,1,1),(0,0,-1),(1,0,-1),(2,0,1)]])
        assert shifts == [offset]
    powers = 0
    for p in (2,3,5,7):
        rows = plane([['power','x',p]],p)
        expected = {1}
        while max(expected)*p <= 130:
            expected.add(max(expected)*p)
        for n in range(-5,131):
            assert reads(rows,{'h/x':(n,0),'v/x':(0,n)}) == (n in expected)
            powers += 1
    rows = plane([['power','x',2],['power','y',3],['add','x','y','z'],['set','z',11]])
    for x,y in product(range(-2,14),repeat=2):
        vars = {'x':x,'y':y,'z':x+y}
        sheets = {f'{kind}/{name}':((v,0) if kind=='h' else (0,v))
                  for name,v in vars.items() for kind in ('h','v')}
        sheets['add/2'] = (x,y)
        assert reads(rows,sheets) == ((x,y) in ((2,9),(8,3)))
        sheets['add/2'] = (x,y+1)
        assert not reads(rows,sheets)
    return cases, powers


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--cyclic',type=Path)
    mode.add_argument('--plane',type=Path)
    parser.add_argument('--control-prime',type=int,default=2)
    parser.add_argument('--sheets',type=Path)
    args = parser.parse_args()
    if args.sheets and not args.plane:
        parser.error('--sheets requires --plane')
    if args.cyclic:
        print(json.dumps(dict(sheets=cyclic(**json.loads(args.cyclic.read_text())))))
    elif args.plane:
        rows = plane(json.loads(args.plane.read_text()),args.control_prime)
        print(json.dumps(dict(matches=reads(rows,json.loads(args.sheets.read_text()))) if args.sheets else rows))
    else:
        cases, powers = audit()
        print(f'{cases} cyclic quotient decisions, 17 free-module placements, {powers} Frobenius tests '
              'and 512 mixed-prime assignments checked.')
