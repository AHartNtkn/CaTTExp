"""Degree 2n signed pair tests at independent rank-n scalar births (n >= 3).

JSON fields: rank, through, packets, pairs. Each entry [i,j,v] in pairs
adds v oriented sphere generators on zero-based terminal tips i and j.
Optional moduli gives the five subgroup generators; zero denotes {0}.
"""
from argparse import ArgumentParser
from itertools import combinations, permutations, product
import json
from pathlib import Path


def reading(n,m,sizes,entries):
    if type(n) is not int or n<3 or type(m) is not int or m<0 or any(type(k) is not int or k<=0 for k in sizes):
        raise ValueError('invalid scalar rank, through count or packet size')
    parity = (-1)**n
    length = m+sum(sizes)
    pairs = {}
    for i,j,v in entries:
        if any(type(x) is not int for x in (i,j,v)) or not (0<=i<length and 0<=j<length) or i==j:
            raise ValueError('expected distinct terminal indices and an integer multiplicity')
        if i>j:
            i,j,v = j,i,parity*v
        pairs[i,j] = pairs.get((i,j),0)+v
    def a(i,j):
        return pairs.get((i,j),0)
    blocks = []
    offset = m
    for size in sizes:
        blocks.append(range(offset,offset+size))
        offset += size
    result = dict(through_pair=[a(i,j) for i,j in combinations(range(m),2)],
                  binary_internal=[],ternary_internal=[],through_packet=[],between_packets=[])
    for block in blocks:
        end = block[-1]
        result['binary_internal'].extend(a(i,end) for i in block[:-1])
        result['ternary_internal'].extend(a(i,j)-a(i,end)-parity*a(j,end)
                                          for i,j in combinations(block[:-1],2))
        result['through_packet'].extend(a(t,i)-a(t,end) for t in range(m) for i in block[:-1])
    for left,right in combinations(blocks,2):
        u,v = left[-1],right[-1]
        result['between_packets'].extend(a(i,j)-a(u,j)-a(i,v)+a(u,v)
                                         for i in left[:-1] for j in right[:-1])
    return result


def evaluate(data):
    tests = reading(data['rank'],data['through'],data['packets'],data['pairs'])
    answer = dict(raw_null=not any(any(values) for values in tests.values()),coordinates=tests)
    if 'moduli' in data:
        d = data['moduli']
        if set(d)!=set(tests) or any(type(k) is not int or k<0 for k in d.values()):
            raise ValueError('expected nonnegative subgroup generators for the five named tests')
        answer['fills_given_moduli'] = all((v%k==0 if k else v==0)
                                            for field,values in tests.items() for k in [d[field]] for v in values)
    return answer


def audit():
    count = 0
    for n,m,sizes in product((3,4),(0,2),((2,2),(1,3),(3,2,2))):
        ends = []
        offset = m
        for k in sizes:
            ends.append(list(range(offset,offset+k)))
            offset += k
        exterior = list(range(m))
        pairs = list(combinations(range(offset),2))
        # Columns from the configuration fibres of the actual successive
        # batches. A new site may wind around every older live individual tip.
        rows = set()
        for order in permutations(ends):
            active = exterior.copy()
            for packet in order:
                for t in active:
                    rel = [(t,i,1) for i in packet]
                    assert not any(any(v) for v in reading(n,m,sizes,rel).values())
                    rows.add(tuple(sorted((min(t,i),max(t,i)) for i in packet)))
                active.extend(packet)
        # A common batch moves two whole new packets about one another.
        for a,b in combinations(ends,2):
            assert not any(any(v) for v in reading(n,m,sizes,[(i,j,1) for i in a for j in b]).values())
        # Reconstruct each terminal generator by placements of the five
        # small witnesses. The discrepancy must be an integral combination
        # of row/column transfers, checked in terminal coordinates.
        for left,right in pairs:
            vals = reading(n,m,sizes,[(left,right,1)])
            coeffs = {name:iter(v) for name,v in vals.items()}
            residual = dict.fromkeys(pairs,0)
            residual[left,right] = 1
            def place(i,j,value):
                if i>j:
                    i,j,value = j,i,(-1)**n*value
                residual[i,j] -= value
            for i,j in combinations(exterior,2):
                place(i,j,next(coeffs['through_pair']))
            for packet in ends:
                for i in packet[:-1]:
                    value = next(coeffs['binary_internal'])
                    for j in packet:
                        if i!=j:
                            place(i,j,value)
                for i,j in combinations(packet[:-1],2):
                    place(i,j,next(coeffs['ternary_internal']))
                for t in exterior:
                    for i in packet[:-1]:
                        place(t,i,next(coeffs['through_packet']))
            for a,b in combinations(ends,2):
                for i in a[:-1]:
                    for j in b[:-1]:
                        place(i,j,next(coeffs['between_packets']))
            def subtract(row,factor):
                assert tuple(row) in rows
                for pair in row:
                    residual[pair] -= factor
            for packet in ends:
                for t in exterior:
                    subtract([(t,i) for i in packet],residual[t,packet[-1]])
            for a,b in combinations(ends,2):
                for i in a:
                    subtract([(i,j) for j in b],residual[i,b[-1]])
                for j in b[:-1]:
                    subtract([(i,j) for i in a],residual[a[-1],j])
            assert not any(residual.values())
            count += 1
    print(f'{count} terminal sphere generators reconstructed integrally from small packet placements and schedule relations.')
    print('Both antipodal signs, singleton packets, three simultaneous births and two throughs checked.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(evaluate(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
