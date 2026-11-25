"""Solve square-zero cyclic sheet placements and compile arithmetic into cube-zero placements.

The linear input is {"blocks":[1,2,...],"steps":[...],"face":[...]} with flat
integral vectors. Optional "counts" fixes occurrences per step (null is free).
Circuit input uses ["add", x, y, z], ["mul", x, y, z] and ["set", x, value].
Each wire becomes one directed declaration. Candidate sheets are signed integers.
"""
import json
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from semistrict_surface_penultimate_intervals import check


def translate(blocks, row, sheet):
    result = []
    start = 0
    for size in blocks:
        block = row[start:start+size]
        start += size
        for j, value in enumerate(block):
            if j >= 1:
                value += sheet*block[j-1]
            if j >= 2:
                value += (sheet*(sheet-1)//2)*block[j-2]
            result.append(value)
    return result


def linear_queries(blocks, steps, requests):
    width = sum(blocks)
    if any(n not in (1, 2) for n in blocks) or any(len(v) != width for v in steps):
        raise ValueError('supply one full step vector per rule in blocks of length one or two')
    changes = [[b-a for a, b in zip(v, translate(blocks, v, 1))] for v in steps]
    lines = ['(set-logic QF_LIA)']
    for i in range(len(steps)):
        lines.extend([f'(declare-const n{i} Int)', f'(declare-const w{i} Int)',
                      f'(assert (>= n{i} 0))', f'(assert (=> (= n{i} 0) (= w{i} 0)))'])
    def integer(value):
        if type(value) is not int:
            raise ValueError('use integer coefficients')
        return str(value) if value >= 0 else f'(- {-value})'
    for face, counts in requests:
        if len(face) != width or len(counts) != len(steps):
            raise ValueError('incorrect face width or number of counts')
        lines.append('(push 1)')
        for i, n in enumerate(counts):
            if n is not None:
                if type(n) is not int or n < 0:
                    raise ValueError('counts must be nonnegative integers or null')
                lines.append(f'(assert (= n{i} {n}))')
        for j, value in enumerate(face):
            terms = [f'(* {integer(v[j])} {var}{i})' for var, values in (('n',steps),('w',changes))
                     for i,v in enumerate(values) if v[j]]
            expr = '(+ 0 '+' '.join(terms)+')' if terms else '0'
            lines.append(f'(assert (= {expr} {integer(value)}))')
        lines.extend(['(check-sat)', '(pop 1)'])
    answers = check('\n'.join(lines)).splitlines()
    if len(answers) != len(requests) or any(s not in ('sat','unsat') for s in answers):
        raise RuntimeError(f'linear integer solver returned {answers}')
    return [s == 'sat' for s in answers]


def compile_circuit(gates):
    wires = {}
    for gate in gates:
        op, *args = gate
        if op in ('add', 'mul') and len(args) == 3:
            names = args
        elif op == 'set' and len(args) == 2 and type(args[1]) is int:
            names = args[:1]
        else:
            raise ValueError('expected add/mul with three wire names, or set with a wire and an integer')
        for name in names:
            if not isinstance(name, str) or not name or name.startswith('@'):
                raise ValueError('wire names must be nonempty strings without a leading @')
            wires.setdefault(name, len(wires))
    blocks, pieces, face = [], [], []
    def block(target, entries):
        offset = len(face)
        blocks.append(len(target))
        face.extend(target)
        pieces.extend((name, offset, values) for name, values in entries)
    for index, gate in enumerate(gates):
        op, *args = gate
        if op == 'set':
            block([1,args[1]], [(args[0],[1,0])])
        elif op == 'add':
            x,y,z = args
            block([1,0], [(x,[1,0]),(y,[1,0]),(z,[-1,0])])
        else:
            x,y,z = args
            w = f'@sum{index}'
            wires[w] = len(wires)
            block([-1,-1,0], [(w,[1,0,0]),(x,[-1,0,0]),(y,[-1,0,0]),(z,[0,-1,0])])
    for name in wires:
        block([1], [(name,[1])])
    steps = [[0]*len(face) for _ in wires]
    for name, offset, values in pieces:
        for k, value in enumerate(values, offset):
            steps[wires[name]][k] += value
    return dict(wires=list(wires), blocks=blocks, steps=steps, face=face)


def evaluate(context, sheets):
    if set(sheets) != set(context['wires']) or any(type(z) is not int for z in sheets.values()):
        raise ValueError('supply exactly one signed integer sheet for every wire, including @sum slots')
    total = [0]*len(context['face'])
    for name, step in zip(context['wires'], context['steps'], strict=True):
        total = [a+b for a,b in zip(total,translate(context['blocks'],step,sheets[name]),strict=True)]
    return total == context['face']


def audit():
    # Enumerate each occurrence independently by actual forward and inverse
    # shifts. Within the queried window a single shift of magnitude <=6
    # realizes any required even correction whenever an occurrence is present.
    blocks, steps = [2,1], [[2,1,1],[2,-1,1]]
    requests, expected = [], []
    def vertical(step):
        positive = negative = step[1]
        values = {positive}
        for _ in range(6):
            positive += step[0]
            negative -= step[0]
            values.update((positive, negative))
        return values
    def placements(n, m):
        sums = {0}
        for step, count in zip(steps, (n,m)):
            for _ in range(count):
                sums = {a+b for a in sums for b in vertical(step)}
        return sums
    for n, m in product(range(3), repeat=2):
        actual = placements(n,m)
        for v in range(-6,7):
            requests.append(([2*(n+m),v,n+m],[n,m]))
            expected.append(v in actual)
    for total_count in range(5):
        actual = set().union(*(placements(n,total_count-n) for n in range(total_count+1)))
        for v in range(-6,7):
            requests.append(([2*total_count,v,total_count],[None,None]))
            expected.append(v in actual)
    assert linear_queries(blocks,steps,requests) == expected
    ctx = compile_circuit([['mul','x','y','z']])
    comparisons = 0
    for x,y,z,w in product(range(-3,4), range(-3,4), range(-10,11), range(-7,8)):
        assert evaluate(ctx,dict(x=x,y=y,z=z,**{'@sum0':w})) == (x*y == z and x+y == w)
        comparisons += 1
    circuit = [['mul','x','x','s'],['add','s','x','q'],['set','q',12]]
    ctx = compile_circuit(circuit)
    for x in range(-9,10):
        assert evaluate(ctx, dict(x=x,s=x*x,q=x*x+x,**{'@sum0':2*x})) == (x in (-4,3))
    # Read the translation independently by iterating the integral Jordan
    # action or its inverse, including negative shifts and mixed blocks.
    for size,z in product((1,2,3),range(-9,10)):
        row = list(range(2,2+size))
        power = row.copy()
        for _ in range(abs(z)):
            if z >= 0:
                power = [a+b for a,b in zip(power,[0]+power)]
            else:
                for j in range(1,size):
                    power[j] -= power[j-1]
        assert power == translate([size],row,z)
    return len(requests), comparisons


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--linear', type=Path)
    mode.add_argument('--circuit', type=Path)
    parser.add_argument('--sheets', type=Path)
    args = parser.parse_args()
    if args.sheets and not args.circuit:
        parser.error('--sheets needs --circuit')
    if args.linear:
        data = json.loads(args.linear.read_text())
        print(json.dumps(dict(fills=linear_queries(data['blocks'],data['steps'],
              [(data['face'],data.get('counts',[None]*len(data['steps'])))])[0])))
    elif args.circuit:
        ctx = compile_circuit(json.loads(args.circuit.read_text()))
        print(json.dumps(dict(fills_at_these_sheets=evaluate(ctx,json.loads(args.sheets.read_text())))
                         if args.sheets else ctx))
    else:
        linear, nonlinear = audit()
        print(f'{linear} linear placement decisions and {nonlinear} signed multiplication placements checked.')
