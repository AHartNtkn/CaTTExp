"""Check the remaining three-slot penultimate comparison with integer tableaux.

The formula asks for two actual parallel 4-faces, a positive solution in the
square quotient, and a negative path excluding every original 5-chain filler.
Use --emit to check the same QF_LIA formula with a separate SMT solver.
"""

from argparse import ArgumentParser
from collections import defaultdict
from ctypes import CDLL, c_char_p, c_void_p
from ctypes.util import find_library
from itertools import combinations, product
from pathlib import Path


def column(updates):
    return [(0,0),(0,1)] + [(1,i) for i in range(updates+1)] + [(2,i) for i in range(updates)]


def boundary(cell):
    sign = 1
    for i,(rank,index) in enumerate(cell):
        if rank:
            start,end = (0,1) if rank == 1 else (index,index+1)
            for point,coefficient in ((start,-sign),(end,sign)):
                yield cell[:i]+((rank-1,point),)+cell[i+1:],coefficient
        sign *= (-1)**rank


def total(entries):
    entries = list(entries)
    if not entries:
        return '0'
    if len(entries) == 1:
        return entries[0]
    return '(+ '+' '.join(entries)+')'


def witness_query(counts, real_faces=False):
    if len(counts) != 3 or min(counts) < 1:
        raise ValueError('expected three positive update counts')
    cells = defaultdict(list)
    for cell in product(*(column(m) for m in counts)):
        cells[sum(rank for rank,_ in cell)].append(cell)
    sort = 'Real' if real_faces else 'Int'
    lines = ['(set-logic '+('QF_LRA' if real_faces else 'QF_LIA')+')']

    def variable(name,positive=False):
        lines.append(f'(declare-const {name} {sort})')
        if positive:
            lines.append(f'(assert (>= {name} 0))')
        return name

    def equal(left,right):
        lines.append(f'(assert (= {left} {right}))')

    def chain(k,prefix,positive):
        return {c:variable(prefix+str(i),positive) for i,c in enumerate(cells[k])}

    def require_boundary(row,previous):
        terms = defaultdict(list)
        for c,var in row.items():
            for f,sign in boundary(c):
                terms[f].append(var if sign == 1 else f'(- {var})')
        for f in previous[0]:
            equal(total(terms[f]),f'(- {previous[1][f]} {previous[0][f]})')

    previous = None
    for d in range(5):
        faces = [chain(d,f'r{d}{s}',True) for s in ('m','p')]
        for row in faces:
            if d:
                require_boundary(row,previous)
            else:
                equal(total(row.values()),'1')
        previous = faces
    z = chain(5,'z',False)
    require_boundary(z,previous)
    nodes = set(product(*(range(m) for m in counts)))

    def potential(axis,node):
        return '0' if node not in nodes else f'k{int(axis==1)}x'+'p'.join(map(str,node))
    for node in sorted(nodes):
        for axis in (0,1):
            variable(potential(axis,node))
    arcs = defaultdict(list)
    for c,var in z.items():
        axis = next(i for i,(d,_) in enumerate(c) if d == 1)
        end = tuple(j for _,j in c)
        start = end[:axis]+(end[axis]-1,)+end[axis+1:]
        lines.append(f'(assert (>= (+ {var} (- {potential(axis,start)} {potential(axis,end)})) 0))')
        arcs[start if start in nodes else None].append((end if end in nodes else None,var))

    def bad_paths(node,costs):
        for target,var in arcs[node]:
            path = costs+[var]
            if target is None:
                yield f'(< {total(path)} 0)'
            else:
                yield from bad_paths(target,path)
    lines.append('(assert (or '+' '.join(bad_paths(None,[]))+'))')
    lines.append('(check-sat)')
    return '\n'.join(lines)+'\n'


def check(query):
    lib = CDLL(find_library('z3') or 'libz3.so.4')
    apis = [('Z3_mk_config',[],c_void_p),('Z3_mk_context',[c_void_p],c_void_p),
            ('Z3_eval_smtlib2_string',[c_void_p,c_char_p],c_char_p),
            ('Z3_del_context',[c_void_p],None),('Z3_del_config',[c_void_p],None)]
    for name,args,ret in apis:
        func = getattr(lib,name)
        func.argtypes,func.restype = args,ret
    config = lib.Z3_mk_config()
    ctx = lib.Z3_mk_context(config)
    try:
        return lib.Z3_eval_smtlib2_string(ctx,query.encode()).decode().strip()
    finally:
        lib.Z3_del_context(ctx)
        lib.Z3_del_config(config)


def exceptional_classes(n):
    # Compute the signed ambiguity by its elementary potential equations.
    # Every nonconsecutive pair equates the two vertex potentials.
    blocks = [{i} for i in range(n)]
    for i,j in combinations(range(n),2):
        if j > i+1:
            a = next(s for s in blocks if i in s)
            b = next(s for s in blocks if j in s)
            if a is not b:
                a.update(b)
                blocks.remove(b)
    return len(blocks)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('counts',nargs='*',type=int)
    parser.add_argument('--emit',type=Path)
    args = parser.parse_args()
    if args.counts or args.emit:
        formula = witness_query(args.counts or (1,1,1))
        if args.emit:
            args.emit.write_text(formula)
        else:
            print(check(formula))
    else:
        for n in range(3,40):
            assert exceptional_classes(n) == (2 if n == 3 else 1)
        for counts in product((1,2),repeat=3):
            assert check(witness_query(counts)) == 'unsat'
            print(f'{counts}: integral comparison reflects',flush=True)
        assert check(witness_query((1,1,1),real_faces=True)) == 'sat'
        print('The rational relaxation has a spurious witness.')
