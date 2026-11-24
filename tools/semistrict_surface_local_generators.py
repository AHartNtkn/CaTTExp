"""Check local generator images, word lifts, and the finite-support distinction."""
from argparse import ArgumentParser
from functools import cache
from itertools import product
from pathlib import Path
import re
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import accepted, rejected, run


WIDTH_ONE = ('--insertion-width', '1')
FULL = ('--sua',)
SCALARS = '(x : *) (a : id(x) -> id(x)) (b : id(x) -> id(x))'
ROW = '[[a],[b],[c]]'
HEADS = """
def left {f{a}g}{h{b}i} = comp[comp[[a],h],comp[g,[b]]]
def right {f{a}g}{h{b}i} = comp[comp[f,[b]],comp[[a],i]]
def swap = coh [ [[a],[b]] : left(a,b) -> right(a,b) ]
def unswap = coh [ [[a],[b]] : right(a,b) -> left(a,b) ]
def h [[a],[b]] = comp[[a],[b]]
def tri [[a],[b],[c]] = comp[[a],[b],[c]]
def grouped = coh [ {f{a}g}{h{b}i}{j{c}k} : comp[comp[f,h],j] -> comp[comp[g,i],k] ]
def flat = coh [ [[a],[b],[c]] : h(h(a,b),c) -> grouped(a,b,c) ]
def unflat = coh [ [[a],[b],[c]] : grouped(a,b,c) -> h(h(a,b),c) ]
"""
RULES = """
def initial [[a],[b],[c]] = tri(a,b,c)
def one [[a],[b],[c]] = h(h(a,b),c)
def two [[a],[b],[c]] = h(a,h(b,c))
def dest {f{a}g}{h{b}i}{j{c}k} = comp[comp[[a],[b],j],comp[g,i,[c]]]
def arrive = coh [ [[a],[b],[c]] : one(a,b,c) -> dest(a,b,c) ]
def arrive_other = coh [ [[a],[b],[c]] : two(a,b,c) -> dest(a,b,c) ]
def leave = coh [ [[a],[b],[c]] : dest(a,b,c) -> one(a,b,c) ]
def leave_other = coh [ [[a],[b],[c]] : dest(a,b,c) -> two(a,b,c) ]
"""


RAW_RULES = """
def initial = coh [ {f{a}g}{i{b}j}{k{c}l}{m{d}n} : comp[comp[f,i],comp[k,m]] -> comp[comp[g,j],comp[l,n]] ]
def group_left = coh [ {p{e}q}{k{c}l}{m{d}n} : comp[p,comp[k,m]] -> comp[q,comp[l,n]] ]
def group_right = coh [ {f{a}g}{i{b}j}{p{e}q} : comp[comp[f,i],p] -> comp[comp[g,j],q] ]
def one [[a],[b],[c],[d]] = group_left(h(a,b),c,d)
def two [[a],[b],[c],[d]] = group_right(a,b,h(c,d))
def first = coh [ [[a],[b],[c],[d]] : initial(a,b,c,d) -> one(a,b,c,d) ]
def first_back = coh [ [[a],[b],[c],[d]] : one(a,b,c,d) -> initial(a,b,c,d) ]
def second = coh [ [[a],[b],[c],[d]] : initial(a,b,c,d) -> two(a,b,c,d) ]
def second_back = coh [ [[a],[b],[c],[d]] : two(a,b,c,d) -> initial(a,b,c,d) ]
def xx [[a],[b],[c],[d]] = comp[first(a,b,c,d),first_back(a,b,c,d)]
def yy [[a],[b],[c],[d]] = comp[second(a,b,c,d),second_back(a,b,c,d)]
def rule = coh [ [[a],[b],[c],[d]] : comp[xx(a,b,c,d),yy(a,b,c,d)] -> comp[yy(a,b,c,d),xx(a,b,c,d)] ]
def unrestricted_back = coh [ [[a],[b],[c],[d]] : comp[yy(a,b,c,d),xx(a,b,c,d)] -> comp[xx(a,b,c,d),yy(a,b,c,d)] ]
"""


class Checker:
    def __init__(self, binary, folder):
        self.binary = binary
        self.folder = folder
        (folder / 'Heads.catt').write_text(HEADS)
        (folder / 'Rules.catt').write_text('import Heads\n' + RULES)
        (folder / 'RawRules.catt').write_text('import Heads\n' + RAW_RULES)

    def query(self, code, mode, module='Heads'):
        path = self.folder / 'Check.catt'
        path.write_text(f'import {module}\n{code}\n')
        return run(self.binary, self.folder, path.name, mode)

    def definitions(self, code, mode, module='Heads'):
        accepted(self.query(code, mode, module), 'Check.catt', re.findall(r'^def (\w+)', code, re.M))

    def equality(self, u, v, context, mode, equal, module='Heads'):
        out = self.query(f'assert {u} = {v} in {context}', mode, module)
        if equal:
            accepted(out, 'Check.catt', [])
            assert 'are equal' in out
        else:
            assert 'Error: Assertion failed:' in out and 'are not equal' in out


def positive_support(check):
    track = 'comp[swap(a,b),unswap(a,b)]'
    base = f'{SCALARS} (A : {track} -> {track})'
    nested, flat = 'h(h(A,A),A)', 'grouped(A,A,A)'
    ctx = f'{base} (z : {flat} -> {flat}) (k : z -> z)'
    l, r = 'flat(A,A,A)', 'unflat(A,A,A)'
    fitted = f'comp[{l},z,{r}]'
    higher = f'comp[{l},[k],{r}]'
    verify = (f'def five {ctx} : {nested} -> {nested} = {fitted}\n'
              f'def six {ctx} : {fitted} -> {fitted} = {higher}')
    for mode in ((), WIDTH_ONE):
        check.definitions(verify, mode)
    for name, boundary, var in [('directfive', nested, 'z'), ('directsix', fitted, 'k')]:
        code = f'def {name} {ctx} : {boundary} -> {boundary} = {var}'
        rejected(check.query(code, WIDTH_ONE), 'Check.catt', name)
        check.definitions(code, FULL)
    for value, desired, wrong in [(fitted, 'z', f'id({flat})'), (higher, 'k', 'id(z)')]:
        check.equality(value, desired, ctx, FULL, True)
        check.equality(value, wrong, ctx, FULL, False)
    print('Raw and width-one fits in degrees five and six; both full classes distinguished')


def erasing_at_three_cuts(check):
    obj = 'grouped(a,b,a)'
    ctx = f'{SCALARS} (w : {obj} -> {obj}) (Z : w -> w)'
    silent = 'comp[unflat(a,b,a),flat(a,b,a)]'
    for length in (2, 3, 5, 11):
        word = 'comp[' + ','.join(['Z'] * length) + ']'
        atom = f'comp[[{word}],{silent}]'
        check.equality(atom, word, ctx, FULL, True)
        out = check.query(f'normalise {atom} in {ctx}', WIDTH_ONE)
        accepted(out, 'Check.catt', [])
        normal, = re.findall(r'Normal form:\s*(.*?)\s+has type:', out, re.S)
        # Two unary spatial levels; at the third level the temporal packet
        # has a stationary neighbour. A temporal four-word has three unary levels.
        spelling = ''.join(normal.split())
        assert spelling.startswith('comp[[[[' + ','.join(['Z'] * length) + '],coh[')
    print('One threefold-hom generator projects to temporal words of lengths 2, 3, 5, 11')


def coloured_paths(check):
    args = '(a,b,c)'
    edges = [('arrive', 0, 2, 'in'), ('arrive_other', 1, 2, 'in'),
             ('leave', 2, 0, 'out'), ('leave_other', 2, 1, 'out')]
    boundary = ['one'+args, 'two'+args, 'dest'+args]
    for u, v in [('one','two'), ('arrive','arrive_other'), ('leave','leave_other')]:
        check.equality(u+args, v+args, ROW, FULL, True, 'Rules')
    check.equality('one'+args, 'two'+args, ROW, WIDTH_ONE, False, 'Rules')
    check.equality('one'+args, 'dest'+args, ROW, FULL, False, 'Rules')
    goal = ['in','out','in','out']
    readings = []
    for chosen in product(edges, repeat=len(goal)):
        if [edge[3] for edge in chosen] != goal:
            continue
        if any(l[2] != r[1] for l, r in zip(chosen, chosen[1:])):
            continue
        readings.append((chosen[0][1], chosen[-1][2],
                         'comp[' + ','.join(edge[0]+args for edge in chosen) + ']'))
    assert len(readings) == 8
    for i, (s, t, expr) in enumerate(readings):
        check.definitions(f'def word{i} {ROW} : {boundary[s]} -> {boundary[t]} = {expr}',
                          WIDTH_ONE, 'Rules')
        check.equality(expr, readings[0][2], ROW, FULL, True, 'Rules')
    print('All eight incidence-compatible colourings of a four-letter upper word checked')


def rewriting(check):
    args, row = '(a,b,c,d)', '[[a],[b],[c],[d]]'
    x, y, rel = (name+args for name in ('xx','yy','rule'))
    xy, yx = f'comp[{x},{y}]', f'comp[{y},{x}]'
    fwd = f'comp[comp[{x},[{rel}]],comp[[{rel}],{x}]]'
    check.definitions(f'def sort {row} : comp[{x},{x},{y}] -> comp[{y},{x},{x}] = {fwd}',
                      WIDTH_ONE, 'RawRules')
    for mode in ((), WIDTH_ONE):
        check.definitions(f'def old_rule {row} : {xy} -> {yx} = {rel}', mode, 'RawRules')
        check.definitions(f'def extra {row} : {yx} -> {xy} = unrestricted_back{args}',
                          mode, 'RawRules')
    check.equality(rel, 'id(id(initial(a,b,c,d)))', row, FULL, True, 'RawRules')
    check.equality(xy, yx, row, WIDTH_ONE, False, 'RawRules')

    @cache
    def closure(word, before, after):
        result = {word}
        for i in range(len(word)-len(before)+1):
            if word.startswith(before, i):
                result.update(closure(word[:i]+after+word[i+len(before):], before, after))
        return result

    def encode(w):
        return ''.join('pr' if ch == 'x' else 'qs' for ch in w)

    count = 0
    for n in range(7):
        for w in map(''.join, product('xy', repeat=n)):
            assert {encode(v) for v in closure(w, 'xy','yx')} == closure(encode(w),'prqs','qspr')
            count += 1
    print(f'{count} words checked against their typed path encodings; the ambient reverse also types')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('binary', type=Path)
    args = parser.parse_args()
    with TemporaryDirectory() as temp:
        checker = Checker(args.binary.resolve(), Path(temp))
        positive_support(checker)
        erasing_at_three_cuts(checker)
        coloured_paths(checker)
        rewriting(checker)
