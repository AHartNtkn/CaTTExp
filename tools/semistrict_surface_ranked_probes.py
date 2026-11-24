"""Check binary reassociations, pruning, and old-boundary fitting in Rice's checker."""
import argparse
from functools import cache
from itertools import combinations
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

from catt import (STAR, arr, comp2, infer, maximal_vars, ps_boundary_vars, ps_dim, restrict,
                  src, sub_from, subst_tm, tgt, tree_ctx, v)
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_globular_poles import fit
from semistrict_surface_insertion_cut import Assertions


HEADS = """
def forward = coh [[a,b,c] : comp[a,b,c] -> comp[a,comp[b,c]]]
def backward = coh [[a,b,c] : comp[a,comp[b,c]] -> comp[a,b,c]]
def rotate = coh [[a,b,c] : comp[comp[a,b],c] -> comp[a,comp[b,c]]]
def unrotate = coh [[a,b,c] : comp[a,comp[b,c]] -> comp[comp[a,b],c]]
"""
PATH = 'x{f}y{g}z{h}w'
LOOP = '(x : *) (f : x -> x)'


def composite(*terms):
    return 'comp[' + ','.join(terms) + ']'


def tower(context, labels, limit, start=1):
    for rank in range(start, limit+1):
        a, b, c = labels
        left = composite(composite(a, b), c)
        right = composite(a, composite(b, c))
        ternary = composite(a, b, c)
        arguments = '(' + ','.join(labels) + ')'
        round_trip = composite('rotate'+arguments, 'unrotate'+arguments)
        yield rank, f'assert {left} = {right} in {context}'
        yield rank, f'assert {round_trip} = id({left}) in {context}'
        yield 'insert', f'assert {ternary} = {right} in {context}'
        # All three of these comparison operands are weak raw terms.
        labels = ('forward'+arguments, 'backward'+arguments, 'forward'+arguments)


def masks():
    labels = ['f','g','h','k','l']
    vertices = list('uvwxyz')
    for size in range(6):
        for chosen in combinations(range(5), size):
            terms = []
            context = vertices[0]
            index = 0
            for i, name in enumerate(labels):
                if i in chosen:
                    terms.append(name)
                    index += 1
                    context += '{' + name + '}' + vertices[index]
                else:
                    terms.append(f'id({vertices[index]})')
            kept = [labels[i] for i in chosen]
            if not kept:
                normal = 'id(u)'
            else:
                normal = kept[-1]
                for item in reversed(kept[:-1]):
                    normal = composite(item, normal)
            # All prune to the same path up to two occupied slots. Beyond
            # two, the primitive head is still present even with top assoc.
            yield 0 if size <= 2 else 'insert', f'assert {composite(*terms)} = {normal} in {context}'
            # A genuinely left-nested head, including every empty-slot pattern.
            nested = terms[0]
            for item in terms[1:]:
                nested = composite(nested, item)
            yield 0 if size <= 2 else 1, f'assert {nested} = {normal} in {context}'


@cache
def bracketed_head(ctx, rank, left):
    height = ps_dim(ctx)
    if height == rank:
        a, b, c = map(v, maximal_vars(ctx))
        if left:
            return comp2(ctx, rank-1, comp2(ctx, rank-1, a, b), c)
        return comp2(ctx, rank-1, a, comp2(ctx, rank-1, b, c))
    faces = []
    for sign in ('-', '+'):
        boundary, inclusion = restrict(ctx, ps_boundary_vars(ctx, height-1, sign))
        faces.append(subst_tm(bracketed_head(boundary, rank, left), inclusion))
    return head(ctx, *faces)


def scalar_cases(code, height, rank, emitter):
    arity = tree_ctx(string_tree(rank-1, [height]*3))
    left = bracketed_head(arity, rank, True)
    right = bracketed_head(arity, rank, False)
    fitted = fit(arity, right, src(arity, left), tgt(arity, left))
    forward = head(arity, left, fitted)
    backward = head(arity, fitted, left)
    base = v(0)
    pole = 'x0'
    for _ in range(height-1):
        base = ident((STAR,), base)
        pole = f'id({pole})'
    scalar = (STAR, infer((STAR,), ident((STAR,), base)))
    sigma = sub_from(arity, scalar, dict.fromkeys(maximal_vars(arity), v(1)))
    context = f'(x0 : *) (x1 : {pole} -> {pole})'
    u, v_term, other = (subst_tm(cell, sigma) for cell in (left, fitted, right))
    up, down = (subst_tm(cell, sigma) for cell in (forward, backward))
    a, b = code.term(u), code.term(v_term)
    yield rank, f'assert {a} = {b} in {context}'
    yield rank, f'assert comp[{code.term(up)},{code.term(down)}] = id({a}) in {context}'
    yield 0, f'assert {b} = {code.term(other)} in {context}'
    for i, (cell, start, end) in enumerate(((up, u, v_term), (down, v_term, u))):
        name = f'raw{height}r{rank}f{i}'
        if emitter is not None:
            emitter.check_type(name, scalar, cell, arr(infer(scalar, start), start, end))
        yield 'raw', (f'def {name} {context} : {code.term(start)} -> {code.term(end)}'
                      f' = {code.term(cell)}')


def checks(binary, limit, agda_dir):
    emitter = Emitter() if agda_dir else None
    cases = list(masks()) + list(tower(PATH, ('f','g','h'), limit))
    cases += list(tower(LOOP, ('f',)*3, limit))
    for rank in range(1, limit+1):
        ctx = 'u{a}v{b}m{c}w'
        for i in range(rank-1):
            ctx = f's{i}{{{ctx}}}t{i}'
        cases.append((rank, f'assert comp[comp[a,b],id(m),c] = comp[a,comp[b,c]] in {ctx}'))

    code = Assertions()
    raw_tests = []
    for height in range(2, limit+1):
        pole = 'x'
        for _ in range(height-1):
            pole = f'id({pole})'
        scalar = f'(x : *) (a : {pole} -> {pole})'
        cases.extend(tower(scalar, ('a',)*3, limit, start=height))
        for rank in range(1, height):
            for law, query in scalar_cases(code, height, rank, emitter):
                if law == 'raw':
                    raw_tests.append(query)
                else:
                    cases.append((law, query))
    if agda_dir:
        agda_dir.mkdir(parents=True, exist_ok=True)
        module = 'ScalarBracketingComparisons'
        (agda_dir/(module+'.agda')).write_text(emitter.module(module, 'Both literal scalar boundaries.'))
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder/'heads.catt').write_text(HEADS+'\n'.join(code.commands)+'\n'+'\n'.join(raw_tests)+'\n')
        names = []
        for i, (_, assertion) in enumerate(cases):
            name = f'case{i}.catt'
            (folder/name).write_text(assertion+'\n')
            names.append(name)
        bindings = '(x : *) (f : x -> x) (p : comp[comp[f,f],f] -> comp[comp[f,f],f])'
        target = 'comp[f,comp[f,f]]'
        declarations = [
            ('fitted', 'comp[unrotate(f,f,f),p,rotate(f,f,f)]'),
            ('direct', 'p'),
        ]
        for name, body in declarations:
            (folder/(name+'.catt')).write_text(f'def {name} {bindings} : {target} -> {target} = {body}\n')
        for flags, first in [([], None), (['--su'], limit+1), (['--sua'], 0)] + [
                (['--top-assoc-from', str(r)], r) for r in range(1, limit+2)]:
            inputs = (names if first is not None else []) + ['fitted.catt', 'direct.catt']
            proc = subprocess.run([binary, *flags, 'heads.catt', *inputs], cwd=folder,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=True)
            log = re.sub(r'\x1b\[[0-9;]*m', '', proc.stdout)
            chunks = re.split(r'^Importing (\w+\.catt)$', log, flags=re.M)
            assert chunks[1::2] == ['heads.catt', *inputs]
            sections = dict(zip(chunks[1::2], chunks[2::2], strict=True))
            for name in ['heads.catt', 'fitted.catt']:
                assert 'Finished importing '+name in sections[name], sections[name][-1500:]
            direct = sections['direct.catt']
            if first in (0,1):
                assert 'Finished importing direct.catt' in direct
            else:
                assert 'Error:' in direct and 'has type' in direct, direct[-1500:]
            hits = 0
            for name, (law, assertion) in zip(names if first is not None else [], cases):
                expected = law == 0 or first == 0 or (isinstance(law, int) and law >= first)
                message = sections[name]
                if expected:
                    assert 'are equal' in message and 'Error:' not in message, (flags, assertion, message[-1500:])
                    hits += 1
                else:
                    assert 'are not equal' in message and 'Error: Assertion failed' in message, (flags, assertion, message[-1500:])
            print(f'{" ".join(flags) or "weak"}: {hits}/{len(inputs)-2} equal, raw correction accepted, '
                  f'direct conversion {first in (0,1)}', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('binary', type=Path)
    parser.add_argument('--ranks', type=int, default=4)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    if args.ranks < 1:
        parser.error('--ranks must be positive')
    checks(args.binary.resolve(), args.ranks, args.agda_dir)
