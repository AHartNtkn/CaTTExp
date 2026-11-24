"""Check first-rank spatial factorizations with a nonstandard transported head."""
from argparse import ArgumentParser
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (comp2, glue_tree, maximal_vars, src, sub_from, subst_tm,
                  subst_ty, tdim, tgt, tree_ctx, v)
from ct_suspension import ident
from relative_coherence_exchange_faces import head
from semistrict_surface_elementary_insertions import exterior
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_insertion_cut import Assertions, shape, variables


def transported(tree, ty, mapping):
    ctx = tree_ctx(tree)
    return ('coh', ctx, subst_ty(ty, mapping), variables(ctx))


def diagram(rank):
    pair = glue_tree(rank, 0, rank)
    base = tree_ctx(pair)
    a, b = map(v, maximal_vars(base))
    s, t = src(base, a), src(base, b)
    left_step = comp2(base, 0, s, src(base, t))
    right_step = comp2(base, 0, tgt(base, s), t)
    initial = comp2(base, rank-2, left_step, right_step)
    final = comp2(base, 0, tgt(base, a), tgt(base, b))
    tag = head(base, initial, final)
    left, expand_left = exterior(pair, (0,), pair)
    right, expand_right = exterior(pair, (1,), pair)
    full, finish_left = exterior(left, (2,), pair)
    same, finish_right = exterior(right, (0,), pair)
    assert full == same
    mapping = tuple(subst_tm(x, finish_left) for x in expand_left)
    assert mapping == tuple(subst_tm(x, finish_right) for x in expand_right)
    first = subst_tm(tag, mapping)
    last = transported(full, tag[2], mapping)
    left_head = transported(left, tag[2], expand_left)
    right_head = transported(right, tag[2], expand_right)
    mid_left = subst_tm(left_head, finish_left)
    mid_right = subst_tm(right_head, finish_right)
    ctx = tree_ctx(full)
    u = comp2(ctx, rank, subst_tm(head(tree_ctx(left), subst_tm(tag, expand_left), left_head),
                                  finish_left), head(ctx, mid_left, last))
    w = comp2(ctx, rank, subst_tm(head(tree_ctx(right), subst_tm(tag, expand_right), right_head),
                                  finish_right), head(ctx, mid_right, last))
    assert src(ctx, u) == src(ctx, w) == first
    assert tgt(ctx, u) == tgt(ctx, w) == last

    # Collapse the middle pair, retaining its first disc, then re-expand it.
    three = tree_ctx(left)
    i, j, k = map(v, maximal_vars(three))
    pole = j
    for _ in range(rank):
        pole = tgt(three, pole)
    stationary = pole
    for _ in range(rank):
        stationary = ident(three, stationary)
    collapse = sub_from(ctx, three, dict(zip(maximal_vars(ctx), [i, j, stationary, k], strict=True)))
    result, section = exterior(left, (1,), pair)
    assert result == full
    wrong = subst_tm(subst_tm(src(ctx, last), collapse), section)
    return ctx, (first, mid_left, mid_right, last), wrong, u, w


def check_rectangle(binary, folder, rank):
    def row(depth, *windows):
        return '[' + ','.join('['*depth + window + ']'*depth for window in windows) + ']'

    two = row(rank-1, 'a', 'b')
    three = row(rank-1, 'a', 'b', 'c')
    inputs = row(rank, 'a,b', 'c')
    ends = row(rank, 'l', 'r')
    expanded = row(rank, 'l,a,r,s,b,t', 'u,c,v')
    rules = [
        f'def h {two} = comp{two}',
        f'def tri {three} = comp{three}',
        f'def flat = coh [ {three} : h(h(a,b),c) -> tri(a,b,c) ]',
        f'def unflat = coh [ {three} : tri(a,b,c) -> h(h(a,b),c) ]',
        f'def top {inputs} = comp{inputs}',
        f'def ends {ends} = comp{ends}',
        f'def triples {expanded} = top(comp[l,a,r],comp[s,b,t],comp[u,c,v])',
        f'def around {expanded} = comp[ends(l,u),top(comp[a,comp[r,s]],b,c),ends(t,v)]',
        f'def rectangle = coh [ {expanded} : triples(l,a,r,s,b,t,u,c,v)'
        ' -> around(l,a,r,s,b,t,u,c,v) ]',
    ]
    # The two top labels have a composite and an identity as attaching face.
    telescope = '(x0 : *)' + ''.join(f' (x{i} : x{i-1} -> x{i-1})' for i in range(1, rank))
    path, unit = f'comp[x{rank-1},x{rank-1}]', f'id(x{rank-2})'
    ctx = (f'{telescope} (a : {path} -> {path}) (b : {unit} -> {unit})'
           ' (y : tri(a,b,a) -> tri(a,b,a)) (z : tri(a,b,a) -> tri(a,b,a))')
    forward, back = 'flat(a,b,a)', 'unflat(a,b,a)'
    args = f'({forward},y,{back},{forward},z,{back},{forward},y,{back})'
    rect = f'rectangle{args}'
    rules.append(f'def compared {ctx} : triples{args} -> around{args} = {rect}')
    (folder / 'Rectangle.catt').write_text('\n'.join(rules) + '\n')
    (folder / 'RectClass.catt').write_text(
        f'import Rectangle\ndef rectclass {ctx} : {rect} -> id(top(y,z,y)) = id({rect})\n')
    accepted(run(binary, folder, 'Rectangle.catt', ['--insertion-width', str(rank-1)]),
             'Rectangle.catt', ['compared'])
    for mode in (['--insertion-width', str(rank)], ['--sua']):
        accepted(run(binary, folder, 'RectClass.catt', mode), 'RectClass.catt', ['rectclass'])


def check(binary, folder, rank):
    ctx, readings, wrong, u, w = diagram(rank)
    code = Assertions()
    names = [code.term(t) for t in readings]
    actual = code.term(src(ctx, readings[-1]))
    other = code.term(wrong)
    tree = shape(ctx)
    tower = '(x0 : *)' + ''.join(f' (x{i} : x{i-1} -> x{i-1})' for i in range(1, rank+1))
    labels = tuple(v(tdim(ty)+1) for ty in ctx)

    def at_tower(t):
        return code.term(subst_tm(t, labels))

    source, target = at_tower(u), at_tower(w)
    forward, back = (at_tower(head(ctx, x, y)) for x, y in ((u, w), (w, u)))
    parametrized = f'{tower} (z : {target} -> {target})'
    fitted = f'comp[{forward},z,{back}]'

    def file(name, definitions):
        (folder / name).write_text('import Heads\n' + '\n'.join(definitions) + '\n')

    (folder / 'Heads.catt').write_text('\n'.join(code.commands) + '\n')
    file('Fit.catt', [f'def fit {parametrized} : {source} -> {source} = {fitted}'])
    file('Direct.catt', [f'def direct {parametrized} : {source} -> {source} = z'])
    file('Class.catt', [f'def same {parametrized} : {fitted} -> z = id(z)'])
    file('Order.catt', [f'def wrong {parametrized} : {fitted} -> id({source}) = id({fitted})'])
    file('Nondescending.catt', [f'assert {actual} = {other} in {tree}'])
    for mode, count in ((['--insertion-width', str(rank-1)], 4),
                        (['--insertion-width', str(rank)], 1), (['--sua'], 1)):
        for left, right in combinations(names, 2):
            file('Pair.catt', [f'assert {left} = {right} in {tree}'])
            out = run(binary, folder, 'Pair.catt', mode)
            if count == 1:
                accepted(out, 'Pair.catt', [])
                assert 'are equal' in out
            else:
                assert 'Error: Assertion failed:' in out and 'are not equal' in out
        negative = run(binary, folder, 'Nondescending.catt', mode)
        assert 'Error: Assertion failed:' in negative and 'are not equal' in negative
        accepted(run(binary, folder, 'Fit.catt', mode), 'Fit.catt', ['fit'])
        direct = run(binary, folder, 'Direct.catt', mode)
        if count == 1:
            accepted(direct, 'Direct.catt', ['direct'])
            accepted(run(binary, folder, 'Class.catt', mode), 'Class.catt', ['same'])
            rejected(run(binary, folder, 'Order.catt', mode), 'Order.catt', 'wrong')
        else:
            rejected(direct, 'Direct.catt', 'direct')
    check_rectangle(binary, folder, rank)
    print(f'Rank {rank}: shared-seam rectangle, four lower readings, one upper class, forbidden middle block, '
          f'and a specified degree-{rank+2} generator fitted at width {rank-1}')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('binary', type=Path)
    parser.add_argument('--max-rank', type=int, default=5)
    args = parser.parse_args()
    with TemporaryDirectory() as temp:
        for rank in range(3, args.max_rank+1):
            check(args.binary.resolve(), Path(temp), rank)
