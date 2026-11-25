"""Construct higher mixed naturality disks and read the planar puncture circuit."""

from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, comp2, glue_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, tdim, tdim_tm, tgt, tree_ctx, tree_of, v)
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, run
from semistrict_surface_mixed_winding import Reading, check_mixed_splices, evaluate


def boundary(ctx, term, rank, face):
    while tdim_tm(ctx, term) > rank:
        term = face(ctx, term)
    return term


@lru_cache(None)
def disk(rank, left):
    ctx = tree_ctx(glue_tree(rank, 0, 2) if left else glue_tree(2, 0, rank))
    first, second = map(v, maximal_vars(ctx))
    change, fixed = (first, second) if left else (second, first)
    s = boundary(ctx, change, 1, src)
    t = boundary(ctx, change, 1, tgt)

    def beside(a, b):
        return comp2(ctx, 0, a, b)

    if left:
        early = comp2(ctx, 1, beside(change, src(ctx, fixed)), beside(t, fixed))
        late = comp2(ctx, 1, beside(s, fixed), beside(change, tgt(ctx, fixed)))
    else:
        early = comp2(ctx, 1, beside(fixed, s), beside(tgt(ctx, fixed), change))
        late = comp2(ctx, 1, beside(src(ctx, fixed), change), beside(fixed, t))
    for level in range(2, rank):
        arity, lower = disk(level, left)
        def pad(face):
            value = boundary(ctx, change, level, face)
            args = (value, fixed) if left else (fixed, value)
            return subst_tm(lower, sub_from(arity, ctx, dict(zip(maximal_vars(arity), args, strict=True))))
        early = comp2(ctx, level, early, pad(tgt))
        late = comp2(ctx, level, pad(src), late)
    return ctx, head(ctx, early, late)


def evaluate_circuit(rank):
    ctx = (STAR,)
    pole = v(0)
    for _ in range(rank-1):
        pole = identity(ctx, pole)
    line = identity(ctx, v(0))
    ctx += (arr(infer(ctx, line), line, line), arr(infer(ctx, pole), pole, pole))
    cycle = Counter()
    for left in (True, False):
        arity, generic = disk(rank, left)
        args = (v(2), v(1)) if left else (v(1), v(2))
        specialized = subst_tm(generic, sub_from(arity, ctx, dict(zip(maximal_vars(arity), args, strict=True))))
        labels = [Reading(), Reading(mass=1), Reading(charge=1)]
        endpoints = [evaluate(face, labels, rank).vertices for face in infer(ctx, specialized)[2:]]
        side = int(not left)
        assert endpoints == [Counter({(1, side): 1}), Counter({(1, 1-side): 1})]
        arc = evaluate(specialized, labels, rank).edges
        assert arc == Counter({((0, side), (1, side)): -1, ((0, side), (1, 1-side)): 1})
        cycle.update(arc)
    assert cycle == Counter({((0, i), (1, j)): (1 if i != j else -1) for i in range(2) for j in range(2)})


def tree_names(tree):
    index = 1
    def visit(node, start):
        nonlocal index
        result = f'x{start}'
        for child in node:
            target = index
            index += 2
            result += '{' + visit(child, target+1) + '}' + f'x{target}'
        return result
    return visit(tree, 0)


def rice_source(max_rank):
    named = {}
    declarations = []
    def expression(term):
        if term[0] == 'v':
            return f'x{term[1]}'
        _, arity, ty, sub = term
        peaks = maximal_vars(arity)
        args = [expression(sub[i]) for i in peaks]
        name = named.get((arity, ty))
        if name:
            return name + '(' + ','.join(args) + ')'
        node = tree_of(arity)
        cut = 0
        while len(node) == 1:
            node, = node
            cut += 1
        assert len(node) == len(args) == 2
        depths = [tdim(arity[i])-cut for i in peaks]
        return 'comp[' + ','.join('['*d+a+']'*d for a, d in zip(args, depths, strict=True)) + ']'
    for rank in range(2, max_rank+1):
        for left in (True, False):
            arity, generic = disk(rank, left)
            if (arity, generic[2]) in named:
                continue
            name = ('left' if left else 'right') + str(rank)
            start, end = [expression(face) for face in generic[2][2:]]
            tree = tree_names(tree_of(arity))
            declarations.append(f'def {name} = coh [ {tree} : {start} -> {end} ]')
            named[arity, generic[2]] = name
        if rank >= 3:
            pole = 'id('* (rank-1) + 'p' + ')'* (rank-1)
            base = 'comp[' + '['*(rank-2) + 'q' + ']'*(rank-2) + ',b]'
            declarations.append(f'def circuit{rank} (p : *) (q : {pole} -> {pole}) (b : id(p) -> id(p))'
                                f' : {base} -> {base} = comp[left{rank}(q,b),right{rank}(b,q)]')
    return '\n\n'.join(declarations) + '\n'


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rank', type=int, default=4, help='largest moving rank')
    parser.add_argument('--checkout', type=Path, help="Rice's catt-strict checkout with a release build")
    args = parser.parse_args()
    if args.rank < 3:
        parser.error('the moving rank must be at least three')
    for rank in range(3, args.rank+1):
        evaluate_circuit(rank)
        print(f'Moving rank {rank}: both raw specialized disks read the two arcs of a primitive winding.')
        if rank in (4, 5):
            counts = check_mixed_splices(rank)
            print(f"Six-edge splices at rank {rank}: {counts['exterior']} exterior and {counts['interior']} interior pairs.")
    if args.checkout:
        executable = args.checkout.resolve() / 'target/release/catt_strict'
        with TemporaryDirectory() as tmp:
            folder = Path(tmp)
            code = rice_source(args.rank)
            heads = [definition for definition in code.strip().split('\n\n') if not definition.startswith('def circuit')]
            (folder / 'HigherHeads.catt').write_text('\n\n'.join(heads) + '\n')
            raw_output = run(executable, folder, 'HigherHeads.catt')
            accepted(raw_output, 'HigherHeads.catt', [])
            for definition in heads:
                assert f'Inferring {definition.split()[1]}\n' in raw_output
            print(f'Rice checked every generic naturality head through rank {args.rank} in raw CaTT.')
            (folder / 'HigherWinding.catt').write_text(code)
            for mode in ('--su', '--sua'):
                names = [f'circuit{i}' for i in range(3, args.rank+1)]
                accepted(run(executable, folder, 'HigherWinding.catt', [mode]), 'HigherWinding.catt', names)
                print(f'Rice checked the closed circuits through moving rank {args.rank} in {mode} mode.')
