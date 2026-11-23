"""Reconstruct raw higher cells from one face under a fold of computads."""
import argparse
from collections import Counter
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, check_ctx, comp2, disc_tree, glue_tree, infer,
                  maximal_vars, ps_boundary_vars, sub_from, subst_tm, subst_ty,
                  tdim, tdim_tm, tree_ctx, v)
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, rejected, run


def face(ty, rank, side):
    while tdim(ty) > rank:
        ty = ty[1]
    assert tdim(ty) == rank
    return ty[side]


def split(arity, ctx, pattern, actual, labels):
    """Read a partial globular tuple from a raw instance on its support."""
    if pattern[0] == 'v':
        index = pattern[1]
        if index in labels:
            assert labels[index] == actual
            return
        labels[index] = actual
        decl, value_type = arity[index], infer(ctx, actual)
        while decl != STAR:
            for side in (2, 3):
                split(arity, ctx, decl[side], value_type[side], labels)
            decl, value_type = decl[1], value_type[1]
        assert value_type == STAR
        return
    assert pattern[:3] == actual[:3]
    for inner, value in zip(pattern[3], actual[3], strict=True):
        split(arity, ctx, inner, value, labels)


def lift(ctx, base, fold, term, given, rank, side):
    """Use the folded head and the chosen face as the only reconstruction data."""
    term_type = infer(base, term)
    assert subst_tm(given, fold) == face(term_type, rank, side)
    tag, arity, decl, args = term
    assert tag == 'coh'
    labels = {}
    split(arity, ctx, face(decl, rank, side), given, labels)
    assert set(labels) == ps_boundary_vars(arity, rank, '-' if side == 2 else '+')
    todo = {i for i, ty in enumerate(arity) if tdim(ty) + 1 > rank}
    while todo:
        ready = [i for i in sorted(todo) if face(arity[i], rank, side)[1] in labels]
        assert ready
        for i in ready:
            at = labels[face(arity[i], rank, side)[1]]
            value = lift(ctx, base, fold, args[i], at, rank, side)
            split(arity, ctx, v(i), value, labels)
        todo.difference_update(ready)
    assert len(labels) == len(arity)
    lifted = (tag, arity, decl, tuple(labels[i] for i in range(len(arity))))
    assert face(infer(ctx, lifted), rank, side) == given
    assert subst_tm(lifted, fold) == term
    return lifted


def disc_head(ctx, term):
    dim = tdim_tm(ctx, term)
    disc = tree_ctx(disc_tree(dim))
    top, = maximal_vars(disc)
    return ('coh', disc, disc[top], sub_from(disc, ctx, {top: term}))


def folded_contexts():
    # Two adjacent rewriting steps. Each rewrites a two-edge path to one edge.
    # Both the intermediate vertices and all edge names coalesce downstairs.
    ctx = (STAR,) * 5
    edges = ((0, 1), (1, 2), (0, 2), (2, 3), (3, 4), (2, 4))
    ctx += tuple(arr(STAR, v(x), v(y)) for x, y in edges)
    step_types = [arr(infer(ctx, v(end)), comp2(ctx, 0, v(a), v(b)), v(end))
                  for a, b, end in ((5, 6, 7), (8, 9, 10))]
    ctx += (step_types[0], step_types[0], step_types[1], step_types[1])
    edge = arr(STAR, v(0), v(0))
    base = (STAR, edge)
    step = arr(edge, comp2(base, 0, v(1), v(1)), v(1))
    base += (step, step)  # One generator outside the image.
    fold = (v(0),) * 5 + (v(1),) * 6 + (v(2),) * 4
    check_ctx(ctx)
    check_ctx(base)
    assert all(subst_ty(ty, fold) == infer(base, image)
               for ty, image in zip(ctx, fold, strict=True))
    return ctx, base, fold


def check_published(checkout):
    binary = checkout / 'target/release/catt_strict'
    path = 'comp[f,g]'
    base = f'(x : *) (y : *) (z : *) (f : x -> y) (g : y -> z) (a : {path} -> {path}) (b : {path} -> {path})'
    padded = f'comp[id({path}),a]'
    attached = f'{base} (k : {padded} -> b)'
    folded = '(x : *) (f : x -> x) (a : comp[f,f] -> comp[f,f])'
    with TemporaryDirectory() as directory:
        folder = Path(directory)
        (folder / 'Lift.catt').write_text(f"""def flat {base} : comp[id({path}),a,id({path}),b] -> comp[a,b] = id(comp[a,b])
def fitted {attached} : a -> b = k
def marked {attached} : comp[id({padded}),k] -> k = id(k)
def folded {folded} (k : comp[id(comp[f,f]),a] -> a) = marked(x,x,x,f,f,a,a,k)
""")
        (folder / 'Order.catt').write_text(
            f'def wrong {base} : comp[id({path}),a,id({path}),b] -> comp[b,a] = id(comp[b,a])\n')
        (folder / 'Class.catt').write_text(
            f'def wrong {attached} (l : {padded} -> b) : comp[id({padded}),k] -> l = id(l)\n')
        # The terminal names of both paths coincide. Their intermediate
        # vertices and edge labels are independent in the universal context.
        generic = (f'(x : *) (y : *) (z : *) (t : *) (f : x -> y) (g : y -> z) '
                   f'(h : x -> t) (i : t -> z) (a : {path} -> comp[h,i]) '
                   f'(b : {path} -> comp[h,i]) (k : {padded} -> b)')
        raw = f"""def enter = coh [ x{{f}}y : f -> comp[id(x),f] ]
def solve {generic} : a -> b = comp[enter(a),k]
def at_fold {folded} (k : comp[id(comp[f,f]),a] -> a) : a -> a = solve(x,x,x,x,f,f,f,f,a,a,k)
"""
        (folder / 'Generic.catt').write_text(raw)
        (folder / 'Value.catt').write_text(
            f'import Generic\ndef value {generic} : solve(x,y,z,t,f,g,h,i,a,b,k) -> k = id(k)\n')
        accepted(run(binary, folder, 'Generic.catt'), 'Generic.catt', ['solve', 'at_fold'])
        rejected(run(binary, folder, 'Lift.catt'), 'Lift.catt', 'flat')
        for mode in ('--su', '--sua'):
            accepted(run(binary, folder, 'Lift.catt', [mode]), 'Lift.catt', ['flat', 'fitted', 'marked', 'folded'])
            accepted(run(binary, folder, 'Value.catt', [mode]), 'Value.catt', ['value'])
            for filename in ('Order.catt', 'Class.catt'):
                rejected(run(binary, folder, filename, [mode]), filename, 'wrong')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    parser.add_argument('--catt-strict', type=Path, help='built checkout of Rice’s checker')
    options = parser.parse_args()
    ctx, base, fold = folded_contexts()
    folded_identity = identity(base, v(2))
    assert fold[11] == fold[12]
    recovered_identity = lift(ctx, base, fold, folded_identity, v(11), 2, 2)
    assert infer(ctx, recovered_identity)[2:] == (v(11), v(11))
    assert infer(ctx, recovered_identity) != arr(ctx[11], v(11), v(12))
    pair = tree_ctx(glue_tree(2, 0, 2))
    early, late = temporal_words(pair, *map(v, maximal_vars(pair)), 0, 1)
    swap = head(pair, late, early)
    padded = comp2(pair, 2, swap, identity(pair, early))
    comparison = head(pair, swap, padded)
    # The disc contributes parallel transport slots joined by its top generator.
    # Composition contributes a transport string of length two.
    doubled = comp2(pair, 2, swap, head(pair, early, late))
    terms = [swap, doubled, disc_head(pair, comparison),
             disc_head(pair, identity(pair, comparison))]
    assignments = [sub_from(pair, ctx, dict(zip(maximal_vars(pair), (v(a), v(b)))))
                   for a in (11, 12) for b in (13, 14)]
    counts, emitter = Counter(), Emitter()
    for rank in (2, 3, 4):
        for example, generic in enumerate(terms):
            folded = subst_tm(subst_tm(generic, assignments[0]), fold)
            for variant, assignment in enumerate(assignments):
                original = subst_tm(generic, assignment)
                ty = infer(ctx, original)
                for side in (2, 3):
                    given = face(ty, rank, side)
                    recovered = lift(ctx, base, fold, folded, given, rank, side)
                    assert recovered == original
                    counts[rank] += 1
                if variant == 2 and example == 2:
                    emitter.check_type(f'lift{rank}', ctx, recovered, ty)
                    emitter.check_eq(f'fold{rank}', recovered, fold, folded)
        if rank != 4:
            ctx, base = susp_ctx(ctx), susp_ctx(base)
            pair = susp_ctx(pair)
            fold = (v(0), v(1)) + tuple(map(susp_tm, fold))
            terms = list(map(susp_tm, terms))
            assignments = [(v(0), v(1)) + tuple(map(susp_tm, tau)) for tau in assignments]
    if options.agda_dir:
        for suffix, kernel in [('Ordinary', 'CaTTExp.Pure'), ('Gray', 'CaTTExp.Gray.Pure')]:
            name = 'ComputadFold' + suffix
            module = emitter.module(name, __doc__).replace('open import CaTTExp.Pure', 'open import ' + kernel)
            (options.agda_dir / (name + '.agda')).write_text(module)
    print(', '.join(f'{count} lifts at rank {rank}' for rank, count in counts.items()))
    if options.catt_strict:
        check_published(options.catt_strict.resolve())
        print('Both published surfaces retained the input order and the chosen class above a folded attachment.')


if __name__ == '__main__':
    main()
