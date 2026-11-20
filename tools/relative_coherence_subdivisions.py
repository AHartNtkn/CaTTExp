"""Strict carriers and raw exchange paths for independent changes followed by fusion."""

from argparse import ArgumentParser
from itertools import combinations
from pathlib import Path

from catt import (STAR, arr, comp2, glue_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, tgt, tree_ctx, v)
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_chart_paths import two_triangles
from relative_coherence_exchange_faces import head


def fusion_charts(lanes):
    # A nontrivial intermediate state is a nonempty set of finished changes.
    # The final fusion has not yet happened, including in the all-finished state.
    full = (1 << lanes) - 1
    chains = set()

    def extend(chain):
        for a in range(1, full + 1):
            if not chain or (chain[-1] != a and chain[-1] & a == chain[-1]):
                step = chain + (a,)
                chains.add(step)
                extend(step)

    extend(())
    for chain in chains:
        upper = chain if chain[-1] == full else chain + (full,)
        assert upper in chains and (full,) in chains and set(chain) <= set(upper)
        for k in range(1, len(chain) + 1):
            for sub in combinations(chain, k):
                upper_sub = sub if sub[-1] == full else sub + (full,)
                assert sub in chains and set(upper_sub) <= set(upper)
        # Strict image of idle repetitions has the original least carrier.
        for idx in range(len(chain)):
            repeated = chain[:idx] + (chain[idx],) + chain[idx:]
            assert tuple(dict.fromkeys(repeated)) == chain
    # Incompatible one-event states prohibit a greatest subdivision.
    assert not any(1 in chain and 2 in chain for chain in chains)
    return len(chains)


def check_exchange(ctx, atoms, fusion, rank, emitter):
    cut = rank - 2
    chart = tree_ctx(glue_tree(rank, cut, rank))
    a, b = (v(i) for i in maximal_vars(chart))
    direct = comp2(chart, cut, a, b)
    lr = comp2(chart, rank - 1, comp2(chart, cut, a, src(chart, b)),
               comp2(chart, cut, tgt(chart, a), b))
    rl = comp2(chart, rank - 1, comp2(chart, cut, src(chart, a), b),
               comp2(chart, cut, a, tgt(chart, b)))
    one = head(chart, lr, rl)
    via = comp2(chart, rank, head(chart, lr, direct), head(chart, direct, rl))
    change = head(chart, one, via)
    sub = sub_from(chart, ctx, dict(zip(maximal_vars(chart), atoms)))
    source = comp2(ctx, rank - 1, subst_tm(one, sub), fusion)
    target = comp2(ctx, rank - 1, subst_tm(via, sub), fusion)
    homotopy = comp2(ctx, rank - 1, subst_tm(change, sub), fusion)
    expected = arr(infer(ctx, source), source, target)
    assert source != target and infer(ctx, homotopy) == expected
    emitter.check_type(f'fusion-{rank}', ctx, homotopy, expected)
    emitter.check_typed(f'fusion-{rank}', ctx, homotopy)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    counts = [fusion_charts(k) for k in range(2, 6)]
    ctx, atoms = two_triangles()
    c = comp2(ctx, 0, *atoms)
    end = v(len(ctx))
    ctx += (arr(STAR, v(0), v(4)),)
    fusion = v(len(ctx))
    ctx += (arr(infer(ctx, end), tgt(ctx, c), end),)
    emitter = Emitter()
    for rank in (2, 3, 4):
        check_exchange(ctx, atoms, fusion, rank, emitter)
        ctx, atoms, fusion = susp_ctx(ctx), [susp_tm(a) for a in atoms], susp_tm(fusion)
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Subdivisions before a common fusion.'))
    print(f'Strict subdivisions for two through five lanes: {counts}; three raw exchanges checked')
