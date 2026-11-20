"""Generate the full-support CaTT four-cell of the unary-chart counterexample."""

import argparse
from pathlib import Path

from catt import arr, chain_tree, check_ctx, comp2, fv_tm, fv_ty, infer, tdim_tm, v
from emit_agda import Emitter
from relative_coherence_middle_wire import check_context, comparison


def four_cell():
    # Share the two-skeleton of the middle-wire example (four objects to beta_1).
    context = check_context()[:13]
    parallel = arr(infer(context, v(9)), v(9), v(10))
    context += (parallel, parallel)
    source, target = (comp2(context, 0, v(6), v(i)) for i in (11, 12))
    context += (arr(infer(context, source), source, target),)
    source, target = (comp2(context, 0, v(i), v(6)) for i in (13, 14))
    context += (arr(infer(context, source), source, target),)
    check_ctx(context)

    # Compose at the cut (f_1 g) h_0. Only the B row needs rebracketing.
    z_row = comp2(context, 0, v(16), v(7))
    b_row = comp2(context, 0, v(5), v(15))
    wires = [v(5), v(6), v(7)]
    common_cut = comp2(context, 0, comp2(context, 0, *wires[:2]), wires[2])
    actual_cut = comp2(context, 0, wires[0], comp2(context, 0, *wires[1:]))
    associator = comparison(context, chain_tree(3), wires, common_cut, actual_cut)
    witness = comp2(context, 1, z_row, comp2(context, 1, associator, b_row))
    assert tdim_tm(context, witness) == 4
    support = set(fv_tm(witness))
    for index in reversed(range(len(context))):
        if index in support:
            support.update(fv_ty(context[index]))
    assert support == set(range(len(context)))
    return context, witness


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    ctx, term = four_cell()
    print(f"Checked {len(ctx)} declarations and a full-support 4-cell")
    if args.agda:
        emitter = Emitter()
        emitter.check_typed("middle-wire-four-cell", ctx, term)
        args.agda.write_text(emitter.module(args.agda.stem, "A unary four-cell over a middle-wire chart."))
