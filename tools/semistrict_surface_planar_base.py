"""Check the rank-five transport and strict-unit braid calculations in Response 26."""
import argparse
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from catt import (STAR, arr, check_ctx, comp2, glue_tree, infer, maximal_vars,
                  sub_from, subst_tm, subst_ty, tree_ctx, v)
from catt_unit_ordered_exchange import temporal_words
from emit_agda import Emitter
from rc_oracle import _top
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity


def folded_transport(emitter):
    pair = tree_ctx(glue_tree(2, 0, 2))
    slots = maximal_vars(pair)
    early, late = temporal_words(pair, *map(v, slots), 0, 1)
    swap, reverse = head(pair, early, late), head(pair, late, early)
    circuit = comp2(pair, 2, swap, reverse)
    stationary = identity(pair, early)
    enter, leave = head(pair, stationary, circuit), head(pair, circuit, stationary)
    unit_c = identity(pair, circuit)
    unit_s = identity(pair, stationary)
    generic = pair + (arr(infer(pair, unit_c), unit_c, unit_c),)
    h = v(len(pair))
    moved = comp2(generic, 3, comp2(generic, 3, enter, h), leave)
    moved_ty = infer(generic, moved)
    assert moved_ty[2] == moved_ty[3] and moved_ty[2] != unit_s
    before, after = head(pair, unit_s, moved_ty[2]), head(pair, moved_ty[3], unit_s)
    fitted = comp2(generic, 4, comp2(generic, 4, before, moved), after)

    unit_x = identity((STAR,), v(0))
    scalar = (STAR, arr(infer((STAR,), unit_x), unit_x, unit_x))
    fold = sub_from(pair, scalar, {i: v(1) for i in slots})
    assert subst_tm(early, fold) != subst_tm(late, fold)
    ctx = scalar + (subst_ty(generic[-1], fold),)
    check_ctx(ctx)
    answer = subst_tm(fitted, (*fold, v(2)))
    expected = subst_ty(arr(infer(pair, unit_s), unit_s, unit_s), fold)
    assert ctx[-1] != expected and infer(ctx, answer) == expected
    assert _top(ctx, answer) == {2: 1}
    emitter.check_type('transportedFive', ctx, answer, expected)
    emitter.check_type('foldedSwap', scalar, subst_tm(swap, fold),
                       subst_ty(infer(pair, swap), fold))


def check_rice(checkout):
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as folder:
        directory = Path(folder)
        (directory / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        positive = directory / 'Positive.catt'
        positive.write_text('''import examples/eh
def eh_is_swap (x : *) (a : id(x) -> id(x)) (b : id(x) -> id(x)) : eh(x,a,b) -> swap(a,b) = id(eh(x,a,b))
def source_is_product (x : *) (a : id(x) -> id(x)) (b : id(x) -> id(x)) : swap_src(a,b) -> comp[a,b] = id(comp[a,b])
def target_is_product (x : *) (a : id(x) -> id(x)) (b : id(x) -> id(x)) : swap_tgt(a,b) -> comp[b,a] = id(comp[b,a])
''')
        negative = directory / 'Negative.catt'
        negative.write_text('''import examples/eh
def diag_is_identity (x : *) (a : id(x) -> id(x)) : eh(x,a,a) -> id(comp[a,a]) = id(eh(x,a,a))
''')
        for flag in ('--su', '--sua'):
            def check(file):
                return subprocess.run([binary, flag, file], stdout=subprocess.PIPE,
                                      stderr=subprocess.STDOUT, text=True, check=True).stdout

            # The interpreter also exits zero on a type error. Check the final
            # import and the specific failed judgement as well as the exit code.
            accepted = check(positive)
            assert 'Error:' not in accepted and f'Finished importing {positive}' in accepted
            for name in ('eh_is_swap', 'source_is_product', 'target_is_product'):
                assert f'Checking {name}\n' in accepted
            failure_log = check(negative)
            assert 'Checking diag_is_identity\n' in failure_log
            rejected = failure_log.split('Checking diag_is_identity\n', 1)[1]
            assert 'Error: Given term' in rejected and 'does not match inferred term' in rejected
            assert f'Finished importing {negative}' not in rejected
            print(f'{flag}: strict-unit swap and endpoint conversions accepted, diagonal identity conversion rejected')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    parser.add_argument('--rice-dir', type=Path, help='built checkout of Rice’s catt-strict')
    args = parser.parse_args()
    emitter = Emitter()
    folded_transport(emitter)
    print('Folded rank-five transport has the prescribed raw boundary and uses the 5-generator once')
    if args.agda_dir:
        module = 'PlanarBaseTransport'
        (args.agda_dir / (module + '.agda')).write_text(emitter.module(module, __doc__))
    if args.rice_dir:
        check_rice(args.rice_dir.resolve())


if __name__ == '__main__':
    main()
