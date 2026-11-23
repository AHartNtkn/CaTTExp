"""Check directed higher attachments over the scalar base in Response 31."""
import argparse
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import arr, check_ctx, comp2, glue_tree, infer, maximal_vars, subst_ty, tdim, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_scalar_cube import exchange
from semistrict_surface_skeletal_base import right_unit


BASE = '(x : *) (a : id(x) -> id(x))'


def check_rank(checkout, rank, seam):
    inputs = BASE + ''.join(f' ({label} : {seam} -> {seam})' for label in 'uvt')
    padded = f'comp[id({seam}),u]'
    extended = inputs + f' (z : comp[{padded},v] -> t)'
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as folder:
        tmp = Path(folder)
        (tmp / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        (tmp / 'Raw.catt').write_text(f"""import examples/eh
def enter = coh [ x{{u}}y{{v}}z : comp[u,v] -> comp[comp[id(x),u],v] ]
def exit_pad = coh [ x{{u}}y{{v}}z : comp[comp[id(x),u],v] -> comp[u,v] ]
def move_slot = coh [ {{m{{e}}n}}{{v}} : comp[m,v] -> comp[n,v] ]
def unit_in = coh [ x{{u}}y : u -> comp[id(x),u] ]
def direct_fit {extended} : comp[u,v] -> t = comp[enter(u,v),z]
def via_slot {extended} : comp[u,v] -> t = comp[move_slot(unit_in(u),v),z]
def round_trip {inputs} : comp[u,v] -> comp[u,v] = comp[enter(u,v),exit_pad(u,v)]
""")
        (tmp / 'Surface.catt').write_text(f"""import Raw
def converted {extended} : comp[u,v] -> t = z
def direct_class {extended} : direct_fit(x,a,u,v,t,z) -> z = id(z)
def slot_class {extended} : via_slot(x,a,u,v,t,z) -> z = id(z)
def round_class {inputs} : round_trip(x,a,u,v,t) -> id(comp[u,v]) = id(id(comp[u,v]))
""")
        (tmp / 'Unfitted.catt').write_text(f'import Raw\ndef premature {extended} : comp[u,v] -> t = z\n')
        (tmp / 'Reversed.catt').write_text(f'import Raw\ndef reversed_fit {extended} : t -> comp[u,v] = z\n')
        accepted(run(binary, tmp, 'Raw.catt'), 'Raw.catt', ['direct_fit', 'via_slot', 'round_trip'])
        rejected(run(binary, tmp, 'Unfitted.catt'), 'Unfitted.catt', 'premature')
        print(f'Weak CaTT checked both fitted {rank+2}-cells and the round trip, and rejected direct conversion.')
        for mode in ('--su', '--sua'):
            accepted(run(binary, tmp, 'Surface.catt', [mode]), 'Surface.catt',
                     ['converted', 'direct_class', 'slot_class', 'round_class'])
            rejected(run(binary, tmp, 'Reversed.catt', [mode]), 'Reversed.catt', 'reversed_fit')
            print(f'{mode} verified the conversion and all three classes, and rejected the reversed use.')


def check_generic_bases(agda_dir):
    emitter = Emitter()
    checked = 0
    for rank in range(4, 8):
        for cut in range(rank):
            arity = tree_ctx(glue_tree(rank, cut, rank))
            parent = list(range(len(arity)))

            def root(index):
                while parent[index] != index:
                    index = parent[index]
                return index

            for ty in arity:
                if tdim(ty) + 1 == 4:
                    left, right = root(ty[2][1]), root(ty[3][1])
                    parent[max(left, right)] = min(left, right)
            base, images = [], []
            for index, ty in enumerate(arity):
                degree = tdim(ty) + 1
                if degree > 3:
                    source, target = (images[face[1]] for face in ty[2:])
                    assert source == target
                    term = identity(tuple(base), source)
                elif root(index) != index:
                    term = images[root(index)]
                else:
                    term = v(len(base))
                    base.append(subst_ty(ty, images))
                assert infer(tuple(base), term) == subst_ty(ty, images)
                images.append(term)
            if agda_dir:
                source, target = emitter.ctx(tuple(base)), emitter.ctx(arity)
                labels = emitter.sub(tuple(images))
                name = f'base{rank}cut{cut}'
                emitter.checks.append(
                    f'{name} : {source} ⊢sub {labels} ∶ {target}\n'
                    f'{name} = from-just (checkSub {source} (from-just (checkCtx {source})) '
                    f'{labels} {target})\n')
            checked += 1
    if agda_dir:
        (agda_dir / 'SemistrictGenericBases.agda').write_text(
            emitter.module('SemistrictGenericBases', __doc__))
    print(f'Checked all {checked} third-degree base quotients of two glued discs in ranks four to seven.')


def check_gray_attachment(agda_dir):
    square = tree_ctx(glue_tree(2, 0, 2))
    swap = exchange(square, *map(v, maximal_vars(square)))
    face_type, first, last = infer(square, swap)[1:]
    # Both sides of this declared return consist of two contextual events.
    base = square + (arr(face_type, last, first),)
    circuit = comp2(base, 2, swap, v(len(square)))
    four_type = arr(infer(base, circuit), circuit, circuit)
    ctx = base + (four_type,) * 3
    u, v_cell, t = map(v, range(len(base), len(ctx)))
    original = comp2(ctx, 3, u, v_cell)
    correction = right_unit(ctx, u, 4, insert=True)
    step = comp2(ctx, 3, correction, v_cell)
    source, padded = infer(ctx, step)[2:]
    assert source == original and padded != original
    extended = ctx + (arr(four_type, padded, t),)
    check_ctx(extended)
    answer = comp2(extended, 4, step, v(len(ctx)))
    desired = arr(four_type, original, t)
    assert infer(extended, answer) == desired
    if agda_dir:
        emitter = Emitter()
        emitter.check_type('fittedOnDirectedCircuit', extended, answer, desired)
        module = emitter.module('GrayDegreeFive', __doc__)
        (agda_dir / 'GrayDegreeFive.agda').write_text(
            module.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))
    print('Checked a fitted 5-generator over a directed square and a declared positive return.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path, help='built checkout of Rice’s catt-strict')
    parser.add_argument('--agda-dir', type=Path, help='emit the typed base substitutions here')
    args = parser.parse_args()
    check_generic_bases(args.agda_dir)
    check_gray_attachment(args.agda_dir)
    checkout = args.checkout.resolve()
    seam = 'eh(x,a,a)'
    for rank in range(3, 6):
        check_rank(checkout, rank, seam)
        seam = f'id({seam})'


if __name__ == '__main__':
    main()
