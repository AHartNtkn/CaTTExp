"""Check scalar occurrence orders, tree insertion and higher scalar attachments."""
import argparse
from collections import Counter
from functools import cache
from itertools import permutations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, comp2, disc_tree, infer, maximal_vars, ps_dim, sub_from, subst_tm, subst_ty, tdim, tree_ctx, v
from emit_agda import Emitter
from rc_oracle import strict_image
from catt_unit_ordered_exchange import temporal_words
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_insertion_cut import standard


def join(left, cut, right):
    if cut == 0:
        return left + right
    assert len(left) == len(right) == 1
    return (join(left[0], cut - 1, right[0]),)


@cache
def read(ctx, term, rank, binary):
    if tdim(infer(ctx, term)) + 1 < rank:
        return ()
    if term[0] == 'v':
        # Two positions at the same address and one at a different address.
        return (('0', (term[1], 0)), ('0', (term[1], 1)), ('1', (term[1], 2)))
    _, arity, _, args = term
    if ps_dim(arity) < rank:
        return ()
    slots = maximal_vars(arity)
    prefix = False
    if binary and len(slots) == 2:
        # Only a pair meeting at the immediate face uses list concatenation.
        prefix = not (tdim(arity[slots[0]]) + 1 == tdim(arity[slots[1]]) + 1 == rank
                      and arity[slots[0]][3] == arity[slots[1]][2])
    result = []
    for position, slot in enumerate(slots):
        if tdim(arity[slot]) + 1 == rank:
            tag = str(position) if prefix else ''
            result.extend((tag + path, x) for path, x in read(ctx, args[slot], rank, binary))
    # For binary tables, list order is local to the address.
    return tuple(sorted(result, key=lambda entry: entry[0])) if binary else tuple(result)


def spatial(ctx, terms, outer, inner):
    return comp2(ctx, outer, terms[0], comp2(ctx, inner, terms[1], terms[2]))


def check_schedules(emitter, counts):
    for rank in range(3, 6):
        for outer, inner in product(range(rank - 1), repeat=2):
            if inner < outer:
                continue
            lengths = (2, 1, 1)
            branches = [string_tree(rank - 1, [rank] * length) for length in lengths]
            ctx = tree_ctx(join(branches[0], outer, join(branches[1], inner, branches[2])))
            leaves = maximal_vars(ctx)
            chains = [leaves[:2], leaves[2:3], leaves[3:]]
            assert list(map(len, chains)) == list(lengths)
            direct = [comp2(ctx, rank - 1, *map(v, chains[0])), v(leaves[2]), v(leaves[3])]
            original = spatial(ctx, direct, outer, inner)
            expected = []
            for path, chain in zip(('0', '10', '11'), chains):
                for index in chain:
                    expected.extend((path + suffix, x) for suffix, x in read(ctx, v(index), rank, True))
            expected.sort(key=lambda pair: pair[0])
            assert read(ctx, original, rank, True) == tuple(expected)
            for order in sorted(set(permutations((0, 0, 1, 2)))):
                used = [0, 0, 0]
                state = [ctx[chain[0]][2] for chain in chains]
                layers = []
                for col in order:
                    index = chains[col][used[col]]
                    inputs = state.copy()
                    inputs[col] = v(index)
                    layers.append(spatial(ctx, inputs, outer, inner))
                    state[col] = ctx[index][3]
                    used[col] += 1
                paste = layers[0]
                for layer in layers[1:]:
                    paste = comp2(ctx, rank - 1, paste, layer)
                assert infer(ctx, paste) == infer(ctx, original)
                assert strict_image(ctx, paste) == strict_image(ctx, original)
                assert read(ctx, paste, rank, True) == tuple(expected)
                # Insertion orders the generating occurrences according to
                # this particular reading, including different shuffles.
                indices = [token[0] for _, token in read(ctx, paste, rank, False)][::3]
                cursor = [iter(chain) for chain in chains]
                assert indices == [next(cursor[col]) for col in order]
                if outer == 0 and inner == 1 and order == (2, 0, 1, 0):
                    emitter.check_type(f'shuffle{rank}', ctx, paste, infer(ctx, original))
                counts['typed parallel readings'] += 1


def check_insertions(counts):
    for rank in range(2, 6):
        for cut in range(rank):
            for size in range(4):
                guard = disc_tree(rank)
                inside = string_tree(rank - 1, [rank] * size) if size else disc_tree(rank - 1)
                outer = tree_ctx(join(join(guard, cut, guard), cut, guard))
                joined = tree_ctx(join(join(guard, cut, inside), cut, guard))
                whole = maximal_vars(joined)
                # At the top cut the empty replacement is the shared seam.
                before, after = whole[0], whole[-1]
                subctx = tree_ctx(inside)
                active = whole[1:-1]
                if size == 0 and cut == rank - 1:
                    argument = identity(joined, joined[before][3])
                else:
                    sigma = sub_from(subctx, joined, dict(zip(maximal_vars(subctx), map(v, active))))
                    argument = subst_tm(standard(subctx, rank), sigma)
                labels = dict(zip(maximal_vars(outer), (v(before), argument, v(after))))
                exterior = sub_from(outer, joined, labels)
                original = standard(outer, rank)
                term = subst_tm(original, exterior)
                flat = ('coh', joined, subst_ty(original[2], exterior), tuple(map(v, range(len(joined)))))
                assert infer(joined, term) == infer(joined, flat)
                assert strict_image(joined, term) == strict_image(joined, flat)
                assert read(joined, term, rank, False) == read(joined, flat, rank, False)
                counts['ordered insertions and prunings'] += 1


def check_colours(emitter, counts):
    for rank in (2, 3, 4):
        point = (STAR,)
        unit = v(0)
        for _ in range(rank - 1):
            unit = identity(point, unit)
        # The generating types have composite faces. Duplicate the top
        # generator while keeping those faces literally unchanged.
        scalar_ty = arr(infer(point, unit), unit, unit)
        ctx = point + (scalar_ty, scalar_ty)
        fold = (v(0), v(1), v(1))
        for cut in range(rank - 1):
            disc = disc_tree(rank)
            pair = tree_ctx(join(disc, cut, disc))
            slots = maximal_vars(pair)
            first, last = temporal_words(pair, *map(v, slots), cut, rank - 1)
            swap = head(pair, first, last)
            padded = comp2(pair, rank, swap, identity(pair, last))
            comparing = head(pair, swap, padded)
            for binary in (False, True):
                # Recover the lift using only the order/address information
                # at the n-source. Check its entire (n+2)-cell by relabelling.
                for coloured in permutations((1, 2)):
                    tau = sub_from(pair, ctx, dict(zip(slots, map(v, coloured))))
                    given = read(ctx, subst_tm(first, tau), rank, binary)
                    source = read(pair, first, rank, binary)
                    by_slot = {}
                    for (address, (slot, i)), (lift_address, (copy, j)) in zip(source, given, strict=True):
                        assert (address, i) == (lift_address, j)
                        assert by_slot.setdefault(slot, v(copy)) == v(copy)
                    recovered = sub_from(pair, ctx, by_slot)
                    assert recovered == tau
                    lifted = subst_tm(comparing, recovered)
                    assert infer(ctx, lifted) == subst_ty(infer(pair, comparing), tau)
                    grey = sub_from(pair, ctx, {slot: v(1) for slot in slots})
                    assert subst_tm(lifted, fold) == subst_tm(comparing, grey)
                    if rank == 3 and cut == 0 and binary and coloured == (2, 1):
                        emitter.check_type('colouredFiveCell', ctx, lifted, infer(ctx, lifted))
                        emitter.check_eq('foldFiveCell', lifted, fold, subst_tm(comparing, grey))
                    counts['polarized higher comparisons'] += 1


def check_scalar(checkout, rank):
    pole = 'x'
    for _ in range(rank - 2):
        pole = f'id({pole})'
    unit = f'id({pole})'
    base = f'(x : *) (a : {unit} -> {unit})'
    loop = f'eh({pole},a,a)'
    coloured = f'{base} (b : {unit} -> {unit})'
    composite = 'comp[a,a]'
    endpoint = f'(k : {composite} -> {composite})'
    extended = f'{base} {endpoint} (z : comp[id({composite}),{loop}] -> k)'
    with TemporaryDirectory() as folder:
        tmp = Path(folder)
        (tmp / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        (tmp / 'Raw.catt').write_text(f"""import examples/eh
def transposition {base} : {composite} -> {composite} = {loop}
def transported {coloured} : comp[a,b] -> comp[a,b] = comp[eh({pole},a,b),eh({pole},b,a)]
def two_steps {base} : {composite} -> {composite} = comp[{loop},{loop}]
def higher_lift {coloured} : transported(x,a,b) -> comp[transported(x,a,b),id(comp[a,b])] = unitor_r_inv(transported(x,a,b))
def folded_lift {base} : two_steps(x,a) -> comp[two_steps(x,a),id({composite})] = higher_lift(x,a,a)
def enter = coh [ x{{f}}y : f -> comp[id(x),f] ]
def fit {extended} : {loop} -> k = comp[enter({loop}),z]
""")
        (tmp / 'Surface.catt').write_text(f"""import Raw
def direct {extended} : {loop} -> k = z
""")
        (tmp / 'Wrong.catt').write_text(f"""import Raw
def trivial_loop {base} : {loop} -> id({composite}) = id({loop})
""")
        (tmp / 'WrongTransport.catt').write_text(f"""import Raw
def lost_colour {coloured} : comp[a,b] -> comp[a,b] = eh({pole},a,b)
""")
        exe = checkout / 'target/release/catt_strict'
        accepted(run(exe, tmp, 'Raw.catt'), 'Raw.catt', ['transposition', 'transported', 'two_steps', 'higher_lift', 'folded_lift', 'fit'])
        rejected(run(exe, tmp, 'Surface.catt'), 'Surface.catt', 'direct')
        for mode in ('--su', '--sua'):
            accepted(run(exe, tmp, 'Surface.catt', [mode]), 'Surface.catt', ['direct'])
            rejected(run(exe, tmp, 'Wrong.catt', [mode]), 'Wrong.catt', 'trivial_loop')
            rejected(run(exe, tmp, 'WrongTransport.catt', [mode]), 'WrongTransport.catt', 'lost_colour')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path, help='built checkout of Rice’s catt-strict')
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter, counts = Emitter(), Counter()
    check_schedules(emitter, counts)
    check_insertions(counts)
    check_colours(emitter, counts)
    if args.agda_dir:
        module = 'HigherScalarReadings'
        (args.agda_dir / (module + '.agda')).write_text(emitter.module(module, __doc__))
    for rank in (3, 4, 5):
        check_scalar(args.checkout.resolve(), rank)
    for test, count in counts.items():
        print(f'{count} {test}')
    print('Checked raw fitted attachments and the published conversions and negative controls in ranks 3, 4 and 5.')


if __name__ == '__main__':
    main()
