"""Check scalar label changes, erasure, and the sharp boundary for erasure."""

from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, comp2, infer, subst_tm, subst_ty, v
from emit_agda import Emitter
from rc_oracle import strict_image
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, rejected, run


def polygon(ctx, rank, scalar_type):
    """A shifted directed triangle, two parallel fillings and two comparisons."""
    start = len(ctx)
    a, b, c, p, q, t, h, j = map(v, range(start, start + 8))
    ctx += (scalar_type,) * 3
    ctx += tuple(arr(scalar_type, s, e) for s, e in ((a, b), (b, c), (a, c)))
    path = comp2(ctx, rank, p, q)
    face_type = arr(infer(ctx, path), path, t)
    ctx += (face_type,) * 2
    return ctx + (arr(face_type, h, j),) * 2


def check_selectors(emitter):
    count = 0
    for rank in (2, 3, 4):
        point = (STAR,)
        units = [v(0)]
        for _ in range(rank + 3):
            units.append(identity(point, units[-1]))
        low = units[rank - 1]
        scalar_type = arr(infer(point, low), low, low)
        one = polygon(point, rank, scalar_type)
        two = polygon(one, rank, scalar_type)
        live = tuple(map(v, range(1, len(one))))
        dead = tuple(units[rank + degree] for degree in (0, 0, 0, 1, 1, 1, 2, 2, 3, 3))
        for keep in (0, 1):
            selector = (v(0),) + (live + dead if keep == 0 else dead + live)
            # A composite of two raw identities has its own spelling.
            # Fill the inactive triangle at its actual faces over the point.
            offset = 1 + (1 - keep) * len(live)
            images = list(selector)
            for i in range(offset, offset + len(live)):
                ty = subst_ty(two[i], images[:i])
                if infer(one, images[i]) != ty:
                    images[i] = head(point, ty[2], ty[3])
                assert infer(one, images[i]) == ty
            selector = tuple(images)
            for i, ty in enumerate(two):
                assert infer(one, selector[i]) == subst_ty(ty, selector[:i])
            for cut in range(rank):
                for shift, right_shift in ((6, 7), (7, 6), (8, 9), (9, 8)):
                    left = live[shift]
                    right = v(1 + len(live) + right_shift)
                    term = comp2(two, cut, left, right)
                    projected = subst_tm(term, selector)
                    expected = left if keep == 0 else live[right_shift]
                    assert infer(one, projected) == subst_ty(infer(two, term), selector)
                    assert strict_image(one, projected) == strict_image(one, expected)
                    if cut == rank - 1 and shift == 8:
                        name = f'select{rank}copy{keep}'
                        emitter.check_type(name, one, projected, subst_ty(infer(two, term), selector))
                        emitter.check_eq(name, term, selector, projected)
                    count += 1
    return count


def check_rank(checkout, rank):
    pole = 'x'
    for _ in range(rank - 2):
        pole = f'id({pole})'
    unit = f'id({pole})'
    point = f'(x : *) (a : {unit} -> {unit})'
    source = f'comp[id({unit}),a]'
    graph = f'{point} (b : {unit} -> {unit}) (p : {source} -> b)'
    args = 'x,a,b,p'
    move = f'move({args})'
    erased = 'x,a,a,unitor_l(a)'
    one_particle = f'{point} (u : id(a) -> id(a))'
    check = f"""import examples/eh
def step {graph} : a -> b = comp[unitor_l_inv(a),p]
def move {graph} : comp[a,a] -> comp[a,b] = comp[comp[[step({args})],a],eh({pole},b,a)]
def roundtrip = coh [ x{{f}}y : comp[unitor_r_inv(f),unitor_r(f)] -> id(f) ]
def comparison {graph} : comp[unitor_r_inv({move}),unitor_r({move})] -> id({move}) = roundtrip({move})
def erase_move {point} : comp[a,a] -> comp[a,a] = move({erased})
def erase_comparison {point} : comp[unitor_r_inv(erase_move(x,a)),unitor_r(erase_move(x,a))] -> id(erase_move(x,a)) = comparison({erased})
def same_after_erasure {point} : unitor_l(a) -> unitor_l(a) = id(unitor_l(a))
def label_braid {one_particle} : comp[u,u] -> comp[u,u] = eh(a,u,u)
"""
    converted = f"""import Graph
def direct {graph} : a -> b = p
"""
    distinct = f"""import Graph
def distinct {graph} (q : {source} -> b) : p -> q = id(p)
"""
    wrong_end = f"""import Graph
def wrong_end {graph} : comp[a,a] -> comp[b,a] = {move}
"""
    wrong_braid = f"""import Graph
def strict_label {one_particle} : label_braid(x,a,u) -> id(comp[u,u]) = id(label_braid(x,a,u))
"""
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as folder:
        root = Path(folder)
        (root / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for name, code in [('Graph', check), ('Direct', converted), ('Distinct', distinct),
                           ('Endpoint', wrong_end), ('Braid', wrong_braid)]:
            (root / f'{name}.catt').write_text(code)
        names = ['step', 'move', 'comparison', 'erase_move', 'erase_comparison', 'same_after_erasure',
                 'label_braid']
        for flags in ([], ['--su'], ['--sua']):
            accepted(run(binary, root, 'Graph.catt', flags), 'Graph.catt', names)
            output = run(binary, root, 'Direct.catt', flags)
            if flags:
                accepted(output, 'Direct.catt', ['direct'])
            else:
                rejected(output, 'Direct.catt', 'direct')
            rejected(run(binary, root, 'Distinct.catt', flags), 'Distinct.catt', 'distinct')
            rejected(run(binary, root, 'Endpoint.catt', flags), 'Endpoint.catt', 'wrong_end')
            rejected(run(binary, root, 'Braid.catt', flags), 'Braid.catt', 'strict_label')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path, help='built checkout of Rice’s catt-strict')
    parser.add_argument('--agda-dir', type=Path, help='write the Agda projection checks here')
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    emitter = Emitter()
    print(f'{check_selectors(emitter)} typed projections with the prescribed strict labels.')
    if args.agda_dir:
        module = 'ScalarLabelProjections'
        (args.agda_dir / f'{module}.agda').write_text(emitter.module(module, __doc__))
    for rank in (2, 3, 4):
        check_rank(checkout, rank)
        print(f'Rank {rank} passed in weak, su and sua modes.')
