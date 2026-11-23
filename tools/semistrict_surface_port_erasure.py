"""Exercise port erasure on cube faces, cabling subgroups and typed cubical diagrams."""
from argparse import ArgumentParser
from itertools import combinations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_concurrent_rules import cable
from semistrict_surface_shared_edge import braid_image, inverse
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_factorization import hexagon


def check_faces():
    # Names of the carriers are independent of the names of the marks. An
    # event mark can be retained in either projection even if both ends vanish.
    count = full_batches = 0
    for sizes in product(range(3), repeat=4):
        before = [[('in', e, i) for i in range(sizes[e])] for e in range(2)]
        after = [[('out', e, i) for i in range(sizes[e + 2])] for e in range(2)]
        added_in = [('pad-in', e) for e in range(2)]
        added_out = [('pad-out', e) for e in range(2)]
        jumps = [('event', e) for e in range(2)]
        stationary = ('bypass',)
        keep_shared = {*jumps, stationary}
        old = keep_shared.union(*(before + after))
        unary = keep_shared.union(added_in, added_out)
        inputs = [block + [mark] for block, mark in zip(before, added_in)]
        outputs = [block + [mark] for block, mark in zip(after, added_out)]

        def frontier(corner):
            carriers = [stationary]
            for e, status in enumerate(corner):
                carriers.extend((inputs[e], [jumps[e]], outputs[e])[status])
            return carriers

        for projection in (old, unary):
            for corner in product(range(3), repeat=2):
                full = frontier(corner)
                if corner == (1, 1):
                    assert set(full) == keep_shared and all(x in projection for x in full)
                    full_batches += 1
                for e, status in enumerate(corner):
                    if status != 1:
                        continue
                    for new_status, block in ((0, inputs[e]), (2, outputs[e])):
                        expected = [m for m in frontier(corner[:e] + (new_status,) + corner[e+1:])
                                    if m in projection]
                        actual = [v for w in full if w in projection
                                  for v in (block if w == jumps[e] else [w]) if v in projection]
                        assert actual == expected
                        count += 1
    return count, full_batches


def pure_generators(n):
    for i, j in combinations(range(n), 2):
        approach = tuple(range(j, i + 1, -1))
        loop = approach + (i + 1, i + 1) + tuple(-s for s in reversed(approach))
        yield loop
        yield tuple(-s for s in reversed(loop))


def check_cluster_braids():
    # Two disjoint clusters and a stationary strand. On the actual pure
    # braid group their commuting retractions identify the full stabilizer.
    count = joint = separated = 0
    for a, b in product((1, 2), repeat=2):
        n = a + b + 1
        collapse_a = [a] + [0] * (a - 1) + [1] * (b + 1)
        collapse_b = [1] * a + [b] + [0] * (b - 1) + [1]
        reps = [1] + [0] * (a - 1) + [1] + [0] * (b - 1) + [1]
        for u, v in product(pure_generators(n), repeat=2):
            w = u + v
            first = cable(w, collapse_a)
            second = cable(w, collapse_b)
            left = braid_image(n, cable(first, collapse_b))
            right = braid_image(n, cable(second, collapse_a))
            expanded = braid_image(n, cable(cable(w, reps), [a, b, 1]))
            original = braid_image(n, w)
            assert left == right == expanded
            in_both = braid_image(n, first) == original and braid_image(n, second) == original
            assert in_both == (original == expanded)
            joint += in_both
            separated += not in_both
            count += 1
    assert joint and separated
    return count, joint, separated


def check_point_push():
    # The last strand is the portless site. It encircles the two stationary
    # strands in succession. The commutator has zero pair linking numbers.
    around_first = (2, 1, 1, -2)
    around_second = (2, 2)
    loop = around_first + around_second + tuple(inverse(around_first)) + tuple(inverse(around_second))
    assert braid_image(3, loop) != braid_image(3, ())
    for dropped in range(3):
        projection = [int(i != dropped) for i in range(3)]
        assert braid_image(2, cable(loop, projection)) == braid_image(2, ())


def check_typed_projection(checkout):
    cube, faces = hexagon()
    exe = checkout / 'target/release/catt_strict'
    count = 0
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        (folder / 'Hex.catt').write_text(cube)
        for n in (2, 3, 4):
            pole = 'x'
            for _ in range(n - 1):
                pole = f'id({pole})'
            empty = f'id({pole})'
            context = '(x : *)' + ''.join(f' ({s} : {pole} -> {pole})' for s in 'abcd')
            ends = [(empty, 'comp[a,b]'), ('comp[c,d]', empty), (empty, empty)]
            for rule, (s, t) in zip('pqr', ends):
                context += f' ({rule} : {s} -> {t})'
            context += f' (z : {empty} -> {empty})'
            fitted = [f'comp[unitor_l({s}),{v},unitor_r_inv({t})]' for v, (s, t) in zip('pqr', ends)]
            args = ','.join(fitted)
            fargs = f'({args})'
            corrected = 'hexcell' + fargs
            left, right = [f.replace('(a,b,c)', fargs) for f in faces]
            raw = 'import Hex\n'
            for rule, (s, t), fit in zip('pqr', ends, fitted):
                raw += f'def port{rule} {context} : comp[{empty},{s}] -> comp[{t},{empty}] = {fit}\n'
            raw += f'def cube {context} : {left} -> {right} = {corrected}\n'
            (folder / 'Projection.catt').write_text(raw)
            for mode in ([], ['--sua']):
                accepted(run(exe, folder, 'Projection.catt', mode), 'Projection.catt', ['portp', 'portq', 'portr', 'cube'])
                count += 1
            eq = f'def kept {context} : {corrected} -> hexcell(p,q,r) = id(hexcell(p,q,r))\n'
            (folder / 'Kept.catt').write_text('import Projection\n' + eq)
            accepted(run(exe, folder, 'Kept.catt', ['--sua']), 'Kept.catt', ['kept'])
            bad = eq.replace(' -> hexcell(p,q,r) = id(hexcell(p,q,r))', ' -> hexcell(p,q,r) = id(hexcell(p,q,z))')
            (folder / 'Wrong.catt').write_text('import Projection\n' + bad)
            rejected(run(exe, folder, 'Wrong.catt', ['--sua']), 'Wrong.catt', 'kept')
            count += 2
    return count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    print('Commuting cube faces and full-batch projections:', *check_faces())
    print('Pure braids, in both cluster groups, outside the intersection:', *check_cluster_braids())
    check_point_push()
    print('Portless-site commutator detected; all three pair projections trivial.')
    if args.catt_strict:
        print('Typed projection and conversion runs:', check_typed_projection(args.catt_strict.resolve()))
