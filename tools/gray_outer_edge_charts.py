"""Check edge-chart coverage and its transfer along the pinned two-suspension section."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import product
from pathlib import Path

from canonical_gray_cube import build_cube, square_chain
from catt import arr, check_ctx, comp2, disc_tree, infer, src, sub_from, subst_tm, subst_ty, tgt, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import head

from gray_globe_comparison import atom, close_atoms, face
from gray_globe_section import row_map, trim
from gray_tree_section import generators, section, tree_boundary


INTERVAL = ((),)
CORNERS = tuple(((((), side), ((), side)),) for side in (0, 1))


def atoms(bases):
    return [atom(g, tree_boundary, len) for g in product(*bases)]


@cache
def projection(cell, axis):
    return row_map(cell, 0, lambda g: (g[axis],) if all(
        not entry[0] for i, entry in enumerate(g) if i != axis) else None)


def edge_charts(tree):
    return [(((), i), ((), i+1), ((i,), j))
            for i, child in enumerate(tree) for j in range(len(child)+1)] or [(((), 0),)]


def belongs(cell, charts):
    labels = {g[0] for pair in cell for chain in pair for g in chain}
    return any(labels.issubset(chart) for chart in charts)


def check_triple(p, q):
    bases = list(map(generators, (p, INTERVAL, q)))
    left, right = edge_charts(p), edge_charts(q)
    full_atoms = atoms(bases)
    degree = max(map(len, full_atoms))-1
    chart_cells = set()
    for basis in left:
        chart_cells.update(close_atoms(atoms((basis, bases[1], bases[2])), degree))
    for basis in right:
        chart_cells.update(close_atoms(atoms((bases[0], bases[1], basis)), degree))
    cells = close_atoms(full_atoms, degree)
    predicted = {y for y in cells if belongs(projection(y, 0), left)
                 or belongs(projection(y, 2), right)}
    assert predicted == chart_cells
    by_rank = Counter(len(trim(y))-1 for y in predicted)
    print(f'Triple: {len(predicted)}/{len(cells)} cells; chart counts by intrinsic rank: {sorted(by_rank.items())}')
    return len(cells) - len(predicted)


def suspend_projection(cell):
    poles = tuple(((((), k),),) for k in (0, 1))
    def chain_image(chain):
        return tuple((((0,) + address, label),) for ((address, label),) in chain)
    return (poles,) + tuple(tuple(chain_image(chain) for chain in pair) for pair in cell)


def check_transfer(p, q):
    target = atoms((generators((p,)), generators((q,))))
    left, right = edge_charts(p), edge_charts(q)
    height = max(map(len, target))-1
    count = Counter()
    for y in close_atoms(target, height):
        if y[0] != CORNERS:
            continue
        x = section(p, q, y)
        for outer, inner in ((0, 0), (1, 2)):
            assert projection(y, outer) == suspend_projection(projection(x, inner))
        expected = any(belongs(projection(x, axis), charts)
                       for axis, charts in ((0, left), (2, right)))
        rank = len(trim(y))-1
        if expected:
            count[rank] += 1
            if rank > 1:
                for side in (0, 1):
                    lower = trim(face(trim(y), side))
                    lifted = section(p, q, lower)
                    assert any(belongs(projection(lifted, axis), charts)
                               for axis, charts in ((0, left), (2, right)))
    print(f'Binary extreme hom: transferred counts by intrinsic target rank: {sorted(count.items())}')
    return count


def disk_charts(tree):
    disks = []
    for g in generators(tree):
        if len(g[0]) <= 2:
            cell = atom((g,), tree_boundary, len)
            disks.append(frozenset(label for pair in cell for chain in pair for (label,) in chain))
    return [disk for disk in disks if not any(disk < other for other in disks)]


def check_binary_charts(p, q):
    left, right = disk_charts(p), disk_charts(q)
    bases = generators(p), generators(q)
    target = atoms(bases)
    degree = max(map(len, target))-1
    covered = set()
    for disk in left:
        covered.update(close_atoms(atoms((disk, bases[1])), degree))
    for disk in right:
        covered.update(close_atoms(atoms((bases[0], disk)), degree))
    cells = close_atoms(target, degree)
    assert covered == {y for y in cells if belongs(projection(y, 0), left)
                       or belongs(projection(y, 1), right)}
    # Compare full tableaux in every overlap, including all composite four-cells.
    intersections = 0
    for a, b in product(left, right):
        overlap = atoms((a, b))
        top = {x for x in overlap if len(x) == 5}
        actual = {x for x in close_atoms(overlap, 4) if x[-1][0]}
        assert actual == top and len(top) <= 1
        intersections += len(top)
    print(f'Binary disk charts: {len(covered)}/{len(cells)} cells; {intersections} four-dimensional intersections.')
    return len(cells) - len(covered)


def check_raw_overlap(output):
    old_cube, _ = build_cube()
    base = old_cube[:-1]
    _, common, source, target = old_cube[-1]
    disk = tree_ctx(disc_tree(2))
    slot = len(disk)-1
    x = v(slot)
    right_unit = comp2(disk, 1, x, ident(disk, tgt(disk, x)))
    left_unit = comp2(disk, 1, ident(disk, src(disk, x)), x)

    def at(term, pole):
        return subst_tm(term, sub_from(disk, base, {slot: pole}))

    new_source, new_target = at(right_unit, source), at(left_unit, target)
    assert new_source != source and new_target != target
    assert square_chain(new_source) == square_chain(source)
    assert square_chain(new_target) == square_chain(target)
    incoming = at(head(disk, x, right_unit), source)
    outgoing = at(head(disk, left_unit, x), target)
    z, other = v(len(base)), v(len(base)+1)

    def extend(boundary):
        return base + (boundary, boundary, arr(boundary, z, other))

    old = extend(old_cube[-1])
    new = extend(arr(common, new_source, new_target))
    check_ctx(old)
    check_ctx(new)

    def whisker(term):
        return comp2(new, 2, comp2(new, 2, incoming, term), outgoing)

    # The third slot is a 4-cell. Its literal faces must be the two transported
    # cube variables, with the same whiskers and bracketing on both sides.
    sigma = tuple(map(v, range(len(base)))) + tuple(whisker(v(i)) for i in range(len(base), len(new)))
    emitter = Emitter() if output else None
    for i in range(len(base), len(new)):
        boundary = subst_ty(old[i], sigma[:i])
        assert infer(new, sigma[i]) == boundary
        if emitter:
            emitter.check_type(f'transport{i}', new, sigma[i], boundary)
    assert infer(new, sigma[-1])[2:] == sigma[-3:-1]
    if output:
        output.write_text(emitter.module(output.stem, 'Retyping both cube hemispheres across a chart overlap.'))
    print('Raw overlap: both cube hemispheres retyped, both transported generators and their four-cell checked.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    check_raw_overlap(args.agda)
    # A non-suspended root path tests whether two consecutive edges are distinguished.
    assert check_triple(((), ((),)), INTERVAL + INTERVAL) > 0
    # Both suspended paths have parallel edges and strict cells moving both outer labels.
    p, q = (((), ()),), (((),),)
    assert check_triple(p, q) > 0
    assert check_transfer(p, q)
    tall = ((p,),)
    assert check_triple(tall, q) > 0
    assert check_transfer(tall, q)[7] > 0
    assert check_binary_charts(((((),), ()), ()), (((), ()),)) > 0
