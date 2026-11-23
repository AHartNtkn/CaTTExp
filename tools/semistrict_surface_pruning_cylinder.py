"""Check the relative cylinder and simultaneous degeneracy tests for strict units."""
from argparse import ArgumentParser
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import maximal_vars, tree_ctx, tree_of
from gray_globe_comparison import atom, globe
from partial_cylinder_steiner import trees
from semistrict_surface_configuration_carriers import prune
from semistrict_surface_exact_boundary import accepted, rejected, run


def subcomplex(facets):
    return {tuple(sorted(face)) for facet in facets
            for length in range(1, len(facet) + 1) for face in combinations(facet, length)}


def simplicial_product(left, right):
    # Each monotone lattice path triangulates one product of ordered simplices.
    cells = set()
    for a, b in product(left, right):
        steps = len(a) + len(b) - 2
        for horizontal in combinations(range(steps), len(a) - 1):
            i = j = 0
            vertices = [(a[i], b[j])]
            for t in range(steps):
                if t in horizontal:
                    i += 1
                else:
                    j += 1
                vertices.append((a[i], b[j]))
            cells.update(subcomplex([vertices]))
    return cells


def relative_ranks(full, prescribed, prime):
    cells = sorted(full - prescribed, key=lambda s: (len(s), s))
    rows = {s: i for i, s in enumerate(cells)}
    pivots = {}
    for cell in cells:
        column = {}
        for i in range(len(cell)):
            face = cell[:i] + cell[i+1:]
            if face in rows:
                column[rows[face]] = (-1)**i % prime
        while column:
            p = max(column)
            scale = column[p]
            if p not in pivots:
                pivots[p] = {k: a * pow(scale, -1, prime) % prime for k, a in column.items()}
                break
            for k, a in pivots[p].items():
                value = (column.get(k, 0) - scale * a) % prime
                if value:
                    column[k] = value
                else:
                    column.pop(k, None)
    return len(cells), len(pivots)


def check_cylinders():
    # V is a torus. The pruning loci are two circles meeting in one vertex.
    def vertex(x, y):
        return 3 * (x % 3) + y % 3

    torus = []
    for x, y in product(range(3), repeat=2):
        a, b = vertex(x, y), vertex(x+1, y)
        c, d = vertex(x, y+1), vertex(x+1, y+1)
        torus.extend([(a, b, d), (a, c, d)])
    v = subcomplex(torus)
    circles = [subcomplex([(vertex(i, 0), vertex(i+1, 0)) for i in range(3)]),
               subcomplex([(vertex(0, i), vertex(0, i+1)) for i in range(3)])]
    base = subcomplex([(0, 1), (1, 2)])
    # E = V x |0--1--2|. Its mapping cylinder has fibre the cone, apex 3.
    cone = subcomplex([(0, 1, 3), (1, 2, 3)])
    full = simplicial_product(v, cone)
    terminal = simplicial_product(v, base)
    narrower = [simplicial_product(circle, subcomplex([(i, i+1, 3)]))
                for i, circle in enumerate(circles)]
    total = 0
    for count in range(3):
        for choice in combinations(narrower, count):
            prescribed = terminal.union(*choice)
            for prime in (2, 3, 5):
                size, rank = relative_ranks(full, prescribed, prime)
                assert size == 2 * rank
                total += 1
    # Prescribing only the pruning union would leave relative homology.
    size, rank = relative_ranks(full, narrower[0] | narrower[1], 2)
    assert size > 2 * rank
    return total


def check_degeneracies():
    # On Delta[r]/boundary every nonsurjection represents the same basepoint.
    def simplices(m, r):
        return {None} | {a for a in combinations_with_replacement(range(r+1), m+1)
                         if len(set(a)) == r+1}

    tests = 0
    for m, r in product(range(1, 9), range(1, 5)):
        top = simplices(m, r)
        def image(indices):
            q = tuple(sum(j not in indices for j in range(i)) for i in range(m+1))
            return {None if a is None else tuple(a[j] for j in q)
                    for a in simplices(m-len(indices), r)}

        single = [image((i,)) for i in range(m)]
        for length in range(1, m+1):
            for indices in combinations(range(m), length):
                assert top.intersection(*(single[i] for i in indices)) == image(indices)
                tests += 1
    return tests


def check_gray_trees():
    quotients = 0
    for size in range(1, 8):
        for tree in trees(size):
            if sum(bool(column) for column in tree) > 1:
                continue
            ctx = tree_ctx(tree)
            leaves = maximal_vars(ctx)
            for count in range(1, len(leaves)+1):
                for choices in combinations(leaves, count):
                    pruned_ctx, _ = prune(ctx, choices)
                    assert sum(bool(column) for column in tree_of(pruned_ctx)) <= 1
                    quotients += 1

    comparisons = 0
    for arity in range(1, 6):
        for index, dim in product(range(arity), range(5)):
            for generator in globe(dim):
                factors = [globe(0)[0]] * arity
                factors[index] = generator
                # Compare the whole signed atom tableau with the active factor.
                single = atom((generator,))
                rows = atom(tuple(factors))
                projected = tuple(tuple(tuple((term[index],) for term in chain)
                                        for chain in row) for row in rows)
                assert projected == single
                assert all(term == tuple(factors[:index]) + (term[index],) + tuple(factors[index+1:])
                           for row in rows for chain in row for term in chain)
                comparisons += 1
    # Two moving columns have a square with different boundary walks.
    active = globe(1)[-1]
    square = atom((active, active))
    assert len(square) == 3 and square[1][0] != square[1][1]
    return quotients, comparisons


def check_checker(checkout):
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as tmp:
        work = Path(tmp)
        (work / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        args = '(x : *) (a : id(x) -> id(x)) (p : eh(x,a,a) -> id(comp[a,a]))'
        old_type = 'comp[p,id(id(comp[a,a]))] -> p'
        def source(name, value):
            return f'import examples/eh\ndef {name} {args} : {old_type} = {value}\n'
        (work / 'Raw.catt').write_text(source('raw', 'unitor_r(p)'))
        (work / 'Unit.catt').write_text(source('unit', 'id(p)'))
        accepted(run(binary, work, 'Raw.catt', []), 'Raw.catt', ['raw'])
        accepted(run(binary, work, 'Unit.catt', ['--su']), 'Unit.catt', ['unit'])
        rejected(run(binary, work, 'Unit.catt', []), 'Unit.catt', 'unit')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    print('quotient-presheaf degeneracy intersections:', check_degeneracies())
    print('acyclic relative cylinder complexes:', check_cylinders())
    print('Gray simple-tree quotients and tensor tableaux:', *check_gray_trees())
    if args.catt_strict:
        check_checker(args.catt_strict.resolve())
        print('mixed-dimensional raw and strict-unit witnesses checked')
