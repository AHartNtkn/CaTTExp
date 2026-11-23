"""Check two-scalar cuts, tree splices, integral cones and published scalar terms."""
import argparse
from collections import Counter
from itertools import combinations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, comp2, glue_tree, infer, maximal_vars, sub_from, subst_tm, subst_ty, tree_ctx, v
from catt_unit_ordered_exchange import temporal_words
from emit_agda import Emitter
from partial_cylinder_steiner import globular, trees
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from relative_coherence_slots import tableaux
from semistrict_surface_exact_boundary import accepted, rejected, run


def check_composable_cuts():
    total = 0
    for rank in range(2, 7):
        for split in range(rank):
            cells = {v: (d, s, t) for v, d, s, t in globular(glue_tree(rank, split, rank))}
            a, b = (v for v in cells if cells[v][0] == rank)
            words = list(tableaux(cells, rank))
            sectors = {v: [w for w in words if w[rank][0] == (v,)] for v in (a, b)}
            for first, second in ((a, b), (b, a)):
                found = set()
                for left, right in product(sectors[first], sectors[second]):
                    for cut in range(rank):
                        if left[:cut] == right[:cut] and left[cut][1] == right[cut][0]:
                            found.add(cut)
                            total += 1
                assert found == set(range(split + int(first == b), rank))
    return total


def positions(tree, depth):
    if depth == 0:
        return [()]
    return [(i,) + pos for i, child in enumerate(tree) for pos in positions(child, depth - 1)]


def divergence(left, right):
    return next(i for i, pair in enumerate(zip(left, right, strict=True)) if pair[0] != pair[1])


def trunk(tree):
    height = 0
    while len(tree) == 1:
        height += 1
        tree, = tree
    return height


def branches(tree):
    for i, child in enumerate(tree):
        if not positions(child, trunk(child) + 1):
            yield (i,), trunk(child) + 1
        for path, height in branches(child):
            yield (i,) + path, height + 1


def splice(tree, path, inner):
    i, *rest = path
    if rest:
        inside, = inner
        return tree[:i] + (splice(tree[i], rest, inside),) + tree[i + 1:]
    return tree[:i] + inner + tree[i + 1:]


def check_splices():
    total = 0
    shapes = [t for size in range(6) for t in trees(size)]
    for outer in shapes:
        for branch, height in branches(outer):
            for inner in shapes:
                if trunk(inner) < len(branch) - 1 or positions(inner, height + 1):
                    continue
                joined = splice(outer, branch, inner)
                for n in range(1, height + 1):
                    old, new = positions(outer, n), positions(joined, n)
                    if n < len(branch):
                        assert new == old
                        continue
                    index = old.index(branch + (0,) * (n - len(branch)))
                    added = positions(inner, n)
                    sources = [(p, None) for p in old[:index]]
                    sources += [(old[index], p) for p in added]
                    sources += [(p, None) for p in old[index + 1:]]
                    assert len(sources) == len(new)
                    for i, j in combinations(range(len(new)), 2):
                        left, right = sources[i], sources[j]
                        pos = 0 if left[0] != right[0] else 1
                        assert left[pos] < right[pos]
                        assert divergence(new[i], new[j]) == divergence(left[pos], right[pos])
                        total += 1
    return total


def boundary(chain):
    result = Counter()
    for face, coefficient in chain.items():
        for i in range(len(face)):
            result[face[:i] + face[i + 1:]] += (-1)**i * coefficient
    return {face: value for face, value in result.items() if value}


def check_cones():
    total = 0
    for n in range(2, 8):
        # Signed ordered levels give the boundary of the n-cross-polytope.
        sphere = {tuple((j, s) for j, s in enumerate(signs)): (-1)**sum(signs)
                  for signs in product((0, 1), repeat=n)}
        assert not boundary(sphere)
        for face, coef in sphere.items():
            opposite = tuple((j, 1 - s) for j, s in face)
            assert sphere[opposite] == (-1)**n * coef
        # Fix the lower skeleton and vary the image of one top cell and its
        # antipodal mate by opposite or equal cycles according to orientation.
        first = tuple((j, 0) for j in range(n))
        opposite = tuple((j, 1) for j in range(n))
        for twist in range(-3, 4):
            image = Counter()
            for face, coef in sphere.items():
                value = Counter({face: 1})
                shift = twist if face == first else ((-1)**n * twist if face == opposite else 0)
                if shift:
                    value.update({f: shift * sign for f, sign in sphere.items()})
                assert boundary(value) == boundary({face: 1})
                image.update({f: coef * coefficient for f, coefficient in value.items()})
            assert image == {f: (1 + 2 * twist) * sign for f, sign in sphere.items()}
        for cut, sign in product(range(n), (0, 1)):
            vertex = cut, sign
            for higher_count in range(n - cut):
                for levels in combinations(range(cut + 1, n), higher_count):
                    for signs in product((0, 1), repeat=higher_count):
                        face = tuple(zip(levels, signs))
                        # On a cone including the augmented empty simplex,
                        # d(v*c) + v*(dc) equals c over the integers.
                        actual = Counter(boundary({(vertex,) + face: 1}))
                        actual.update({(vertex,) + f: t for f, t in boundary({face: 1}).items()})
                        assert {f: t for f, t in actual.items() if t} == {face: 1}
                        total += 1
    return total


def check_rice(checkout):
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for n in (3, 4, 5):
            pole = 'x'
            for _ in range(n - 3):
                pole = f'id({pole})'
            unit = f'id(id({pole}))'
            context = f'(x : *) (a : {unit} -> {unit}) (b : {unit} -> {unit})'
            syl = f'syllepsis_su({pole},a,b)'
            (folder / 'Pair.catt').write_text(f"""import examples/syllepsis-su
def back = coh [ u{{x{{f{{a}}g}}y}}v{{s{{h{{b}}k}}t}}w : right(a,b) -> left(a,b) ]
def pair {context} : swap(a,b) -> swapinv(b,a) = {syl}
def grouped {context} : swap(a,b) -> swap(a,b) = comp[{syl},back(a,b)]
def singleton {context} : a -> a = swap(a,id({unit}))
def empty_input {context} : comp[a,id({unit})] -> a = id(a)
""")
            (folder / 'Order.catt').write_text(f"""import Pair
def wrong {context} : swap(a,b) -> swapinv(a,b) = {syl}
""")
            (folder / 'Group.catt').write_text(f"""import Pair
def wrong {context} : grouped(x,a,b) -> id(swap(a,b)) = id(grouped(x,a,b))
""")
            for mode in ('--su', '--sua'):
                accepted(run(binary, folder, 'Pair.catt', [mode]), 'Pair.catt',
                         ['pair', 'grouped', 'singleton', 'empty_input'])
                rejected(run(binary, folder, 'Order.catt', [mode]), 'Order.catt', 'wrong')
                rejected(run(binary, folder, 'Group.catt', [mode]), 'Group.catt', 'wrong')


def check_pair_projection(folder):
    emitter = Emitter()
    for n in (3, 4, 5):
        point = (STAR,)
        unit = v(0)
        for _ in range(n - 1):
            unit = identity(point, unit)
        base = point + (arr(infer(point, unit), unit, unit),) * 2
        other = comp2(point, n - 2, unit, unit)
        correction = head(point, unit, other)
        ctx = base + (infer(point, correction),)
        forget = tuple(map(v, range(3))) + (correction,)
        pair = tree_ctx(glue_tree(n, 0, n))
        early, late = temporal_words(pair, *map(v, maximal_vars(pair)), 0, n - 1)
        # Whisker the two marked scalar events together. Place the scalar
        # with unequal raw faces in the other spatial column of the exchange.
        retained = comp2(ctx, n - 1, v(1), v(2))
        label = sub_from(pair, ctx, dict(zip(maximal_vars(pair), (retained, v(3)))))
        term = subst_tm(head(pair, early, late), label)
        projected = subst_tm(term, forget)
        expected = subst_ty(infer(ctx, term), forget)
        assert infer(base, projected) == expected
        emitter.check_type(f'projected{n}', base, projected, expected)
        emitter.check_eq(f'forget{n}', term, forget, projected)
    if folder:
        name = 'ScalarPairProjection'
        (folder / (name + '.agda')).write_text(emitter.module(name, __doc__))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    parser.add_argument('--agda-dir', type=Path)
    options = parser.parse_args()
    print(f'{check_composable_cuts()} composable two-event factorizations')
    print(f'{check_splices()} ordered pair positions after insertion or pruning')
    print(f'{check_cones()} integral cone identities')
    check_pair_projection(options.agda_dir)
    if options.catt_strict:
        check_rice(options.catt_strict.resolve())
        print('Both published modes checked the split, grouped and singleton cases in ranks 3–5.')
