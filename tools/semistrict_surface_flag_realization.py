"""Check the oriental faces and temporal sums used in Researcher Response 3."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import combinations, permutations
from pathlib import Path

from catt import STAR, arr, comp2, comp_tree, infer, maximal_vars, src, sub_from, subst_tm, subst_ty, tgt, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_grid_tracks import associator, temporal


def check_cube(rank, output, opaque=False):
    """Type all flags in the three-cube and specialize at a single compound loop."""
    cut = rank - 2 if opaque else 0

    @cache
    def carrier(first, last):
        dims = [rank if (first ^ last) & 1 << i else rank - 1 for i in range(3)]
        ctx = tree_ctx(string_tree(cut, dims))
        return ctx, tuple(map(v, maximal_vars(ctx)))

    def at_face(flag, face):
        ctx, cells = carrier(flag[0], flag[-1])
        small, _ = carrier(face[0], face[-1])
        labels = []
        for i, cell in enumerate(cells):
            bit = 1 << i
            if (flag[0] ^ flag[-1]) & bit and not (face[0] ^ face[-1]) & bit:
                cell = (tgt if face[0] & bit else src)(ctx, cell)
            labels.append(cell)
        substitution = sub_from(small, ctx, dict(zip(maximal_vars(small), labels, strict=True)))
        return subst_tm(generic(face), substitution)

    @cache
    def generic(flag):
        ctx, cells = carrier(flag[0], flag[-1])
        if opaque and len(flag) == 1:
            # This ternary head is distinct from both binary bracketings.
            return comp_tree(string_tree(cut, [rank - 1] * 3), ctx, cells)
        if opaque and len(flag) == 2:
            return head(ctx, at_face(flag, flag[:1]), at_face(flag, flag[1:]))
        if len(flag) == 1:
            return composite(ctx, cut, cells)
        if len(flag) == 2:
            edges = [a if (flag[0] ^ flag[-1]) & 1 << i else identity(ctx, a)
                     for i, a in enumerate(cells)]
            return composite(ctx, cut, edges)

        def face(*positions):
            return at_face(flag, tuple(flag[i] for i in positions))

        if len(flag) == 3:
            return head(ctx, face(0, 2), temporal(ctx, face(0, 1), face(1, 2)))
        assert len(flag) == 4
        a, b, c = face(0, 1), face(1, 2), face(2, 3)
        left = temporal(ctx, face(0, 2, 3), comp2(ctx, rank - 1, face(0, 1, 2), c))
        left = temporal(ctx, left, associator(ctx, a, b, c))
        right = temporal(ctx, face(0, 1, 3), comp2(ctx, rank - 1, a, face(1, 2, 3)))
        return head(ctx, left, right)

    folded = (STAR, arr(STAR, v(0), v(0)))
    cell = comp2(folded, 0, v(1), v(1))
    for _ in range(2, rank + 1):
        folded += (arr(infer(folded, cell), cell, cell),)
        cell = v(len(folded) - 1)
    fixed = src(folded, cell)
    emitter = Emitter() if output else None
    images = {}
    for order in permutations(range(3)):
        flag = [0]
        for i in order:
            flag.append(flag[-1] | 1 << i)
        flag = tuple(flag)
        ctx, _ = carrier(flag[0], flag[-1])
        fold = sub_from(ctx, folded, dict.fromkeys(maximal_vars(ctx), cell))
        for n in range(1, len(flag) + 1):
            for face in combinations(flag, n):
                small, _ = carrier(face[0], face[-1])
                labels = [cell if (face[0] ^ face[-1]) & 1 << i else fixed for i in range(3)]
                local = sub_from(small, folded, dict(zip(maximal_vars(small), labels, strict=True)))
                t = generic(face)
                image = subst_tm(t, local)
                assert infer(folded, image) == subst_ty(infer(small, t), local)
                assert subst_tm(at_face(flag, face), fold) == image
                assert images.setdefault(face, image) == image
        if emitter and order == (0, 1, 2):
            expected = subst_ty(infer(ctx, generic(flag)), fold)
            emitter.check_type('foldedFlag', folded, images[flag], expected)
    assert len({t for face, t in images.items() if len(face) == 1}) == 1
    assert len({t for face, t in images.items() if len(face) == 2 and face[0] == 0
                and face[1] in (1, 2, 4)}) == 3
    if emitter:
        name = f'FoldedOpaque{rank}' if opaque else f'FoldedFlag{rank}'
        (output / (name + '.agda')).write_text(emitter.module(name, __doc__))
    kind = 'ternary head' if opaque else 'binary products'
    print(f'Rank {rank}, {kind}: {len(images)} folded flags typed, including all six tetrahedra.')


def boundary(simplex):
    return Counter({simplex[:i] + simplex[i+1:]: (-1)**i for i in range(len(simplex))})


def serial_image(simplex, seams):
    """Positive chain map to a wedge; label its basis faces by global vertices."""
    if len(simplex) == 1:
        return Counter({simplex: 1})
    result = Counter()
    for lo, hi in zip(seams, seams[1:]):
        projection = tuple(min(hi, max(lo, vtx)) for vtx in simplex)
        if len(set(projection)) == len(simplex):
            result[projection] += 1
    return result


def check_restriction(face, seams):
    blocks = []
    for lo, hi in zip(seams, seams[1:]):
        visited = sorted({min(hi, max(lo, vertex)) for vertex in face})
        if len(visited) > 1:
            blocks.append(visited)
    nodes = sorted({v for block in blocks for v in block})
    restricted_seams = (0, *(nodes.index(block[-1]) for block in blocks))
    for size in range(1, len(face) + 1):
        for subface in combinations(face, size):
            indices = tuple(nodes.index(v) for v in subface)
            restricted = serial_image(indices, restricted_seams)
            included = {tuple(nodes[i] for i in atom): count for atom, count in restricted.items()}
            assert serial_image(subface, seams) == included


def check_sums(maximum=6):
    tested = 0
    for n in range(1, maximum + 1):
        for blocks in range(n):
            for inner in combinations(range(1, n), blocks):
                seams = (0, *inner, n)
                for k in range(2, n + 2):
                    for face in combinations(range(n + 1), k):
                        left, right = Counter(), Counter()
                        for a, coefficient in serial_image(face, seams).items():
                            for b, sign in boundary(a).items():
                                left[b] += coefficient * sign
                        for b, sign in boundary(face).items():
                            for a, coefficient in serial_image(b, seams).items():
                                right[a] += coefficient * sign
                        assert left == right
                        check_restriction(face, seams)
                        tested += 1
    print(f'{tested} signed boundary checks for temporal sums of orientals through dimension {maximum}.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
    check_sums()
    for rank in (3, 4):
        check_cube(rank, args.agda_dir)
    check_cube(4, args.agda_dir, opaque=True)
