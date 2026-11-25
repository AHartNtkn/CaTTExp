"""Check a relative walking-equivalence extension at its original attaching terms."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import STAR, arr, check_ctx, coh_between, comp2, infer, subst_ty, tdim, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_skeletal_base import right_unit


def check(cap, emitter=None):
    # The retained factor contains a binary multiplication at a nonempty edge.
    p = v(1)
    target = (STAR, arr(STAR, v(0), v(0)))
    target += (arr(target[1], comp2(target, 0, p, p), p),)
    ctx = list(target)
    fold = [v(i) for i in range(len(target))]
    point = (STAR,)

    def declare(ty):
        # Every added term in this example folds through the shared vertex.
        # Its two folded faces can be different raw writings on that point.
        image_type = subst_ty(ty, fold)
        if image_type == STAR:
            image = v(0)
        else:
            source, dest = image_type[2:]
            image = coh_between(point, (), [v(0)], source, dest)
        assert infer(target, image) == image_type
        cell = v(len(ctx))
        ctx.append(ty)
        fold.append(image)
        return cell

    def arrow(source, dest):
        ty = infer(tuple(ctx), source)
        assert ty == infer(tuple(ctx), dest)
        return declare(arr(ty, source, dest))

    def walk_at(old):
        before = len(ctx)
        ty = infer(tuple(ctx), old)
        degree = tdim(ty) + 1
        new = declare(ty)
        fronts = [(old, new)]
        first_reverse = None
        for k in range(degree, cap):
            next_fronts = []
            for source, dest in fronts:
                step = arrow(source, dest)
                left, right = arrow(dest, source), arrow(dest, source)
                if first_reverse is None:
                    first_reverse = left
                if k + 1 < cap:
                    g = tuple(ctx)
                    next_fronts.extend([
                        (comp2(g, k, left, step), identity(g, dest)),
                        (comp2(g, k, step, right), identity(g, source)),
                    ])
            fronts = next_fronts
        assert len(ctx) - before == 1 + 3 * (2 ** (cap - degree) - 1)
        return new, first_reverse

    y, back = walk_at(v(0))
    f, _ = walk_at(back)
    witness = right_unit(tuple(ctx), f, 1, insert=True)
    z, _ = walk_at(witness)
    marked = target + (STAR, arr(STAR, v(3), v(0)))
    f0 = v(4)
    marked += (arr(marked[-1], f0, comp2(marked, 0, f0, identity(marked, v(0)))),)
    inclusion = [v(i) for i in range(len(target))] + [y, f, z]
    for i, (ty, term) in enumerate(zip(marked, inclusion)):
        assert infer(tuple(ctx), term) == subst_ty(ty, inclusion[:i])
    check_ctx(tuple(ctx))
    assert fold[:len(target)] == [v(i) for i in range(len(target))]
    if emitter:
        def substitution(label, ambient, source, terms):
            a, b = emitter.ctx(ambient), emitter.ctx(source)
            sigma = emitter.sub(terms)
            emitter.checks.append(
                f'{label} : {a} ⊢sub {sigma} ∶ {b}\n'
                f'{label} = from-just (checkSub {a} (from-just (checkCtx {a})) {sigma} {b})')
        substitution('retainBoth', tuple(ctx), marked, inclusion)
        substitution('foldAtVertex', target, tuple(ctx), fold)
    return len(ctx)



def check_block_degrees():
    """Degree of the named pair-direction maps before and after exchanging blocks."""
    def det(a, b, c):
        return sum(a[i] * (b[(i+1) % 3] * c[(i+2) % 3] -
                           b[(i+2) % 3] * c[(i+1) % 3]) for i in range(3))

    def degree(displacements):
        # Count oriented intersections with a regular positive ray.
        ray = (3, 5, 7)
        total = 0
        for signs in product((1, -1), repeat=3):
            face = [(axis, sign) for axis, sign in enumerate(signs)]
            if signs[0] * signs[1] * signs[2] < 0:
                face.reverse()
            a, b, c = (displacements[v] for v in face)
            volume = det(a, b, c)
            if not volume:
                continue
            barycentric = det(ray, b, c), det(a, ray, c), det(a, b, ray)
            assert all(barycentric)
            if all(v * volume > 0 for v in barycentric):
                total += 1 if volume > 0 else -1
        return total

    total = 0
    for size in range(1, 8):
        # Retain any one representative from each of two clusters of this size.
        for first, second in product(range(size), repeat=2):
            spacing = second - first
            offset = (spacing, 2 * spacing, 0)
            for swapped in (False, True):
                for block in range(2):
                    moving = block == int(swapped)
                    vectors = {}
                    for axis, sign in product(range(3), (1, -1)):
                        direction = [100, 0, 0]
                        if moving:
                            direction = [0, 0, 0]
                            direction[axis] = 100 * sign
                        vectors[axis, sign] = tuple(x + y for x, y in zip(direction, offset))
                    assert degree(vectors) == int(moving)
                    total += 1
    print(f'Checked {total} cabled block projections by integer degrees of pair-direction maps.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_block_degrees()
    for cap in (2, 3, 4):
        emitter = Emitter() if cap == 3 and args.agda_dir else None
        size = check(cap, emitter)
        print(f'Cap {cap}: checked both inclusions and the fold on {size} declarations.')
        if emitter:
            args.agda_dir.mkdir(parents=True, exist_ok=True)
            (args.agda_dir / 'RelativeExtensions.agda').write_text(
                emitter.module('RelativeExtensions', __doc__))
