"""Check inverse-probe presentations, signed track readings and scanning degrees."""
from argparse import ArgumentParser
from itertools import permutations, product
import json
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, tdim, tgt, tree_ctx, v)
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, string_tree


def parity(sequence):
    return sum(a > b for i, a in enumerate(sequence) for b in sequence[i + 1:]) % 2


def read(holes, words, order):
    if holes < 0 or sorted(order) != list(range(len(words))):
        raise ValueError('expected a permutation of the zero-based probe positions')
    winding = [0] * holes
    for word in words:
        for g in word:
            if not 1 <= abs(g) <= holes:
                raise ValueError('unknown signed meridian')
            winding[abs(g) - 1] += 1 if g > 0 else -1
    odd = parity(order)
    return dict(winding=winding, parity=odd, raw_fills=not odd and not any(winding),
                excluded_by_surface_parity=bool(odd))


def parity_tables():
    # Each positive input block carries positions on one address. The second
    # coordinate of a name is its ordinal in the entire input slot.
    def blocks(parts):
        return {(i, j): tuple((i, n) for n in range(sum(row[:j]), sum(row[:j + 1])))
                for i, row in enumerate(parts) for j in range(len(row))}
    orders = list(permutations(product(range(2), range(2))))
    def flatten(data, order):
        return [a for index in order for a in data[index]]
    def sign(data, order):
        # Order only the blocks. An even block makes no contribution.
        return parity([k for k in order if len(data[k]) % 2])
    count = 0
    for counts in product(range(3), repeat=4):
        rows = (counts[:2], counts[2:])
        s = blocks(rows)
        t = blocks([row[::-1] for row in rows])
        for orientation in product((False, True), repeat=2):
            image = {(i, n): (i, sum(row) - 1 - n if reverse else n)
                     for i, (row, reverse) in enumerate(zip(rows, orientation, strict=True))
                     for n in range(sum(row))}
            middle = parity([image[a] for a in sorted(image)])
            for i, source in enumerate(orders):
                target = orders[(7 * i + 1) % len(orders)]
                transported = [image[a] for a in flatten(s, source)]
                destination = flatten(t, target)
                actual = parity([destination.index(a) for a in transported])
                assert actual == (sign(s, source) + middle + sign(t, target)) % 2
                count += 1
    return count


def finite_wreath():
    # Take the two meridians in UT_3(F_2); the central coordinate records
    # their order. Compare the predicted kernel with the actual derived subgroup.
    d = list(product(range(2), repeat=3))
    z = (0, 0, 0)
    def times(u, v):
        a, b, c = u
        x, y, t = v
        return a ^ x, b ^ y, c ^ t ^ (a * y)
    def mul(x, y):
        a, b, i = x
        c, d, j = y
        if i:
            c, d = d, c
        return times(a, c), times(b, d), i ^ j
    group = list(product(d, d, range(2)))
    unit = (z, z, 0)
    inverse = {x: next(y for y in group if mul(x, y) == unit) for x in group}
    comms = {mul(mul(x, y), mul(inverse[x], inverse[y])) for x in group for y in group}
    derived, todo = {unit}, [unit]
    while todo:
        x = todo.pop()
        for c in comms:
            y = mul(x, c)
            if y not in derived:
                derived.add(y)
                todo.append(y)
    assert derived == {(a, b, i) for a, b, i in group if not i and a[:2] == b[:2]}
    return len(group), len(derived)


def circle_charges():
    # Intersect a polygonal motion with each positive ray. At a regular
    # non-basepoint of the coefficient circle the label loop has degree one.
    punctures = (0, 6)
    base = (-4, -2)
    def meridian(x):
        corner = (x - 1, -1)
        return [base, (x - 1, -2), corner, (x + 1, -1), (x + 1, 1),
                (x - 1, 1), corner, (x - 1, -2), base]
    count = 0
    for length in range(5):
        for word in product((-2, -1, 1, 2), repeat=length):
            path = [base]
            for g in word:
                circle = meridian(punctures[abs(g) - 1])
                path.extend((circle if g > 0 else circle[::-1])[1:])
            degrees = [sum((int(b > 0) - int(a > 0)) for (x, a), (y, b) in zip(path, path[1:])
                           if x == y and x > p) for p in punctures]
            assert degrees == read(2, [word], [0])['winding']
            count += 1
    return count


def inverse_context(rank):
    ctx = (STAR,)
    lower = v(0)
    for _ in range(rank - 1):
        lower = ident(ctx, lower)
    e = ident(ctx, lower)
    ctx += (arr(infer(ctx, lower), lower, lower),)
    ty = arr(infer(ctx, e), e, e)
    ctx += (ty, ty)
    q, r = v(2), v(3)
    stop = ident(ctx, e)
    def arrow(s, t):
        nonlocal ctx
        assert infer(ctx, s) == infer(ctx, t)
        name = v(len(ctx))
        ctx += (arr(infer(ctx, s), s, t),)
        return name
    fits = []
    for s, t in ((q, r), (r, q)):
        p = comp2(ctx, rank, s, t)
        fits.append((arrow(p, stop), arrow(stop, p)))
    for f, g in fits:
        for a, b in ((f, g), (g, f)):
            twice, identity = comp2(ctx, rank + 1, a, b), ident(ctx, src(ctx, a))
            arrow(twice, identity)
            arrow(identity, twice)
    assert len(ctx) == 16
    return ctx, stop, fits


def triangle(rank, writer):
    ctx, _, fits = inverse_context(rank)
    q, r = v(2), v(3)
    row = tree_ctx(string_tree(rank, [rank + 1] * 3))
    slots = maximal_vars(row)
    x, y, z = map(v, slots)
    left = comp2(row, rank, comp2(row, rank, x, y), z)
    right = comp2(row, rank, x, comp2(row, rank, y, z))
    assoc = subst_tm(head(row, left, right), sub_from(row, ctx, dict(zip(slots, (q, r, q)))))
    disk = tree_ctx(disc_tree(rank + 1))
    peak, = maximal_vars(disk)
    a = v(peak)
    pad_left = comp2(disk, rank, ident(disk, src(disk, a)), a)
    pad_right = comp2(disk, rank, a, ident(disk, tgt(disk, a)))
    sub = sub_from(disk, ctx, {peak: q})
    l, u = (subst_tm(head(disk, padded, a), sub) for padded in (pad_left, pad_right))
    paths = (composite(ctx, rank + 1, [comp2(ctx, rank, fits[0][0], q), l]),
             composite(ctx, rank + 1, [assoc, comp2(ctx, rank, q, fits[1][0]), u]))
    boundary = arr(infer(ctx, q), comp2(ctx, rank, comp2(ctx, rank, q, r), q), q)
    # The ordinary strict top chain sees exactly the slots of the output rank.
    def weight(t):
        if t[0] == 'v':
            return int(t == fits[0][0]) - int(t == fits[0][1])
        _, arity, _, sigma = t
        return sum(weight(sigma[j]) for j, ty in enumerate(arity) if tdim(ty) + 1 == rank + 2)
    for i, t in enumerate(paths):
        assert infer(ctx, t) == boundary
        assert weight(t) == 1 - i
        writer.check_type(f'triangle{rank}route{i}', ctx, t, boundary)
    for ty in ctx[8:]:
        assert weight(ty[2]) == weight(ty[3])
    if rank == 2:
        for i in range(8, 16, 2):
            for a, b in ((v(i), v(i + 1)), (v(i + 1), v(i))):
                pair = comp2(ctx, rank + 2, a, b)
                unit = ident(ctx, src(ctx, a))
                assert infer(ctx, pair) == infer(ctx, unit)
                base = infer(ctx, pair)
                ctx += (arr(base, pair, unit), arr(base, unit, pair))
        assert len(ctx) == 32
        g = writer.ctx(ctx)
        writer.checks.append(f'throughSix : {g} ⊢ctx\nthroughSix = from-just (checkCtx {g})\n')


def scanning_degrees():
    # Count the signed preimages in the parameter disk of an extended track.
    # One generic centre value for each scanning coordinate fixes the spatial
    # point and the circle-label time. Only the coned parameter triangles remain.
    def det(a, b, c):
        return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])
    origin, base = (-13, 17), (-4, -2)
    centres = [(0, 0), (8, 0)]
    def circuit(x):
        a = (x-1, -1)
        return [base, a, (x+1,-1), (x+1,1), (x-1,1), a, base]
    trials = 0
    for size in range(5):
        for word in product((-2, -1, 1, 2), repeat=size):
            path = [base]
            for g in word:
                loop = circuit(centres[abs(g)-1][0])
                path.extend((loop if g > 0 else loop[::-1])[1:])
            degrees = []
            for centre in centres:
                value = 0
                for a, b in zip(path, path[1:]):
                    signs = det(origin, a, centre), det(a, b, centre), det(b, origin, centre)
                    assert 0 not in signs
                    value += int(min(signs) > 0) - int(max(signs) < 0)
                degrees.append(value)
            assert degrees == read(2, [word], [0])['winding']
            trials += 1
    return trials


def typed(directory):
    completed, stop, fits = inverse_context(2)
    q, r = v(2), v(3)
    a = v(len(completed))
    ctx = completed + (arr(infer(completed, q), q, q),)
    f, g = fits[0]
    moved = composite(ctx, 3, [g, comp2(ctx, 2, a, r), f])
    assert (src(ctx, moved), tgt(ctx, moved)) == (stop, stop)
    writer = Emitter()
    for rank in (2, 3):
        triangle(rank, writer)
    if directory:
        writer.checks.append('inverseContext : ' + writer.ctx(completed) + ' ⊢ctx\n'
                             'inverseContext = from-just (checkCtx ' + writer.ctx(completed) + ')\n')
        writer.check_type('loopAtIdentity', ctx, moved, arr(infer(ctx, stop), stop, stop))
        directory.mkdir(parents=True, exist_ok=True)
        (directory / 'InvertibleProbes.agda').write_text(writer.module('InvertibleProbes', __doc__))


def audit():
    assert read(2, [[1, 2, -1, -2]], [0])['raw_fills']
    assert read(1, [[1, 1], [-1, -1]], [0, 1])['raw_fills']
    assert read(1, [[1], [-1]], [1, 0])['excluded_by_surface_parity']
    assert read(2, [[1, 1, 2], [2, -1]], [0, 1])['winding'] == [1, 2]
    assert read(2, [[], [], []], [2, 0, 1])['raw_fills']
    return dict(sign_checks=parity_tables(), finite_group_and_derived_sizes=finite_wreath(),
                geometric_charges=circle_charges(), scanning_degrees=scanning_degrees())


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, help='JSON with holes, signed meridian words, and final order')
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(read(**json.loads(args.input.read_text()))))
        return
    typed(args.agda_dir)
    print(json.dumps(audit()))


if __name__ == '__main__':
    main()
