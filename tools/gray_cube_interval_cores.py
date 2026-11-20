"""Check primitive interval totals, their whiskerings, and the small hemisphere folds."""
from collections import Counter, defaultdict
from itertools import product

from canonical_gray_cube import build_cube
from canonical_gray_two_discs import cube_generators, strict_interpreter
from catt import comp2, fv_tm, infer, src, subst_ty, tgt, v
from ct_suspension import ident
from gray_cube_facet_paths import neighbors, packed_atom
from gray_cube_six_poles import all_codimension_one, boundary_equals, differential, pack_cell
from rc2 import kappa, rc2_full


def faces(n):
    for coordinates in product(range(3), repeat=n):  # 0, moving, 1
        yield (sum(1 << i for i, a in enumerate(coordinates) if a == 1),
               sum(1 << i for i, a in enumerate(coordinates) if a == 2))


def interval(n, start, length, sign):
    full = (1 << n) - 1
    return tuple(sorted((full ^ (1 << i), ((i + sign) % 2) << i)
                        for i in range(start, start + length)))


def core(top):
    low = high = top
    rows = [(low, high)]
    while low[0][0]:
        delta = differential(low)
        assert delta == differential(high) and all(abs(c) <= 1 for c in delta.values())
        low = tuple(sorted(f for f, c in delta.items() if c < 0))
        high = tuple(sorted(f for f, c in delta.items() if c > 0))
        rows.append((low, high))
    assert len(low) == len(high) == 1
    return tuple(reversed(rows))


def face_order(n, start, length, face):
    moving, ones = face
    degree = moving.bit_count()
    if n == length:
        value, reverse = 0, False
        for i in range(n):
            symbol = 1 if moving & (1 << i) else 2 * ((ones >> i) & 1)
            value = 3 * value + (2 - symbol if reverse else symbol)
            reverse ^= symbol == 1
        return value
    if start:
        symbol = 1 if moving & 1 else 2 * (ones & 1)
        tail = face_order(n - 1, start - 1, length, (moving >> 1, ones >> 1))
        if symbol == 1:
            tail = 3 ** (n - 1) - 1 - tail
    else:
        last = 1 << (n - 1)
        symbol = 1 if moving & last else (2 if ones & last else 0)
        if degree % 2:
            symbol = 2 - symbol
        tail = face_order(n - 1, start, length, (moving % last, ones % last))
    return symbol * 3 ** (n - 1) + tail


def check_orders(n):
    basic = [packed_atom(n, f) for f in faces(n)]
    totals = 0
    for length in range(2, n + 1):
        for start in range(n - length + 1):
            atoms = [core(interval(n, start, length, sign)) for sign in range(2)]
            order = {f: face_order(n, start, length, f) for f in faces(n)}
            for cell in basic + atoms:
                for low, high in cell[:-1]:
                    assert max(map(order.__getitem__, low)) < min(map(order.__getitem__, high))
            totals += len(atoms)
    return totals


def retract_face(r, sign, f):
    # Pair the missing corner faces along an axis whose stationary bit is unique.
    full = (1 << r) - 1
    corner = sum(((1 + j + sign) % 2) << j for j in range(r))
    axis = corner if corner.bit_count() == 1 else full ^ corner
    assert axis.bit_count() == 1
    moving, ones = f
    if (ones ^ corner) & (full ^ moving):
        return Counter([f])
    if moving & axis:
        return Counter()
    result = Counter([(moving, ones ^ axis)])
    for j in range(r):
        bit = 1 << j
        if moving & bit:
            result[(moving ^ bit) | axis, (ones & ~axis) | ((~corner) & bit)] += 1
    return result


def check_retraction(r, sign):
    def extend(chain):
        result = Counter()
        for f, count in chain.items():
            for image, coefficient in retract_face(r, sign, f).items():
                result[image] += count * coefficient
        return result

    hemisphere = interval(r, 0, r, sign)
    for f in faces(r):
        mapped = retract_face(r, sign, f)
        assert extend(mapped) == mapped
        assert all(any(d & ~mask == 0 and (ones ^ station) & ~mask == 0
                       for mask, station in hemisphere) for d, ones in mapped)
        assert f[0] or sum(mapped.values()) == 1
        assert all(c > 0 and g[0].bit_count() == f[0].bit_count() for g, c in mapped.items())
        assert differential(tuple(mapped.elements())) == extend(differential((f,)))
    assert all(retract_face(r, sign, f) == Counter([f]) for f in hemisphere)


def strips(smaller, larger):
    """Recover a lower-dimensional operand and verify the exact glued tableau."""
    for k in range(4):
        if smaller[:k] != larger[:k]:
            continue
        for side in (0, 1):
            if smaller[k][side] != larger[k][side]:
                continue
            glued = (smaller[k][1], larger[k][1]) if side == 0 else (larger[k][0], smaller[k][0])
            operand = list(larger[:k]) + [glued]
            for small_pair, large_pair in zip(smaller[k+1:-1], larger[k+1:-1]):
                difference = tuple(tuple(sorted(set(a) - set(b))) for a, b in zip(large_pair, small_pair))
                if any(tuple(sorted(a + b)) != c for a, b, c in zip(small_pair, difference, large_pair)):
                    break
                operand.append(difference)
            if len(operand) == 5 and operand[-1][0] == operand[-1][1]:
                if all(boundary_equals(row, lo) for lo, hi in zip(operand, operand[1:]) for row in hi):
                    return True
    return False


def subword(n, native, top):
    row = native[-2][0]
    steps = []
    for _ in range(n):
        (f, following), = [(f, t) for f, t in neighbors(n, row, 0) if f in native[-1][0]]
        if f in top:
            steps.append((f, row, following))
        row = following
    assert len(steps) == len(top) and all(a[2] == b[1] for a, b in zip(steps, steps[1:]))
    return native[:-2] + ((steps[0][1], steps[-1][2]), (top, top))


def fold_cell(cell, n, start, length, sign):
    mask = (1 << length) - 1
    outside = ((1 << n) - 1) ^ (mask << start)

    def row_image(row):
        result = Counter()
        for d, ones in row:
            inner = ((d >> start) & mask, (ones >> start) & mask)
            for (dim, bits), count in retract_face(length, (sign + start) % 2, inner).items():
                result[(d & outside) | (dim << start), (ones & outside) | (bits << start)] += count
        assert all(c == 1 for c in result.values())
        return tuple(sorted(result))
    return tuple(tuple(row_image(row) for row in pair) for pair in cell)


def check_raw_fold(sign):
    context, checks = build_cube()
    interpret = strict_interpreter(context, tuple(cube_generators()))

    def value(term):
        return pack_cell(interpret(term))

    atoms = [value(v(i)) for i in range(len(context))]
    images = [fold_cell(cell, 3, 0, 3, sign) for cell in atoms]
    fixed = {i for i, cell in enumerate(atoms) if images[i] == cell}
    section = {cell: v(i) for i, cell in enumerate(atoms)}
    section.update((value(term), term) for _, term, _ in checks)
    substitution = []
    for i, image in enumerate(images):
        expected = subst_ty(context[i], substitution)
        if i in fixed:
            term = v(i)
        elif len(image) == 1 or (len(image) == 2 and image[-1][0]):
            term = section[image]
        elif len(image) == 2:
            term = ident(context, expected[2])
        elif len(image) == 3 and not image[-1][0]:
            term = kappa(context, *expected[2:])
        elif len(image) == 3:
            term = section[image]
            if src(context, term) != expected[2]:
                term = comp2(context, 1, kappa(context, expected[2], src(context, term)), term)
            if tgt(context, term) != expected[3]:
                term = comp2(context, 1, term, kappa(context, tgt(context, term), expected[3]))
        else:
            term = rc2_full(context, *expected[2:])
        assert infer(context, term) == expected
        assert value(term) == image and fv_tm(term) <= fixed
        substitution.append(term)


def check_six():
    by_top = defaultdict(list)
    for cell in all_codimension_one(6):
        if len(cell[-1][0]) >= 2:
            by_top[cell[-1][0]].append(cell)
    count = Counter()
    for length in range(2, 7):
        for start in range(7 - length):
            for sign in (0, 1):
                top = interval(6, start, length, sign)
                root = core(top)
                cells = by_top.pop(top)
                assert root in cells
                reached = {root}
                pending = [root]
                while pending:
                    current = pending.pop()
                    for cell in cells:
                        if cell not in reached and strips(current, cell):
                            reached.add(cell)
                            pending.append(cell)
                assert reached == set(cells)
                count[length] += len(cells)
                native = core(interval(6, 0, 6, sign))
                part = subword(6, native, top)
                if length <= 3:
                    assert fold_cell(part, 6, start, length, sign) == root
                elif length >= 5:
                    assert part == root
                else:
                    outside = ((1 << 6) - 1) ^ (((1 << length) - 1) << start)
                    extra, = set(part[-2][0]) - set(root[-2][0])
                    assert set(part[-2][1]) - set(root[-2][1]) == {extra}
                    assert extra[0] | outside == 63 and not extra[0] & outside
    assert not by_top and count == {2: 296, 3: 48, 4: 12, 5: 4, 6: 2}
    print('All 362 six-cube totals with multiple facets recovered from 30 interval cores.')
    print('18 cores recovered by hemisphere folds, four by direct subwords; six four-facet cores and the native pair remain.')


if __name__ == '__main__':
    for r in (2, 3):
        for sign in (0, 1):
            check_retraction(r, sign)
    for n in range(3, 8):
        print(f'{n}-cube: checked the face orders and units for {check_orders(n)} interval cores.', flush=True)
    check_six()
    for sign in (0, 1):
        check_raw_fold(sign)
    print('Checked both three-cube retractions as raw substitutions on all 27 declarations.')
