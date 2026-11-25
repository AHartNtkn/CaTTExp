"""Compute degree-six paired axes from finite first-Hopf image and its 2-height filtration.

With --input FILE, supply bottom primary orders (0 for free), images as bit
masks, and divisible[k-1] spanning im(q) intersect 2**k B as bit masks.
Omit trailing zero spaces. With --laurent, give the powers of t in a sum
over F_2 for the two-axis cover of Researcher Response 232.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from semistrict_surface_bracket_axes import factors, paired_axes


def span(generators):
    values = {0}
    for v in generators:
        if type(v) is not int or v < 0:
            raise ValueError('a vector must be a nonnegative bit mask')
        values.update([x ^ v for x in values])
    return values


def filtered_axes(bottom, images, divisible):
    if len(bottom) != len(images):
        raise ValueError('each bottom generator needs one image')
    image = span(images)
    levels = [image]
    for generators in divisible:
        level = span(generators)
        if not level <= levels[-1]:
            raise ValueError('the divisibility filtration must be descending in the image')
        levels.append(level)
    height = {v: k for k, level in enumerate(levels) for v in level if v}
    height[0] = len(levels)  # Larger than every finite depth.
    for n, v in zip(bottom, images):
        if type(n) is not int or (n and len(factors(n)) != 1) or (n % 2 and v):
            raise ValueError('use primary cyclic orders with zero Hopf image at odd orders')
    basis = [[int(i == j) for j in range(len(bottom))] for i in range(len(bottom))]
    orders = sorted(range(len(bottom)), key=lambda i: (not bottom[i], bottom[i], i))
    residual = list(images)
    shears = {0: ()}
    for i in orders:
        v = images[i]
        offset = max(shears, key=lambda w: height[v ^ w])
        residual[i] = v ^ offset
        for j in shears[offset]:
            basis[i] = [a + b for a, b in zip(basis[i], basis[j])]
        if residual[i]:
            additions = {w ^ residual[i]: js + (i,) for w, js in shears.items()}
            shears.update(additions)
    return dict(axes=[[n, height[v] + 1 if v else 0] for n, v in zip(bottom, residual)],
                bottom_basis=basis, images=residual)


def laurent(powers, attached):
    # Parity counts monomials over F_2, including negative powers.
    support = set()
    for j in powers:
        support.symmetric_difference_update({j})
    value = len(support) % 2
    derivative = sum(support) % 2
    raw = (value == derivative == 0) if attached else not support
    binary = 'fills' if raw else 'survives'
    if attached and not value and derivative:
        binary = 'fills iff the fundamental bracket fills on axes (4,2) and (4,1)'
    return dict(support=sorted(support), raw_fills=raw, binary=binary, joined_fills=True)


def audit():
    # Compare with explicit finite middle groups, including non-coordinate
    # inputs to the filtration. Independently check heights of all image sums.
    middle = [2, 4, 8]
    bottom = [4, 0, 2]
    counts = 0
    for images in product(range(8), repeat=len(bottom)):
        image = span(images)
        levels = [[v for v in image if v % (2**k) == 0] for k in (1, 2)]
        data = filtered_axes(bottom, images, levels)
        eta = [[((v >> j) & 1) * (n // 2) for j, n in enumerate(middle)] for v in images]
        assert data['axes'] == [list(a) for a in paired_axes(bottom, middle, eta)['axes']]
        for i, row in enumerate(data['bottom_basis']):
            actual = 0
            for c, v in zip(row, images):
                if c % 2:
                    actual ^= v
            assert actual == data['images'][i]
            assert all(not bottom[i] or (n and bottom[i] * c % n == 0) or not c
                       for n, c in zip(bottom, row))
        nonzero = [(v, s) for v, (_, s) in zip(data['images'], data['axes']) if v]
        for mask in range(1, 2**len(nonzero)):
            chosen = [entry for j, entry in enumerate(nonzero) if mask & (1 << j)]
            v = 0
            for w, _ in chosen:
                v ^= w
            assert (v & -v).bit_length() == min(s for _, s in chosen)
        counts += 1
    # Quotient C4{c} + (F2)^n by all translates c-z_i-z_(i+1).
    # Enumerate the relation subgroup directly, independently of derivatives.
    words = 0
    for sheets in (2, 4, 6, 8):
        relations = {(0, 0)}
        for j in range(sheets):
            vector = (1 << j) ^ (1 << ((j+1) % sheets))
            relations = {((c+k) % 4, w ^ (vector if k % 2 else 0))
                         for c, w in relations for k in range(4)}
        for mask in range(1 << sheets):
            powers = [j - sheets for j in range(sheets) if mask & (1 << j)]
            result = laurent(powers, True)
            assert result['raw_fills'] == ((0, mask) in relations)
            assert result['binary'].startswith('fills iff') == ((1, mask) in relations)
            assert laurent(powers+powers, False)['raw_fills']
            words += 1
    return counts, words


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--input', type=Path)
    mode.add_argument('--laurent', type=int, nargs='*')
    parser.add_argument('--attached', action='store_true')
    args = parser.parse_args()
    if args.attached and args.laurent is None:
        parser.error('--attached applies to --laurent')
    if args.input:
        print(json.dumps(filtered_axes(**json.loads(args.input.read_text()))))
    elif args.laurent is not None:
        print(json.dumps(laurent(args.laurent, args.attached)))
    else:
        counts, words = audit()
        print(f'{counts} filtered actions and {words} finite-cover Laurent comparisons checked.')
