"""Compute primary extension readings on finite skeleta of BC_4 and BC_8.

--length L is the bottom square degree on the suspended cone. Use --skeleton
to truncate the lens space; the default contains the entire relevant range.
"""
from argparse import ArgumentParser
from itertools import product
from math import comb, gcd


def square(degree, op):
    # z_2a = v^a and z_(2a+1) = u v^a. Sq^1 u = Sq^1 v = 0.
    return (op % 2 == 0 and op // 2 <= degree // 2 and
            comb(degree // 2, op // 2) % 2 == 1)


def row_reduce(rows):
    pivots = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return pivots


def primary_extensions(length, skeleton):
    top = length + 1
    width = min(skeleton, length)
    rows = []
    for a in range(1, width + 1):
        for s in range(1, top - a):
            r = top - a - s
            if r >= 2 * s:
                continue
            row = 0
            if a + s <= width and square(a, s):
                row ^= 1 << (a + s - 1)
            for j in range(r // 2 + 1):
                if (a + j <= width and square(a, j) and
                        comb(s - j - 1, r - 2*j) % 2):
                    row ^= 1 << (a + j - 1)
            rows.append(row)
    pivots = row_reduce(rows)
    kernel = []
    for col in range(width):
        if col not in pivots:
            vector = 1 << col
            for lead, equation in sorted(pivots.items()):
                if (vector & equation).bit_count() % 2:
                    vector |= 1 << lead
            kernel.append(vector)
    # Changing the chosen lift of z_top adds the original top operations.
    change = sum(1 << (a-1) for a in range(1, width + 1)
                 if skeleton >= top and square(a, top-a))
    span = row_reduce([change] if change else [])
    basis = []
    for vector in kernel:
        residual = vector
        for k, v in sorted(span.items(), reverse=True):
            if residual & (1 << k):
                residual ^= v
        if residual:
            span[residual.bit_length()-1] = residual
            basis.append(vector)
    return basis


def cochain_check(n):
    # Normalized group cochains. Check an explicit primitive of the inflated
    # carry cocycle, and one for the square of the mod-two character.
    checked = 0
    for a, b in product(range(n), repeat=2):
        ab = (a+b) % n
        du = (a//2 + b//2 + ab//2) % 2
        assert du == (a % 2) * (b % 2)
        dv = (a//4 + b//4 + ab//4) % 2
        assert dv == ((a % 4 + b % 4) // 4)
        checked += 1
    return checked


def audit():
    cochains = sum(cochain_check(n) for n in (8, 16, 24, 32))
    print(f'Checked {cochains} pairs on normalized bar cochains for cyclic quotients to C4.')
    for length in (16, 32, 64, 128):
        shallow = primary_extensions(length, length // 2)
        full = primary_extensions(length, length + 1)
        assert shallow == [1] and 1 in full
        # Every additional extension has its support in the image of the
        # reduced circle transfer, i.e. odd cohomology degrees above one.
        for vector in full:
            if vector != 1:
                assert all(k >= 2 and k % 2 == 0 for k in range(vector.bit_length())
                           if (vector >> k) & 1)
        # In the even submodule Sq^1(v^(L/2)) has zero top coefficient.
        assert not any((v >> (length-1)) & 1 for v in full)
        for a in range(1, length+1):
            for k in range(length+2-a):
                # Fibre integration z_(2s+1) -> v^s. On the reduced source
                # this coordinate exists only for s>0. Compare both orders.
                lhs = square(a, k) and (a+k) % 2 == 1 and a+k > 1
                rhs = a % 2 == 1 and a > 1 and square(a-1, k)
                assert bool(lhs) == bool(rhs)
        print(f'L={length}: {len(full)} primary extension directions in the full range; '
              f'{len(shallow)} through skeleton {length // 2}.')
    count = 0
    for orders in ((0, 2, 4), (2, 6, 12, 24), (3, 4, 8), (8, 10, 16)):
        choices = [[k for k in range(4) if not q or q*k % 4 == 0] for q in orders]
        characters = list(product(*choices))
        for v in product(*[range(gcd(q, 2)) for q in orders]):
            detected = any(sum(x*y for x, y in zip(v, c)) % 2 for c in characters)
            # Compare against actual order-two elements, reduced modulo 2A.
            images = [{0, (q//2) % gcd(q, 2)} if q else {0} for q in orders]
            assert detected != all(x in pool for x, pool in zip(v, images))
            count += 1
    print(f'{count} mod-two vectors tested against every mod-four character and order-two image.')
    for length in range(6, 33, 2):
        basis = primary_extensions(length, length + 1)
        assert any(row & 1 for row in basis) == (length & (length-1) == 0)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--length', type=int)
    parser.add_argument('--skeleton', type=int)
    args = parser.parse_args()
    if args.length is None and args.skeleton is None:
        audit()
    elif args.length is None or args.length < 2 or (args.skeleton is not None and args.skeleton < 1):
        parser.error('supply a length >= 2 and a positive skeleton dimension')
    else:
        basis = primary_extensions(args.length, args.skeleton or args.length + 1)
        for vector in basis:
            print([i + 1 for i in range(vector.bit_length()) if vector & (1 << i)])
