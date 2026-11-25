"""Compute cyclic binary readings of Hopf exchanges with signed cell relations."""

from argparse import ArgumentParser
from itertools import permutations, product

from semistrict_surface_divisible_squares import first_stage
from semistrict_surface_framed_relations import parity_mask
from semistrict_surface_invertible_probes import parity


def collapse(weight, signs, moduli, hopf):
    return tuple((w + sum(bit * image[j] for bit, image in zip(signs, hopf, strict=True))) % modulus
                 for j, (w, modulus) in enumerate(zip(weight, moduli, strict=True)))


def block_parity(order, counts):
    return sum(counts[left]*counts[right] for i, left in enumerate(order)
               for right in order[i+1:] if left > right) % 2


def check_transports():
    moduli = (4, 8)
    hopf = ((2, 4), (0, 4))
    orders = list(permutations(range(3)))
    checks = 0
    for bits in product(range(2), repeat=6):
        # The same table admits positive lifts of different cardinalities.
        counts = [[bits[3*k+j] + 2*int(j == k) for j in range(3)] for k in range(2)]
        for source, target in product(orders, repeat=2):
            signs = []
            shuffle = []
            for row in counts:
                initial = [(j, i) for j in source for i in range(row[j])]
                final = [(j, i) for j in target for i in range(row[j])]
                moved = [(j, row[j]-1-i if j == 1 else i) for j, i in initial]
                signs.append(parity([final.index(token) for token in moved]))
                shuffle.append(block_parity(source, row) ^ block_parity(target, row))
            weight = (source[0]+target[1], 3*source[2]-target[0])
            intrinsic = [row[1]*(row[1]-1)//2 % 2 for row in counts]
            reading = collapse(weight, signs, moduli, hopf)
            assert reading == collapse(collapse(weight, intrinsic, moduli, hopf), shuffle, moduli, hopf)
            # Move arbitrarily chosen signs from the lift into the independent weights.
            for changes in product(range(2), repeat=2):
                new_signs = [a ^ b for a, b in zip(signs, changes, strict=True)]
                assert reading == collapse(collapse(weight, changes, moduli, hopf), new_signs, moduli, hopf)
                checks += 1
    return checks


def audit():
    print(f'Checked {check_transports():,} coloured transport and lift readings in C4 x C8.')
    count = 0
    for a in range(8):
        rows = [[1, -(2**a)]]
        level, char, upper = first_stage(rows, 1, 1, 1)
        assert (level, char) == (a+1, 1)
        assert (2**a * upper[0]) % 2**level == 2**(level-1)
        for s in range(1, 10):
            allowed = any((2**a * t) % 2**s == 2**(s-1) for t in range(2**s))
            assert allowed == (s >= level)
            count += 1
    assert first_stage([[1]], 1, 0, 1) is None
    print(f'Checked {count} cyclic-exponent cutoffs and a disk killing the Hopf class.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--shell', type=int, nargs='+', help='coefficients of the bottom Hopf exchanges')
    parser.add_argument('--upper', type=int, default=0, help='number of independent upper spheres')
    parser.add_argument('--row', type=int, nargs='+', action='append', default=[])
    args = parser.parse_args()
    if args.shell is None and not args.row and not args.upper:
        audit()
    elif not args.shell or args.upper < 0 or any(len(row) != len(args.shell)+args.upper for row in args.row):
        parser.error('supply one shell coefficient per bottom sphere, a nonnegative upper count and matching rows')
    else:
        result = first_stage(args.row, len(args.shell), args.upper, parity_mask(args.shell))
        if result:
            level, char, upper = result
            print(f'Least cyclic order {2**level}. Root bits {[(char >> i) & 1 for i in range(len(args.shell))]}. Upper readings {upper}.')
        else:
            print('The marked Hopf exchange has a raw filler.')
