"""Certify prescribed square relations on labels with fixed low stable homotopy groups."""

from argparse import ArgumentParser
from itertools import product
from math import gcd

from semistrict_surface_divisible_squares import valuation
from semistrict_surface_framed_relations import parity_mask
from semistrict_surface_lens_squares import row_reduce
from semistrict_surface_loop_eta import dependencies, eta_bounds


def roots(power, values, orders):
    result = []
    for value, k in zip(values, orders, strict=True):
        if not k:
            assert value == 0
            result.append(0)
            continue
        divisor = gcd(power, k)
        assert value % divisor == 0
        modulus = k // divisor
        root = -(value // divisor) * pow(power // divisor, -1, modulus) % modulus
        assert (power * root + value) % k == 0
        result.append(root)
    return tuple(result)


def realize(bottom, upper, columns, rows):
    n = len(bottom)
    low_rank, _, _ = eta_bounds(upper, columns, [0]*n, bottom)
    if any(len(row) != n for row in rows):
        raise ValueError("supply one coefficient per bottom generator in each relation")
    axes = [j for j, k in enumerate(bottom) if not k % 2]
    axis_mask = sum(1 << j for j in axes)
    images = [parity_mask([int(bool(k and x % k)) for x, k in zip(col, upper)])
              for col in columns]
    certificates = []
    basis = {}

    def insert(mask, level):
        coeff = 1 << len(certificates)
        v = mask
        while v:
            j = v.bit_length() - 1
            if j not in basis:
                basis[j] = v, coeff
                reading = [sum(columns[i][k] for i in axes if mask >> i & 1) for k in range(len(upper))]
                if level is None:
                    assert all(x % k == 0 if k else x == 0 for x, k in zip(reading, upper))
                certificates.append((mask, level, () if level is None else roots(2**level, reading, upper)))
                break
            vector, provenance = basis[j]
            coeff ^= provenance
            v ^= vector

    for v in dependencies(images, axes, (1 << len(upper)) - 1):
        insert(v, None)
    for level in sorted({valuation(bottom[i]) for i in axes if bottom[i]}):
        allowed = [j for j in axes if bottom[j] and valuation(bottom[j]) <= level]
        visible = parity_mask([int(bool(k and valuation(k) <= level)) for k in upper])
        for v in dependencies(images, allowed, visible):
            insert(v, level)
    assert low_rank + len(basis) == len(axes)

    recipes = []
    requested = [parity_mask(r) & axis_mask for r in rows]
    for mask in requested:
        remaining = mask
        recipe = 0
        while remaining:
            bit = remaining.bit_length() - 1
            if bit not in basis:
                return None
            v, provenance = basis[bit]
            remaining ^= v
            recipe ^= provenance
        selected = [cert for i, cert in enumerate(certificates) if recipe >> i & 1]
        reading = 0
        for x, _, _ in selected:
            reading ^= x
        assert reading == mask
        recipes.append(selected)
    rank = len(axes) - len(row_reduce(requested))
    return rank, rank - low_rank, recipes


def audit():
    checked = 0
    for bottom in product((0, 2, 4), repeat=2):
        upper = [2, 4]
        for columns in product(tuple(product((0, 1), (0, 2))), repeat=2):
            # Enumerate both coefficient characters directly, independently of surgery generators.
            separating = set()
            for s in (1, 2):
                mod = 2**s
                for char in product(range(mod), repeat=2):
                    if any(k*x % mod for k, x in zip(upper, char)):
                        continue
                    v = [int(bool(sum(x*y for x, y in zip(col, char)) % mod)) for col in columns]
                    if all(any(z % 2 == b and z*k % mod == 0 for z in range(mod)) for b, k in zip(v, bottom)):
                        separating.add(parity_mask(v))
            for rows in product(tuple(product((0, 1), repeat=2)), repeat=2):
                allowed = not any((parity_mask(row) & v).bit_count() % 2 for v in separating for row in rows)
                assert (realize(bottom, upper, columns, rows) is not None) == allowed
                checked += 1
    # A cyclic bottom factor with an odd part and a signed representative of its Hopf image.
    assert realize([6], [12], [[-6]], [[1]]) == (0, 0, [[(1, 1, (3,))]])
    print(f"Checked {checked:,} prescribed relation lists against direct cyclic character search.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--bottom-orders", nargs="*", type=int)
    parser.add_argument("--orders", nargs="*", type=int)
    parser.add_argument("--column", action="append", nargs="*", type=int, default=[])
    parser.add_argument("--relation", action="append", nargs="*", type=int, default=[])
    args = parser.parse_args()
    if args.orders is None and args.bottom_orders is None and not (args.column or args.relation):
        audit()
    elif args.orders is None or args.bottom_orders is None:
        parser.error("supply bottom and upper cyclic orders and the Hopf columns")
    else:
        try:
            result = realize(args.bottom_orders, args.orders, args.column, args.relation)
        except ValueError as exc:
            parser.error(str(exc))
        if result is None:
            print("Impossible: a requested relation survives in the common two-stage type.")
        else:
            rank, invisible, recipes = result
            print(f"Realizable. Raw square dimension {rank}; dimension killed by every threefold loop target {invisible}.")
            for i, recipe in enumerate(recipes, 1):
                print(f"Disk {i}:", recipe)
