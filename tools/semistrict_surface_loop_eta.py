"""Compute rank-two loop-label squares from bottom orders and the local Hopf action."""

from argparse import ArgumentParser
from itertools import product

from semistrict_surface_divisible_squares import valuation
from semistrict_surface_framed_relations import parity_mask
from semistrict_surface_lens_squares import row_reduce


def restrict_characters(characters, forbidden):
    pivots = {}
    for character in characters:
        while character & forbidden:
            bit = (character & forbidden).bit_length() - 1
            if bit not in pivots:
                pivots[bit] = character
                break
            character ^= pivots[bit]
        else:
            yield character


def dependencies(images, allowed, visible):
    """Relations of the visible eta coordinates among the allowed bottom generators."""
    pivots = {}
    for j in allowed:
        value, source = images[j] & visible, 1 << j
        while value:
            bit = value.bit_length() - 1
            if bit not in pivots:
                pivots[bit] = value, source
                break
            v, x = pivots[bit]
            value ^= v
            source ^= x
        else:
            yield source


def surgery_relations(images, orders, bottom_orders):
    relations = list(dependencies(images, range(len(images)), (1 << len(orders)) - 1))
    for level in sorted({valuation(k) for k in bottom_orders if k and k % 2 == 0}):
        allowed = [j for j, k in enumerate(bottom_orders) if k and valuation(k) <= level]
        visible = parity_mask([int(bool(k and valuation(k) <= level)) for k in orders])
        relations.extend(dependencies(images, allowed, visible))
    return row_reduce(relations)


def eta_bounds(orders, columns, shell, bottom_orders=None):
    # columns are the actual images of bottom generators in H = pi_(d+1) K.
    if any(k < 0 for k in orders):
        raise ValueError("cyclic orders must be nonnegative, with zero for a free factor")
    if len(columns) != len(shell):
        raise ValueError("supply one shell coordinate per eta column")
    images = []
    known_bottom = bottom_orders is not None
    if bottom_orders is None:
        bottom_orders = [2] * len(shell)
    if len(bottom_orders) != len(shell) or any(k < 0 for k in bottom_orders):
        raise ValueError("supply one nonnegative bottom cyclic order for each column")
    for order, column in zip(bottom_orders, columns, strict=True):
        if len(column) != len(orders):
            raise ValueError("each eta column needs one coordinate for every cyclic order")
        if any((2*x % k if k else x) for k, x in zip(orders, column)):
            raise ValueError("each eta image must have order dividing two")
        images.append(parity_mask([int(bool(x % k)) if k else 0 for k, x in zip(orders, column)]))
        if order % 2 and images[-1]:
            raise ValueError("an odd-order bottom generator has zero eta image")
    image = 0
    for coefficient, full in zip(shell, images, strict=True):
        if coefficient % 2:
            image ^= full
    certified = []
    levels = sorted({valuation(k) for k in orders if k and k % 2 == 0})
    for level in levels:
        forbidden = parity_mask([int(k != 0 and valuation(k) < level) for k in bottom_orders])
        available = (parity_mask([(v >> j) & 1 for v in images])
                     for j, k in enumerate(orders) if k and k % 2 == 0 and valuation(k) <= level)
        certified.extend(restrict_characters(available, forbidden))
    shell_bits = parity_mask(shell)
    detected = any((shell_bits & c).bit_count() % 2 for c in certified)
    status = "zero" if not image else ("nonzero" if detected else "undetermined")
    low = len(row_reduce(certified))
    if known_bottom:
        relations = surgery_relations(images, orders, bottom_orders)
        high = len(images) - len(relations)
        assert high == low and all((r & c).bit_count() % 2 == 0 for r in relations.values() for c in certified)
        return low, high, "nonzero" if detected else "zero"
    return low, len(row_reduce(images)), status


def audit():
    count = 0
    for orders in product((0, 2, 4, 6, 8), repeat=2):
        twos = [(0, k//2) if k and not k % 2 else (0,) for k in orders]
        for columns in product(tuple(product(*twos)), repeat=2):
            images = set()
            residues = set()
            answers = []
            for shell in product(range(2), repeat=2):
                value = tuple(sum(x*y for x, y in zip(shell, coord)) % (k or 1)
                              for coord, k in zip(zip(*columns), orders))
                images.add(value)
                doubles = [set((2*j) % (k or 1) for j in range(k or 1)) for k in orders]
                residue = tuple(x not in subset for x, subset in zip(value, doubles))
                residues.add(residue)
                answers.append(eta_bounds(orders, columns, shell))
                assert answers[-1][2] == ("zero" if not any(value) else
                                          "nonzero" if any(residue) else "undetermined")
                count += 1
            assert all(2**low == len(residues) and 2**high == len(images) for low, high, _ in answers)
    mixed = 0
    for bottom in product((0, 2, 4), repeat=2):
        orders = [2, 4]
        for columns in product(tuple(product((0, 1), (0, 2))), repeat=2):
            valid = set()
            for level in (1, 2):
                modulus = 1 << level
                char_images = [[j for j in range(modulus) if j*k % modulus == 0] for k in orders]
                for char in product(*char_images):
                    readings = tuple(sum(x*y for x, y in zip(col, char)) % modulus for col in columns)
                    bits = tuple(int(x != 0) for x in readings)
                    if all(any(z % 2 == bit and k*z % modulus == 0 for z in range(modulus))
                           for bit, k in zip(bits, bottom)):
                        valid.add(parity_mask(bits))
            for shell in product(range(2), repeat=2):
                low, high, answer = eta_bounds(orders, columns, shell, bottom)
                assert low == len(row_reduce(valid))
                assert (answer == "nonzero") == any((v & parity_mask(shell)).bit_count() % 2 for v in valid)
                assert low == high
                mixed += 1
    framed = 0
    for r in range(1, 8):
        for s in range(1, 9):
            modulus = 2**s
            # Cellular Ext representative for the spherical surgery, and all coboundaries.
            image = {2**r * z % modulus for z in range(modulus)}
            assert ((modulus // 2) in image) == (r < s)
            exact = eta_bounds([modulus], [[modulus // 2]], [1], [2**r])
            assert (exact[2] == "zero") == (r < s)
            framed += 1
    # Two independent eta values can cancel in the visible coordinates at an intermediate level.
    example = eta_bounds([2, 4], [[1, 0], [1, 2]], [1, 1], [2, 2])
    assert example == (1, 1, "zero")
    print(f"Verified {framed} two-stage surgery coefficient maps and mixed relations.")
    print(f"Verified {mixed:,} coefficient-lifting cases by enumeration of both homomorphisms.")
    print(f"Verified {count:,} shell classifications against the cyclic groups and their doubles.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--orders", nargs="*", type=int)
    parser.add_argument("--bottom-orders", nargs="*", type=int,
                        help="bottom cyclic orders, with zero for free; omit for bounds independent of these orders")
    parser.add_argument("--column", action="append", nargs="*", type=int, default=[])
    parser.add_argument("--shell", nargs="*", type=int)
    args = parser.parse_args()
    if args.orders is None and args.shell is None and not args.column and args.bottom_orders is None:
        audit()
    elif args.orders is None or args.shell is None:
        parser.error("supply --orders and --shell together")
    else:
        try:
            low, high, status = eta_bounds(args.orders, args.column, args.shell, args.bottom_orders)
        except ValueError as exc:
            parser.error(str(exc))
        print(f"Square-group dimension in [{low}, {high}]. The chosen raw square is {status}.")
