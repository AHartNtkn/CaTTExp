"""Bound universal marked-square comparisons in the first unstable shell."""

from argparse import ArgumentParser
from itertools import product

from semistrict_surface_divisible_squares import valuation


# 2-primary cyclic factors in sphere stems m-2 and m-1, respectively.
# Isaksen–Wang–Xu, Stable homotopy groups of spheres, Tables 1 and 2.
SPHERE_STEMS = {
    5: ((8,), ()),
    9: ((16,), (2, 2)),
    11: ((2, 2, 2), (2,)),
    13: ((8,), ()),
    15: ((), (2, 2)),
    31: ((), (2,)),
    63: ((), (2, 2, 2, 2)),
}


def tower_bound(bottom, rank, stable_orders, kernel_orders, ambiguity_orders):
    if bottom % 2 == 0 or not 2 <= rank < bottom or bottom in (3, 7):
        raise ValueError("use an odd bottom dimension other than 3 or 7 and 2 <= rank < bottom")
    if any(k < 0 for k in stable_orders):
        raise ValueError("stable cyclic orders must be nonnegative (zero denotes a free factor)")
    if any(k < 2 or k & (k - 1) for k in (*kernel_orders, *ambiguity_orders)):
        raise ValueError("sphere factors must have nontrivial power-of-two orders")
    lift_level = 1 + max((valuation(k) for k in stable_orders if k), default=0)
    mark_level = 1 + max(map(valuation, ambiguity_orders), default=0)
    count = 2 ** len(ambiguity_orders)
    if bottom in (15, 31, 63) and not kernel_orders and all(k == 2 for k in ambiguity_orders):
        count = 1
    level = max(lift_level, mark_level) + bool(kernel_orders)
    return rank + 2 * bottom - 1, bottom * 2 - rank - 1, level, count


def elements(orders):
    return product(*(range(order) for order in orders))


def normalize(p, coords, modulus, orders, twists):
    # Each lift v_j of the j-th quotient generator satisfies order_j*v_j = twist_j*p0.
    parts = [divmod(x, order) for x, order in zip(coords, orders)]
    return ((p + sum(t * carry for t, (carry, _) in zip(twists, parts))) % modulus,
            tuple(rem for _, rem in parts))


def check_transitions():
    comparisons = 0
    for kernel in (2, 4, 8):
        for orders in ((), (2,), (4,), (2, 2), (2, 4)):
            for level in range(1 + max(map(valuation, orders), default=0), 6):
                modulus = min(kernel, 2 ** level)
                following = min(kernel, 2 ** (level + 1))
                for twists in product(range(modulus), repeat=len(orders)):
                    # The next extension receives p0 -> 2*p0' and v_j -> v_j'.
                    next_twists = tuple(2 * t for t in twists)
                    doubles = {normalize(2 * p, [2 * x for x in coords],
                                         following, orders, next_twists)
                               for p in range(following) for coords in elements(orders)}
                    for p in range(modulus):
                        for coords in elements(orders):
                            mark = tuple(x % 2 for x in coords)
                            difference = normalize(2 * p, [x-y for x, y in zip(coords, mark)],
                                                   following, orders, next_twists)
                            assert difference in doubles
                            comparisons += 1
    return comparisons


def audit():
    assert tower_bound(5, 2, [0, 12, 8], *SPHERE_STEMS[5]) == (11, 7, 5, 1)
    assert tower_bound(9, 2, [], *SPHERE_STEMS[9]) == (19, 15, 3, 4)
    for m in (15, 31, 63):
        for n in range(2, m):
            assert tower_bound(m, n, [12], *SPHERE_STEMS[m]) == (n+2*m-1, 2*m-n-1, 3, 1)
    # For C_k the transition from the level-one cokernel sends j to 2^(s-1)*j.
    for k in range(1, 129):
        for s in range(1, 10):
            multiples = {(2 ** s * j) % k for j in range(k)}
            assert all((2 ** (s-1) * j) % k in multiples for j in range(k)) == (s > valuation(k))
    print(f"{check_transitions():,} comparisons of marked lifts across finite group extensions passed")
    print("Cyclic character transitions through order 128 and the tabulated bound examples passed")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--bottom", type=int)
    parser.add_argument("--rank", type=int, default=2)
    parser.add_argument("--stable-orders", type=int, nargs="*", default=[])
    parser.add_argument("--kernel-orders", type=int, nargs="*")
    parser.add_argument("--ambiguity-orders", type=int, nargs="*")
    args = parser.parse_args()
    if args.bottom is None:
        audit()
    else:
        if args.kernel_orders is None and args.ambiguity_orders is None and args.bottom in SPHERE_STEMS:
            factors = SPHERE_STEMS[args.bottom]
        elif args.kernel_orders is not None and args.ambiguity_orders is not None:
            factors = (args.kernel_orders, args.ambiguity_orders)
        else:
            parser.error("supply both 2-primary sphere decompositions for an untabulated bottom dimension")
        try:
            degree, stem, level, count = tower_bound(args.bottom, args.rank, args.stable_orders, *factors)
        except ValueError as exc:
            parser.error(str(exc))
        print(f"old degree {degree}; local stable stem {stem}; test level {level}; at most {count} comparisons")
