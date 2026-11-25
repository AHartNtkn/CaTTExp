"""Find elementary three-stage targets detecting the double alpha_1 composite."""

from argparse import ArgumentParser
from math import factorial, isqrt


def linear(p, *terms):
    result = {}
    for scalar, poly in terms:
        for monomial, value in poly.items():
            result[monomial] = (result.get(monomial, 0) + scalar*value) % p
    return {m: v for m, v in result.items() if v}


def reduced_power(poly, p):
    # Cartan in H*((CP^infinity)^2): replace one degree-two root by its p-th power.
    terms = []
    for (i, j), c in poly.items():
        terms.extend(((i*c, {(i+p-1, j): 1}), (j*c, {(i, j+p-1): 1})))
    return linear(p, *terms)


def coefficient(p, a, b):
    """Test whether P^1(kappa) is an earlier transgression and return its coefficient."""
    k = (p+1)//2
    invariant = linear(p, (a, reduced_power({(1, 1): 1}, p)), (b, {(k, k): 1}))
    boundary = {(i+k-1, j+k-1): c for (i, j), c in invariant.items()}
    image = reduced_power(invariant, p)
    if not boundary:
        return 0 if not image else None
    monomial = next(iter(boundary))
    multiple = image.get(monomial, 0) * pow(boundary[monomial], -1, p) % p
    if image == linear(p, (multiple, boundary)):
        return multiple
    return None


def audit():
    checked = 0
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
        for a in range(1, p):
            for b in range(p):
                c = coefficient(p, a, b)
                assert (c is not None) == (b*b % p == 4*a*a % p)
                checked += 1
        signs = {pow(z, (p-1)//2, p) for z in range(1, p)}
        assert signs == {1, p-1}
        shifts = {reduced_power({(p-1, 0): j}, p).get((2*p-2, 0), 0) for j in range(p)}
        assert shifts == set(range(p))
    # Pull back powers of the projective class to products of two-spheres.
    for j in range(1, 10):
        coeffs = {0: 1}
        for _ in range(j):
            new = {}
            for mask, c in coeffs.items():
                for bit in range(j):
                    if not mask & (1 << bit):
                        target = mask | (1 << bit)
                        new[target] = new.get(target, 0) + c
            coeffs = new
        assert coeffs == {(1 << j)-1: factorial(j)}
    print(f"Checked {checked:,} candidate invariants by Cartan on two polynomial roots.")
    print("Checked generator rescalings, every rank-three obstruction shift, and nine projective degrees.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int)
    parser.add_argument("--primary", type=int, default=1)
    parser.add_argument("--product", type=int)
    args = parser.parse_args()
    if args.prime is None and args.primary == 1 and args.product is None:
        audit()
    elif args.prime is None or args.prime < 3 or args.prime % 2 == 0 or any(
            args.prime % k == 0 for k in range(3, isqrt(args.prime)+1, 2)):
        parser.error("supply an odd prime")
    else:
        p = args.prime
        a = args.primary % p
        b = (-2*a if args.product is None else args.product) % p
        c = coefficient(p, a, b)
        if not a:
            print("The first alpha_1 already maps to zero.")
        elif c is None:
            print("The fibre class has nonzero transgression. This first invariant cannot detect the composite.")
        else:
            print(f"Target homotopy degrees 4, {2*p+1}, {4*p-2}, each cyclic of order {p}.")
            print(f"P^1(kappa) = {c} * u^{(p-1)//2} * kappa. The secondary class extends.")
