"""Compute Hilton multiplicities and rank-two odd-primary shell kernels in Toda's first range."""

from argparse import ArgumentParser
from collections import Counter
from itertools import product
from math import isqrt


def hilton_counts(spheres, shell):
    """Logarithmic derivative of the weighted tensor-algebra/Witt product identity."""
    weights = Counter(m-1 for m in spheres if m <= shell)
    tensor = [1]
    counts = {}
    for degree in range(1, shell):
        tensor.append(sum(k*tensor[degree-w] for w, k in weights.items() if w <= degree))
        logarithmic = sum(w*k*tensor[degree-w] for w, k in weights.items() if w <= degree)
        earlier = sum(w*k for w, k in counts.items() if degree % w == 0)
        count, rem = divmod(logarithmic - earlier, degree)
        assert rem == 0 and count >= 0
        if count:
            counts[degree] = count
    return {w+1: count for w, count in counts.items()}


def odd_kernel(counts, shell, p):
    if p <= 2 or any(p % k == 0 for k in range(2, isqrt(p)+1)):
        raise ValueError("use an odd prime")
    result = {}
    for m, copies in counts.items():
        if m % 2:
            continue
        stem = shell-m
        if stem > 2*p*(p-1)-3:
            raise ValueError(f"sphere dimension {m} is beyond the tabulated Toda range for prime {p}")
        i, rem = divmod(stem+2, 2*(p-1))
        if rem == 0 and m//2 <= i < p:
            result[m] = copies
    return result


def integral_kernel(counts, shell):
    if shell == 11:
        return {}
    if shell != 10:
        raise ValueError("the integral calculation covers shell dimensions 10 and 11")
    return {p: counts[m] for m, p in ((4, 3), (5, 2)) if m in counts}


def lyndon_counts(spheres, shell):
    counts = Counter()
    for length in range(1, (shell-1)//(min(spheres)-1)+1):
        for word in product(range(len(spheres)), repeat=length):
            m = 1 + sum(spheres[j]-1 for j in word)
            if m <= shell and all(word < word[i:]+word[:i] for i in range(1, length)):
                counts[m] += 1
    return counts


def audit():
    wedges = 0
    for spheres in product((3, 4, 5, 6), repeat=3):
        for shell in range(3, 14):
            counts = hilton_counts(spheres, shell)
            assert counts == lyndon_counts(spheres, shell)
            if shell == 10:
                c = Counter(spheres)
                expected = {3: c[4], 2: c[5]+c[3]*(c[3]-1)//2}
                assert integral_kernel(counts, shell) == {p: n for p, n in expected.items() if n}
            wedges += 1
    readings = 0
    for p in (3, 5, 7, 11, 13):
        bound = 2*p*(p-1)-3
        for a in range(2, p+2):
            # Build the odd-sphere stem table and record images under double suspension.
            source = {2*i*(p-1)-1: 1 for i in range(1, p)}
            source.update({2*i*(p-1)-2: 0 for i in range(a, p)})
            for k in range(bound+1):
                actual = odd_kernel({2*a: 1}, 2*a+k, p)
                assert bool(actual) == (source.get(k) == 0)
                readings += 1
        assert odd_kernel({3: 2, 4: 1, 5: 3, 6: 4}, 4*p-2, p) == {4: 1}
    print(f"Checked {wedges} weighted wedge decompositions against primitive Lyndon words.")
    print(f"Checked {readings:,} odd-primary readings against the two Toda series and their suspension images.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--spheres", type=int, nargs="+")
    parser.add_argument("--shell", type=int)
    parser.add_argument("--prime", type=int)
    args = parser.parse_args()
    if args.spheres is None and args.shell is None and args.prime is None:
        audit()
    elif args.shell is None or not args.spheres or min(args.spheres) < 3 or args.shell < 3:
        parser.error("give the suspended sphere dimensions (at least three) and a shell dimension >= 3")
    else:
        counts = hilton_counts(args.spheres, args.shell)
        try:
            if args.prime is None:
                print("Raw test group, number of cyclic factors by prime:", integral_kernel(counts, args.shell))
            else:
                print("Order-p factors by Hilton sphere dimension:", odd_kernel(counts, args.shell, args.prime))
        except ValueError as exc:
            parser.error(str(exc))
