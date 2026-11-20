#!/usr/bin/env python3
"""Check fibre-stratified rank descents on all strict tableaux of a tensor of globes."""
import argparse
from itertools import product
from gray_globe_comparison import face, globe, strict_cells


def rank(side, degree):
    values = [0] * degree
    for (j, tag), (k, _) in side[-1][0]:
        assert j+k == degree-1
        # A globe has no composable pair of nonidentity 1-arrows. Its finite
        # path-rewrite height is one on the source arrow and zero on the target.
        if j < 2:
            values[j] += int(tag == 0)
        else:
            values[j] += 2 if tag == 0 else 1
    return tuple(values)


def check(m, n):
    descents = 0
    strata = set()
    for d in range(2, m+n+1):
        for cell in strict_cells((m,n), d):
            labels = cell[-1][0]
            if not labels or any(f[0] == 0 for f, _ in labels):
                continue  # identities, or a step using the separate object budget
            left, right = (rank(face(cell,i),d) for i in (0,1))
            first = min(f[0] for f, _ in labels) - 1
            assert left[:first] == right[:first] and left[first] > right[first]
            strata.add((d, first+1))
            descents += 1
    expected = {(d, j) for j, k in product(range(1,m+1),range(n+1)) if (d := j+k) >= 2}
    assert strata == expected
    print(f"D{m} tensor D{n}: {descents} nonidentity rank descents, "
          f"{len(strata)} distinct degree/first-stratum pairs, top degree {m+n}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("m", type=int, default=4, nargs="?")
    parser.add_argument("n", type=int, default=4, nargs="?")
    args = parser.parse_args()
    check(args.m, args.n)
