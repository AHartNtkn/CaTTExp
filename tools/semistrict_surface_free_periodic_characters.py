"""Build a finite permutation reading for a signed-span obstruction on a free deck.

The JSON format is that of semistrict_surface_free_tree_placements.py, with
steps interpreted as symmetrized top declarations. With optional counts the
rules have independent trivial integral markers of those target counts.
Returns a finite action, generator weights and the residual reading, or null
when all finite ordinary evaluations admit a comparison in the reflecting
sphere-and-disk family. The --height calculation uses exact localized groups.
"""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction
from itertools import product
import json
from pathlib import Path

from semistrict_surface_free_tree_placements import local_names, solve


def marked_columns(deck_rank, steps, face, relations, counts):
    if counts is None:
        return face, relations + steps
    if len(counts) != len(steps) or any(type(c) is not int or c < 0 for c in counts):
        raise ValueError("one nonnegative target count is required per marker")
    residual = list(face)
    rows = list(relations)
    for step, n in zip(steps, counts):
        residual.extend((w, i, -n*c) for w, i, c in step)
        for a in range(1, deck_rank + 1):
            rows.append([([a, *w], i, c) for w, i, c in step] +
                        [(w, i, -c) for w, i, c in step])
    return residual, rows


def evaluate(model, column):
    modulus, actions, weights = (model[k] for k in ("modulus", "actions", "weights"))
    degree = len(weights[0])
    perms = {}
    for a, perm in enumerate(actions, 1):
        if sorted(perm) != list(range(degree)):
            raise ValueError("deck action is not a permutation")
        perms[a] = perm
        inverse = [0] * degree
        for x, y in enumerate(perm):
            inverse[y] = x
        perms[-a] = inverse
    result = [0] * degree
    for word, i, c in column:
        for x in range(degree):
            y = x
            for a in word:
                y = perms[a][y]
            result[x] = (result[x] + c * weights[i][y]) % modulus
    return result


def certificate(deck_rank, modulus, rank, steps, face, relations, counts=None):
    residual, rows = marked_columns(deck_rank, steps, face, relations, counts)
    names, columns = local_names(deck_rank, modulus, rank, [residual, *rows])
    def value(x, column):
        return sum(c * x[names[name]] for name, c in column) % modulus
    states = {x for x in product(range(modulus), repeat=len(names))
              if all(value(x, col) == 0 for col in columns[1:])}
    pairs = [[] for _ in range(deck_rank)]
    for (w, i), j in names.items():
        if w:
            short = names[w[1:], i]
            pairs[abs(w[0]) - 1].append((j, short) if w[0] > 0 else (short, j))
    while True:
        viable = set(states)
        bins = []
        for edge in pairs:
            left, right = defaultdict(list), defaultdict(list)
            for x in sorted(states):
                left[tuple(x[i] for i, _ in edge)].append(x)
                right[tuple(x[j] for _, j in edge)].append(x)
            viable.difference_update(x for key in left.keys() - right.keys() for x in left[key])
            viable.difference_update(x for key in right.keys() - left.keys() for x in right[key])
            bins.append((left, right))
        if states == viable:
            break
        states = viable
    start = next((x for x in sorted(states) if value(x, columns[0])), None)
    if start is None:
        return None
    permutations = []
    for left, right in bins:
        perm = {}
        for key, xs in left.items():
            perm.update(zip(xs, right[key], strict=True))
        permutations.append(perm)
    # One orbit of a nonzero target character suffices; finite forward
    # permutation orbits already include all inverse images.
    orbit = [start]
    ids = {start: 0}
    for x in orbit:
        for perm in permutations:
            y = perm[x]
            if y not in ids:
                ids[y] = len(orbit)
                orbit.append(y)
    model = dict(modulus=modulus, actions=[[ids[perm[x]] for x in orbit] for perm in permutations],
                 weights=[[x[names[(), i]] for x in orbit] for i in range(rank)])
    model["residual"] = evaluate(model, residual)
    assert model["residual"][0] and all(not any(evaluate(model, row)) for row in rows)
    if counts is not None:
        model["marker_weights"] = [[-v % modulus for v in evaluate(model, step)] for step in steps]
        assert all(len(set(w)) == 1 for w in model["marker_weights"])
    return model


def height(p, n):
    if p < 2 or n < 0:
        raise ValueError("use a multiplier >= 2 and a nonnegative height")
    def act(letter, z, t):
        if letter == 1:
            return p*z, t
        if letter == -1:
            return z/p, t
        if letter == 2:
            return p*z, (t + z/p) % 1
        if letter == -2:
            return z/p, (t - z/(p*p)) % 1
        raise ValueError("invalid deck letter")
    def action(w, z=Fraction(1), t=Fraction(0)):
        for a in reversed(w):
            z, t = act(a, z, t)
        return z, t
    q, t = action([2] + [-1]*n)
    z, u = action([-1]*n)
    root = q - p*z, (t - p*u) % 1
    assert root == (0, Fraction(1, p**(n + 1)))
    for w in [(), (1, -2), (-2, 1, 2)]:
        assert action(w + (1,)) == action(w, Fraction(p))
        z, t = action(w + (2,))
        u, v = action(w, Fraction(p))
        assert (z - u, (t - v) % 1) == (0, Fraction(1, p))
    return dict(multiplier=p, depth=n, value=str(root[1]), order=root[1].denominator)


def audit():
    x = [([], 0, 1)]
    checks = 0
    for m in (2, 3, 4, 6):
        for a, b in product(range(2), repeat=2):
            data = dict(deck_rank=2, modulus=m, rank=1, steps=[], relations=[
                [([1], 0, 1), ([], 0, -a)], [([2], 0, 1), ([], 0, -b)]])
            for r in range(m):
                face = [([-1], 0, 1), ([2], 0, -r)]
                model = certificate(**data, face=face)
                assert (model is None) == bool(solve(**data, face=face))
                if model:
                    assert any(evaluate(model, face))
                checks += 1
    # A genuine noncommuting deck reading is needed to see (ab-ba)x.
    data = dict(deck_rank=2, modulus=2, rank=1, steps=[], relations=[],
                face=[([1, 2], 0, 1), ([2, 1], 0, -1)])
    model = certificate(**data)
    A, B = model["actions"]
    assert any(B[A[i]] != A[B[i]] for i in range(len(A)))
    marked = dict(deck_rank=2, modulus=2, rank=2, steps=[x], relations=[], counts=[1])
    assert certificate(**marked, face=[([1], 0, 1), ([2], 0, 1), ([], 0, 1)]) is None
    assert certificate(**marked, face=[([], 1, 1)]) is not None
    for p in (2, 3, 5):
        for n in range(32):
            assert height(p, n)["order"] == p**(n+1)
    print(f"{checks} independent primal/dual decisions; noncommuting cover of degree {len(A)};"
          " two marker tests and 96 exact division orders passed")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path)
    parser.add_argument("--height", nargs=2, type=int, metavar=("MULTIPLIER", "DEPTH"))
    args = parser.parse_args()
    if args.height:
        print(json.dumps(height(*args.height)))
    elif args.input:
        print(json.dumps(certificate(**json.loads(args.input.read_text()))))
    else:
        audit()
