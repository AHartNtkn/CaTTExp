"""Find the cyclic tests for a specified square in a two-stage local label."""

from argparse import ArgumentParser
from itertools import product
from math import inf

from semistrict_surface_divisible_squares import valuation

from semistrict_surface_lens_squares import row_reduce
from semistrict_surface_loop_eta import eta_bounds


def reduce_action(bottom, upper, columns, shell):
    # Validate the integral input and independently compare the full raw quotient.
    dimension, _, status = eta_bounds(upper, columns, shell, bottom)
    source = sorted((valuation(k) if k else inf, j) for j, k in enumerate(bottom)
                    if k % 2 == 0)
    target = sorted((valuation(k), j) for j, k in enumerate(upper) if k and k % 2 == 0)
    matrix = [[bool(columns[j][i] % upper[i]) for _, j in source] for _, i in target]
    coords = [shell[j] % 2 for _, j in source]
    pivots = []
    occupied = set()
    for j, (right, _) in enumerate(source):
        pivot = next((i for i in range(len(target)) if i not in occupied and matrix[i][j]), None)
        if pivot is None:
            continue
        left, _ = target[pivot]
        for i in range(pivot+1, len(target)):
            if matrix[i][j]:
                matrix[i] = [a ^ b for a, b in zip(matrix[i], matrix[pivot], strict=True)]
        for k in range(j+1, len(source)):
            if matrix[pivot][k]:
                # The pivot column is now a unit vector. Carry the inverse basis change on the query.
                matrix[pivot][k] = False
                coords[j] ^= coords[k]
        occupied.add(pivot)
        pivots.append((left, right, j))
    intervals = [(s, r) for s, r, _ in pivots if s <= r]
    active = [(s, r) for s, r, j in pivots if s <= r and coords[j]]
    assert len(intervals) == dimension and bool(active) == (status == "nonzero")
    return [(s, r) for s, r, _ in pivots], active


def contains(outer, inner):
    return outer[0] <= inner[0] and inner[1] <= outer[1]


def infer(active, fills, nonfills):
    if any(contains(a, b) for a in fills for b in nonfills):
        raise ValueError("a supplied filling would transport to a supplied nonfilling")
    if not active:
        return "raw filler"
    if any(contains(a, b) for a in active for b in nonfills):
        return "published nonfilling"
    if all(any(contains(a, b) for a in fills) for b in active):
        return "published filler"
    return "open"


def audit():
    checked = 0
    bottom, upper = [2, 8, 0], [2, 4, 8]
    for masks in product(range(8), repeat=3):
        columns = [[(k//2 if v & (1 << i) else 0) for i, k in enumerate(upper)] for v in masks]
        pivots, _ = reduce_action(bottom, upper, columns, [0]*3)
        for j, r in enumerate((1, 3, inf)):
            for s in range(1, 4):
                rank = len(row_reduce(v & ((1 << s) - 1) for v in masks[:j+1]))
                assert rank == sum(left <= s and right <= r for left, right in pivots)
        for shell in product((0, 1), repeat=3):
            _, active = reduce_action(bottom, upper, columns, shell)
            # For each diagonal tester, enumerate the allowable homomorphisms in the original basis.
            for s in range(1, 4):
                available = [v for v in range(1 << s)
                             if all(not ((v & col).bit_count() % 2)
                                    for col, k in zip(masks, bottom) if k and valuation(k) < s)]
                x = 0
                for value, selected in zip(masks, shell):
                    if selected:
                        x ^= value
                assert any((x & v).bit_count() % 2 for v in available) == any(
                    contains(a, (s, s)) for a in active)
            checked += 1
    pairs = 0
    intervals = [(s, r) for r in range(1, 5) for s in range(1, r+1)]
    for a in intervals:
        for b in intervals:
            s, r = a
            t, u = b
            possible = any(2**r * f % 2**u == 0 and f % 2 and
                           2**s * g % 2**t == 0 and (2**(s-1)*g - 2**(t-1)*f) % 2**t == 0
                           for f in range(2**u) for g in range(2**t))
            assert possible == contains(a, b)
            pairs += 1
    ideals = 0
    for flags in product((0, 1), repeat=len(intervals)):
        yes = [a for a, flag in zip(intervals, flags) if flag]
        no = [a for a, flag in zip(intervals, flags) if not flag]
        if any(contains(a, b) for a in yes for b in no):
            continue
        assert all(infer([a], yes, no) == ("published filler" if a in yes else "published nonfilling")
                   for a in intervals)
        ideals += 1
    assert ideals == 42
    print(f"Verified {checked:,} named shells, {pairs} ordered pairs of cyclic types and {ideals} closed patterns.")


def interval(pair):
    s, r = pair
    if s < 1 or r < 0 or (r and r < s):
        raise ValueError("tests need 1 <= left <= right, with right=0 for an infinite endpoint")
    return s, r or inf


def display(pair):
    s, r = pair
    return f"[{s},{'inf' if r == inf else r}]"


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--bottom-orders", nargs="*", type=int)
    parser.add_argument("--orders", nargs="*", type=int)
    parser.add_argument("--column", action="append", nargs="*", type=int, default=[])
    parser.add_argument("--shell", nargs="*", type=int)
    parser.add_argument("--fills", action="append", nargs=2, type=int, default=[])
    parser.add_argument("--nonfills", action="append", nargs=2, type=int, default=[])
    args = parser.parse_args()
    if all(v is None for v in (args.orders, args.bottom_orders, args.shell)) and not (
            args.column or args.fills or args.nonfills):
        audit()
    elif any(v is None for v in (args.orders, args.bottom_orders, args.shell)):
        parser.error("supply bottom and upper orders, eta columns and a shell")
    else:
        try:
            pivots, active = reduce_action(args.bottom_orders, args.orders, args.column, args.shell)
            result = infer(active, list(map(interval, args.fills)), list(map(interval, args.nonfills)))
        except ValueError as exc:
            parser.error(str(exc))
        print("Surviving factors:", ", ".join(display(a) for a in pivots if a[0] <= a[1]) or "none")
        print("Factors of this shell:", ", ".join(map(display, active)) or "none")
        print("Comparison:", result)
