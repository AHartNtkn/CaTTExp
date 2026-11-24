"""Test the two-strand criterion for directed scalar braid attachments."""
import argparse
from functools import reduce
from itertools import combinations_with_replacement, product
from math import gcd
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import accepted, run


def pair_tests(colours, rules):
    """rules list (strand colours, signed crossing-count change) at parallel braids."""
    increments = {pair: [] for pair in combinations_with_replacement(sorted(set(colours)), 2)}
    for strands, crossings in rules:
        if len(strands) == 2:
            pair = tuple(sorted(strands))
            unit = 1 if pair[0] == pair[1] else 2
            if crossings % unit:
                raise ValueError('odd difference between parallel braids on distinct colours')
            increments[pair].append(crossings // unit)
    return {pair: bool(values and min(values) < 0 < max(values)
                       and reduce(gcd, values, 0) == 1)
            for pair, values in increments.items()}


def contains(values, target):
    if not target:
        return True
    steps = sorted(set(values) - {0})
    if not steps:
        return False
    if steps[0] < 0 < steps[-1]:
        return target % reduce(gcd, steps) == 0
    if steps[-1] < 0:
        target, steps = -target, [-step for step in steps]
    if target < 0:
        return False
    reachable = {0}
    for value in range(target):
        if value in reachable:
            reachable.update(value + step for step in steps if value + step <= target)
    return target in reachable


def window_paths(values):
    # A directed integer walk toward a target in [-12,12] needs at most
    # max |step| overshoot: reorder any realizing multiset toward the target.
    seen = {0}
    pending = [0]
    while pending:
        source = pending.pop()
        for d in values:
            end = source + d
            if -15 <= end <= 15 and end not in seen:
                seen.add(end)
                pending.append(end)
    return seen


def check_orders():
    tested = 0
    for mixed_colours in (False, True):
        pair = ('a', 'b' if mixed_colours else 'a')
        for mask in product((0, 1), repeat=7):
            values = [d for d, take in zip(range(-3, 4), mask) if take]
            rules = [(pair, d*(2 if mixed_colours else 1)) for d in values]
            # These rules always leave the two-strand component unchanged.
            rules += [((*pair, 'a'), 1), ((*pair, 'a'), -1)]
            seen = window_paths(values)
            assert pair_tests(pair, rules)[pair] == ({-1, 1} <= seen)
            for target in range(-12, 13):
                assert contains(values, target) == (target in seen)
            tested += 1
    colours = ('a', 'b')
    rules = [(pair, sign * (1 if pair[0] == pair[1] else 2))
             for pair in combinations_with_replacement(colours, 2) for sign in (-1, 1)]
    for index in range(len(rules)):
        tests = pair_tests(colours, rules[:index] + rules[index+1:])
        assert {pair for pair in tests if not tests[pair]} == {rules[index][0]}
    print(f'Checked {25*tested} signed queries in {tested} pair systems and all six omissions.')


def check_rice(checkout):
    text = """import examples/eh
def kill (x : *) (a : id(x) -> id(x)) (k : eh(x,a,a) -> id(comp[a,a]))
  : eh(x,a,a) -> id(comp[a,a]) = k
def create (x : *) (a : id(x) -> id(x)) (r : id(comp[a,a]) -> eh(x,a,a))
  : id(comp[a,a]) -> eh(x,a,a) = r
def on_three (x : *) (a : id(x) -> id(x)) (k : eh(x,a,a) -> id(comp[a,a]))
  : comp[[eh(x,a,a)],a] -> comp[[id(comp[a,a])],a] = comp[[[k]],a]
def different_colours (x : *) (a : id(x) -> id(x)) (b : id(x) -> id(x))
  : comp[a,b] -> comp[a,b] = comp[eh(x,a,b),eh(x,b,a)]
"""
    with TemporaryDirectory() as folder:
        directory = Path(folder)
        (directory / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        (directory / 'Repairs.catt').write_text(text)
        accepted(run(checkout / 'target/release/catt_strict', directory, 'Repairs.catt'),
                 'Repairs.catt', ('kill', 'create', 'on_three', 'different_colours'))
    print('Rice checked both declared repairs, a three-strand placement and a distinct-colour twist.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rice-checkout', type=Path)
    parser.add_argument('--steps', nargs='*', type=int, help='two-strand increments')
    parser.add_argument('--target', type=int, help='signed target difference')
    args = parser.parse_args()
    if (args.steps is None) != (args.target is None):
        parser.error('--steps and --target must be supplied together')
    if args.steps is None:
        check_orders()
    else:
        print('inhabited' if contains(args.steps, args.target) else 'uninhabited')
    if args.rice_checkout:
        check_rice(args.rice_checkout.resolve())
