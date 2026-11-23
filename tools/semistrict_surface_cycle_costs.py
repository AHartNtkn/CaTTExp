"""Stable signed cycle costs and separated-cycle obstructions in the square quotient."""
import argparse
from functools import cache
from itertools import permutations

from semistrict_surface_square_quotient import evaluate, inverse, multiply, parse_rule


def cycle_type(p):
    seen = set()
    lengths = []
    for i in range(len(p)):
        if i not in seen:
            j, length = i, 0
            while j not in seen:
                seen.add(j)
                length += 1
                j = p[j]
            if length > 1:
                lengths.append(length)
    return tuple(sorted(lengths))


def canonical(cycles, width):
    p = list(range(width))
    i = 0
    for length in cycles:
        p[i:i+length] = list(range(i+1, i+length)) + [i]
        i += length
    return tuple(p)


@cache
def products(current, action, width_cap):
    n = sum(current) + sum(action)
    if width_cap is not None:
        n = min(n, width_cap)
    if n < max(sum(current), sum(action)):
        return set()
    p = canonical(current, n)
    d = canonical(action, sum(action))
    output = set()
    for labels in permutations(range(n), len(d)):
        step = list(range(n))
        for i, j in enumerate(d):
            step[labels[i]] = labels[j]
        output.add(cycle_type(multiply(step, p)))
    return output


def defects(rules):
    actions = set()
    for n, l, r in rules:
        d = cycle_type(multiply(evaluate(n, r), inverse(evaluate(n, l))))
        cost = len(r)-len(l)
        if cost < 0 or (cost == 0 and d):
            raise ValueError('requires increasing costs and permutation-preserving neutral rules')
        if cost:
            actions.add((cost, d))
    return actions


def signed_costs(actions, budget, width_cap=None):
    layers = [set() for _ in range(budget+1)]
    layers[0].add(())
    for c, layer in enumerate(layers):
        for cost, d in actions:
            if c+cost <= budget:
                for p in layer:
                    layers[c+cost].update(products(p, d, width_cap))
    return layers


def split_costs(cycles, layers, budget):
    if not cycles:
        return {c for c in range(budget+1) if () in layers[c]}
    totals = {0}
    for k in cycles:
        prices = [c for c in range(1, budget+1) if (k,) in layers[c]]
        totals = {a+b for a in totals for b in prices if a+b <= budget}
    return totals


def chart(rules, cost, cycles):
    """Compact description of two positive endpoints and the separating width."""
    w = max(n for n, _, _ in rules)
    length = sum(k-1 for k in cycles)
    initial = max(0, length-cost)
    assert (initial+cost-length)%2 == 0 and initial%2 == 0
    gap = cost*(w+2*(initial+cost))+1
    starts = []
    end = 0
    for k in cycles:
        starts.append(end)
        end += k+gap
    n = max(end-gap, w, cost*w)
    return {'width': n, 'source_central_squares': initial//2,
            'target_cycles_at_zero_based_positions': list(zip(starts, cycles)),
            'target_central_squares': (initial+cost-length)//2}


def separated_failure(rules, budget):
    layers = signed_costs(defects(rules), budget)
    for c, layer in enumerate(layers):
        for cycles in sorted(layer):
            if len(cycles) > 1 and c not in split_costs(cycles, layers, c):
                return c, cycles, chart(rules, c, cycles)
    return None


def cheapest_pair_failure(rules):
    """Two cheapest conjugates force two separated individual transpositions."""
    actions = defects(rules)
    cheapest = min((c for c, d in actions if d), default=None)
    if cheapest is not None and (cheapest, (2,)) not in actions:
        return 2*cheapest, (2, 2), chart(rules, 2*cheapest, (2, 2))
    return None


def checks():
    exact = 0
    for n in range(2, 6):
        group = list(permutations(range(n)))
        types = {cycle_type(p) for p in group}
        for d in types - {()}:
            actions = {(len(d)+1, d), (2, ())}
            layers = signed_costs(actions, 8, n)
            steps = [(cost, p) for cost, t in actions for p in group if cycle_type(p) == t]
            actual = [set() for _ in layers]
            actual[0].add(tuple(range(n)))
            for c, layer in enumerate(actual):
                assert {cycle_type(p) for p in layer} == layers[c]
                for cost, step in steps:
                    if c+cost < len(layers):
                        actual[c+cost].update(multiply(step, p) for p in layer)
                exact += 1
    for d in [(2,), (3,), (4,), (2, 2), (2, 3), (5,)]:
        assert (2, 2) in products(d, d, max(sum(d)+2, 4))
    three = [(3, (), (1, 2))]
    assert separated_failure(three, 4) == cheapest_pair_failure(three)
    assert separated_failure(three + [(2, (), (1,))], 4) is None
    two_pairs = [(4, (), (1, 3)), (2, (), (1,)*3)]
    assert separated_failure(two_pairs, 2)[:2] == (2, (2, 2))
    # An odd rule is available, but spending two per *pair* is too cheap.
    assert separated_failure(two_pairs + [(2, (), (1,))], 3) is None
    print(f'{exact} fixed-width cost layers against literal permutations; '
          'six double-transposition products and separated-budget checks passed')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rule', action='append', type=parse_rule, default=[])
    parser.add_argument('--budget', type=int)
    args = parser.parse_args()
    if args.rule:
        result = (cheapest_pair_failure(args.rule) if args.budget is None
                  else separated_failure(args.rule, args.budget))
        print('separated obstruction', result)
    else:
        checks()
