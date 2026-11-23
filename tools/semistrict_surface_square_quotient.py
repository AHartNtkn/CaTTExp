"""Raw and surface reachability after equating adjacent crossing squares.

Letters in the API are one-based adjacent transpositions. Command-line words
are comma-separated lists, with the empty string for the empty braid.
"""
import argparse
from collections import defaultdict, deque
from functools import cache
from itertools import permutations, product
from math import gcd, lcm

from semistrict_surface_triple_attachments import one_counter


def multiply(p, q):
    return tuple(p[i] for i in q)


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def inversions(p):
    return sum(a > b for i, a in enumerate(p) for b in p[i+1:])


def order(p):
    remaining = set(range(len(p)))
    value = 1
    while remaining:
        i = next(iter(remaining))
        cycle = 0
        while i in remaining:
            remaining.remove(i)
            i = p[i]
            cycle += 1
        value = lcm(value, cycle)
    return value


def evaluate(width, word):
    p = list(range(width))
    for i in word:
        if not 1 <= i < width:
            raise ValueError(f'letter {i} outside width {width}')
        p[i-1], p[i] = p[i], p[i-1]
    return tuple(p)


def spelling(p, height):
    letters = []
    q = list(p)
    for k in reversed(range(len(q))):
        i = q.index(k)
        while i < k:
            q[i], q[i+1] = q[i+1], q[i]
            i += 1
            letters.append(i)
    return (1, 1) * height + tuple(reversed(letters))


def parse_word(word):
    return tuple(map(int, word.split(','))) if word else ()


def parse_rule(spec):
    width, left, right = spec.split(':')
    n, l, r = int(width), parse_word(left), parse_word(right)
    if n < 2:
        raise ValueError('rules with moving crossings require width at least two')
    evaluate(n, l)
    evaluate(n, r)
    return n, l, r


class SquareQuotient:
    def __init__(self, width, rules):
        if width < 2:
            raise ValueError('widths zero and one have only the empty word')
        self.width = width
        self.states = tuple(permutations(range(width)))
        self.length = {p: inversions(p) for p in self.states}
        thresholds = {}
        self.moves = set()
        for m, l, r in rules:
            for shift in range(width-m+1):
                p, q = (evaluate(width, (i+shift for i in word)) for word in (l, r))
                delta = len(r)-len(l)
                for u in self.states:
                    up = multiply(u, p)
                    defect = multiply(multiply(u, q), inverse(up))
                    self.moves.add((defect, delta))
                    for v in self.states:
                        i = multiply(up, v)
                        j = multiply(defect, i)
                        minimum = self.length[u]+len(l)+self.length[v]
                        a = (minimum-self.length[i])//2
                        b = (minimum+delta-self.length[j])//2
                        key = (i, j, b-a)
                        thresholds[key] = min(a, thresholds.get(key, a))
        self.edges = defaultdict(list)
        self.transitions = []
        for (i, j, e), a in thresholds.items():
            self.edges[i].append((j, a, a+e))
            self.transitions.append(((i, a), (j, a+e), False))
        costs = [d for _, d in self.moves]
        self.mixed = any(d < 0 for d in costs) and any(d > 0 for d in costs)
        self.period = gcd(*(order(p)*abs(d) for p, d in self.moves)) if self.mixed else 0

    def state(self, word):
        p = evaluate(self.width, word)
        return p, (len(word)-self.length[p])//2

    @cache
    def reachable(self, start, goal, signed):
        if start == goal:
            return True
        i, a = start
        j, b = goal
        if not signed and any(p == j and a >= need and a-need+give == b
                              for p, need, give in self.edges[i]):
            return True
        if self.mixed and not signed:
            return one_counter(start, goal, self.transitions)
        k, end = self.length[i]+2*a, self.length[j]+2*b
        low, high = sorted((k, end))
        if self.period:
            k, end = k % self.period, end % self.period
        seen = {(i, k)}
        todo = deque(seen)
        while todo:
            p, t = todo.popleft()
            if signed:
                steps = ((multiply(d, p), t+cost) for d, cost in self.moves)
            else:
                h = (t-self.length[p])//2
                steps = ((q, self.length[q]+2*(h-need+give))
                         for q, need, give in self.edges[p] if h >= need)
            for q, value in steps:
                if self.period:
                    value %= self.period
                elif not low <= value <= high:
                    continue
                if (q, value) == (j, end):
                    return True
                if (q, value) not in seen:
                    seen.add((q, value))
                    todo.append((q, value))
        return False

    def reflection_failure(self):
        radius = 0
        for (p, a), (q, b), _ in self.transitions:
            e = b-a
            radius = max(radius, abs(e))
            pair = ((p, max(0, -e)), (q, max(0, e)))
            if not self.reachable(*pair, False):
                return pair
        small = list(product(self.states, range(radius)))
        for pair in product(small, repeat=2):
            if self.reachable(*pair, True) and not self.reachable(*pair, False):
                return pair
        return None


def neutral_cutoff(rules):
    """First width with all letters identified, or a one-letter obstruction."""
    defects = []
    for n, l, r in rules:
        if len(l) == len(r):
            d = multiply(evaluate(n, r), inverse(evaluate(n, l)))
            if d != tuple(range(n)):
                defects.append((n, d))
    if not defects:
        return None, None
    n = min(m for m, _ in defects)
    exceptional = n == 4 and all(order(d) == 2 for m, d in defects if m == 4)
    for width in range(n, n+1+exceptional):
        graph = {i: set() for i in range(1, width)}
        for m, l, r in rules:
            if len(l) == len(r) == 1:
                for offset in range(width-m+1):
                    graph[l[0]+offset].add(r[0]+offset)
        for i in graph:
            seen, todo = {i}, [i]
            while todo:
                for j in graph[todo.pop()] - seen:
                    todo.append(j)
                    seen.add(j)
            required = ({1, 3} if i != 2 else {2}) if exceptional and width == 4 else graph.keys()
            for j in sorted(required - seen):
                pair = tuple((evaluate(width, (letter,)), 0) for letter in (i, j))
                return None, (width, pair)
    return n + int(exceptional), None


def unary_failure(cutoff, rules):
    """After the single letters agree, only the rule lengths remain."""
    for width, l, r in rules:
        change = len(r)-len(l)
        if not change:
            continue
        n = max(cutoff, width)
        # Orient the entire weakly monotone system towards larger counts.
        moves = [(min(len(a), len(b)), abs(len(a)-len(b)))
                 for m, a, b in rules if m <= n and len(a) != len(b)]
        target = abs(change)
        seen = {0}
        for count in range(target):
            if count in seen:
                seen.update(count+cost for guard, cost in moves if guard <= count)
        if target not in seen:
            words = ((), (1,)*target) if change > 0 else ((1,)*target, ())
            pair = tuple((evaluate(n, w), len(w)//2) for w in words)
            return n, pair
    return None


def all_width_failure(rules):
    increasing = sorted(rule for rule in rules if len(rule[2]) > len(rule[1]))
    decreasing = sorted(rule for rule in rules if len(rule[2]) < len(rule[1]))
    if increasing and decreasing:
        threshold = max(increasing[0][0], decreasing[0][0])
        for n in range(2, threshold):
            failure = SquareQuotient(n, rules).reflection_failure()
            if failure:
                return n, failure
        costs = []
        for n, l, r in (increasing[0], decreasing[0]):
            defect = multiply(evaluate(n, r), inverse(evaluate(n, l)))
            costs.append(order(defect)*abs(len(r)-len(l)))
        h = lcm(*costs)//2
        identity = tuple(range(threshold))
        solver = SquareQuotient(threshold, rules)
        for a, b in ((0, h), (h, 0)):
            pair = ((identity, a), (identity, b))
            if not solver.reachable(*pair, False):
                return threshold, pair
        return None
    cutoff, failure = neutral_cutoff(rules)
    if failure:
        return failure
    if cutoff is not None:
        if increasing or decreasing:
            for n in range(2, cutoff):
                failure = SquareQuotient(n, rules).reflection_failure()
                if failure:
                    return n, failure
        return unary_failure(cutoff, rules)
    if any(evaluate(n, l) != evaluate(n, r) for n, l, r in rules):
        raise ValueError('all-width criterion requires permutation preservation, a nontrivial '
                         'count-neutral defect, or costs of both signs')
    solvers = {}
    for n, l, r in sorted(rules):
        e = (len(r)-len(l))//2
        if not e:
            continue
        if n not in solvers:
            solvers[n] = SquareQuotient(n, rules)
        identity = tuple(range(n))
        pair = ((identity, max(0, -e)), (identity, max(0, e)))
        if not solvers[n].reachable(*pair, False):
            return n, pair
    return None


def base_neighbors(w, width):
    for i in range(len(w)-1):
        a, b = w[i:i+2]
        if a == b:
            for j in (a-1, a+1):
                if 1 <= j < width:
                    yield w[:i]+(j, j)+w[i+2:]
        if abs(a-b) > 1:
            yield w[:i]+(b, a)+w[i+2:]
        if i+2 < len(w) and w[i+2] == a and abs(a-b) == 1:
            yield w[:i]+(b, a, b)+w[i+3:]


def checks():
    counted, comparisons = 0, 0
    for n in (2, 3, 4):
        rules = [(2, (1, 1), ()), (3, (1,), (2, 1)), (3, (), (1, 2))]
        solver = SquareQuotient(n, rules)
        for k in range(6):
            remaining = set(product(range(1, n), repeat=k))
            seen_states = set()
            while remaining:
                w = remaining.pop()
                src = solver.state(w)
                assert src not in seen_states and solver.state(spelling(*src)) == src
                seen_states.add(src)
                component, todo = {w}, [w]
                while todo:
                    for v in base_neighbors(todo.pop(), n):
                        if v not in component:
                            remaining.remove(v)
                            component.add(v)
                            todo.append(v)
                counted += len(component)
                actual = set()
                for v in component:
                    assert solver.state(v) == src
                    for m, l, r in rules:
                        for shift in range(n-m+1):
                            left, right = (tuple(i+shift for i in s) for s in (l, r))
                            for pos in range(len(v)-len(l)+1):
                                if v[pos:pos+len(l)] == left:
                                    actual.add(solver.state(v[:pos]+right+v[pos+len(l):]))
                p, h = src
                assert actual == {(q, h-a+b) for q, a, b in solver.edges[p] if h >= a}
                comparisons += 1
    guarded = [(3, (1,)*3, (2,)*3)]
    q = SquareQuotient(3, guarded)
    pair = q.state((1,)), q.state((2,))
    assert q.reachable(*pair, True) and not q.reachable(*pair, False)
    assert q.reflection_failure() and SquareQuotient(3, []).reflection_failure() is None
    empty, square = (), (1, 1)
    assert all_width_failure([(3, (1,), (1,)*3)]) == (3, (q.state(empty), q.state(square)))
    mixed = [(2, empty, square*2), (2, square*3, empty)]
    assert all_width_failure(mixed) is None and SquareQuotient(3, mixed).reflection_failure() is None
    model = SquareQuotient(3, mixed)
    cycling = [(3, empty, (1, 2)), (3, (1, 2), empty), (5, (2,), (3, 4))]
    assert all_width_failure(cycling) is None
    guarded_cycle = [(3, (1,), (1, 1, 2)), (3, (1, 1, 2), (1,))]
    assert all_width_failure(guarded_cycle) is not None
    for words in product([empty, square, (1,), (2,), (1, 2), (2, 1, 2)], repeat=2):
        pair = tuple(q.state(w) for w in words)
        for signed in (True, False):
            assert model.reachable(*pair, signed) == (pair[0][0] == pair[1][0])
    distant = [(4, (1,), (3,)), (4, (3,), (1,))]
    joined = distant + [(5, (1,), (2,)), (5, (2,), (1,))]
    assert all_width_failure(distant)[0] == 5 and all_width_failure(joined) is None
    assert all_width_failure(joined + [(6, (1,), (1, 1))])[0] == 6
    assert all_width_failure(joined + [(6, (), (1, 1))]) is None
    assert all_width_failure(joined + [(6, (1, 1), ())]) is None
    catalogue = [(3, (1,), (2,)), (3, (2,), (1,)), *distant,
                 (4, (1, 2), (2, 1)), (4, (1, 1, 1), (3, 3, 3))]
    homogeneous = 0
    for flags in product((False, True), repeat=len(catalogue)):
        rules = [r for r, use in zip(catalogue, flags) if use]
        first = all_width_failure(rules)
        for n in (3, 4):
            result = SquareQuotient(n, rules).reflection_failure()
            if result is not None:
                assert first is not None and first[0] == n
                break
            assert first is None or first[0] > n
        homogeneous += 1
    print(f'{counted} positive spellings, {comparisons} exact successor sets, '
          f'{homogeneous} homogeneous dictionaries, guarded and mixed-sign checks passed')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--width', type=int)
    ap.add_argument('--rule', action='append', type=parse_rule, default=[])
    ap.add_argument('--faces', nargs=2, type=parse_word)
    ap.add_argument('--all-widths', action='store_true')
    args = ap.parse_args()
    if args.all_widths:
        print('all-width failure (width and permutation-height endpoints)', all_width_failure(args.rule))
    elif args.width:
        solver = SquareQuotient(args.width, args.rule)
        if args.faces:
            pair = tuple(solver.state(w) for w in args.faces)
            print('raw', solver.reachable(*pair, False), 'surface', solver.reachable(*pair, True))
        else:
            failure = solver.reflection_failure()
            print('failure (positive words)', tuple(spelling(*s) for s in failure) if failure else None)
    else:
        checks()
