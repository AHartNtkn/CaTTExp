"""Compare old movies on two unrolled globular columns, in degrees four and five.

For degree five the prism keys (side,i,k,j,h) denote update k of slot i on
the moving side crossing phase h of slot j on the other side (zero based).
The filling keys (i,k,j,h) give the left and right updates respectively.
"""
import argparse
from collections import Counter, defaultdict
from itertools import combinations, product
import json


def slide_kind(first, second):
    """The permitted direction of transposition. Tokens name their strands."""
    if first[0] == second[0] == 'C':
        return 'exchange' if first[1] != second[1] and first[2] != second[2] else None
    if 'C' not in (first[0], second[0]):
        return 'exchange' if first[:2] != second[:2] else None
    crossing, label = (first, second) if first[0] == 'C' else (second, first)
    slot = crossing[1 if label[0] == 'L' else 2]
    if slot != label[1]:
        return 'exchange'
    if (first[0] == 'C') == (label[0] == 'L'):
        return 'prism'
    return None


def slides_to(source, target):
    """Construct a sequence of strict exchanges and positive prisms on legal schedules."""
    if Counter(source) != Counter(target):
        return None
    current = list(source)
    slides = []
    for i, token in enumerate(target):
        j = current.index(token, i)
        while j > i:
            move = slide_kind(current[j-1], token)
            if move is None:
                return None
            slides.append((j-1, move))
            current[j-1], current[j] = current[j], current[j-1]
            j -= 1
    return slides


def schedules(start, goal, lengths):
    """Enumerate legal movies directly on temporal lists with advancing unary phases."""
    end_rank = {slot: i for i, slot in enumerate(goal)}

    def visit(order, used, path):
        if order == goal and used == lengths:
            yield tuple(path)
        for k, ((side, slot), count, limit) in enumerate(zip(start, used, lengths)):
            if count < limit:
                nxt = used[:k] + (count+1,) + used[k+1:]
                yield from visit(order, nxt, path+[(side, slot, count)])
        for k, (r, l) in enumerate(zip(order, order[1:])):
            if r[0] == 'R' and l[0] == 'L' and end_rank[r] > end_rank[l]:
                nxt = order[:k] + (l, r) + order[k+2:]
                yield from visit(nxt, used, path+[('C', l[1], r[1])])
    yield from visit(start, (0,)*len(start), [])


def measurements(start, path):
    """Evaluate the per-update prefix-mass coefficients on literal temporal lists."""
    order = list(start)
    bits = set()
    for token in path:
        side, i, j = token
        if side == 'C':
            k = order.index(('R', j))
            assert order[k+1] == ('L', i)
            order[k:k+2] = order[k:k+2][::-1]
        else:
            bits.update((token, slot) for slot in order[:order.index((side, i))])
    return frozenset(bits)


def atoms(left, right):
    for i, j in product(range(len(left)), range(len(right))):
        for k, h in product(range(left[i]), range(right[j])):
            yield i, k, j, h


def boundary(chain):
    result = Counter()
    for (i, k, j, h), coeff in chain.items():
        for key, phase in [(('L', i, k, j), h), (('R', j, h, i), k)]:
            result[key+(phase,)] -= coeff
            result[key+(phase+1,)] += coeff
    return {key: value for key, value in result.items() if value}


def filling(left, right, difference):
    """Recover the unique signed top chain, or reject a nonboundary."""
    # A selected pair of updates reads each other's increment in later phases.
    z = {}
    for i, k, j, h in atoms(left, right):
        doubled = sum(difference.get(('L', i, k, j, phase), 0)
                      for phase in range(h+1, right[j]+1))
        doubled += sum(difference.get(('R', j, h, i, phase), 0)
                       for phase in range(k+1, left[i]+1))
        if doubled % 2:
            return None
        if doubled:
            z[i, k, j, h] = doubled//2
    if boundary(z) == {key: value for key, value in difference.items() if value}:
        return z
    return None


def orders(m, n):
    for positions in combinations(range(m+n), m):
        left = set(positions)
        i = j = 0
        result = []
        for k in range(m+n):
            if k in left:
                result.append(('L', i))
                i += 1
            else:
                result.append(('R', j))
                j += 1
        yield tuple(result)


def check_movies():
    cases = movies = pairs = 0
    for m, n, updates in [(1, 2, (2, 1, 0)), (2, 2, (1, 0, 0, 1)), (3, 1, (0, 1, 0, 2))]:
        for start, goal in product(orders(m, n), repeat=2):
            lengths = tuple(updates[i if side == 'L' else m+i] for side, i in start)
            words = list(schedules(start, goal, lengths))
            if not words:
                continue
            scores = {w: measurements(start, w) for w in words}
            adjacency = defaultdict(set)
            for w in words:
                for k in range(len(w)-1):
                    v = w[:k] + (w[k+1], w[k]) + w[k+2:]
                    if v in scores and slide_kind(w[k], w[k+1]) is not None:
                        adjacency[w].add(v)
            for w in words:
                reached, todo = {w}, [w]
                while todo:
                    for v in adjacency[todo.pop()] - reached:
                        reached.add(v)
                        todo.append(v)
                for v in words:
                    cert = slides_to(w, v)
                    assert (v in reached) == (scores[w] <= scores[v]) == (cert is not None)
                    if cert is not None:
                        a = w
                        for k, _ in cert:
                            b = a[:k] + (a[k+1], a[k]) + a[k+2:]
                            assert b in adjacency[a]
                            a = b
                        assert a == v
                pairs += len(words)
            cases += 1
            movies += len(words)
    return cases, movies, pairs


def check_chains():
    tests = 0
    for left, right in product([(), (0,), (1,), (2,), (0, 2), (1, 0, 2)], repeat=2):
        basis = list(atoms(left, right))
        chains = [{key: 1} for key in basis]
        for seed in range(9):
            chains.append({key: value for t, key in enumerate(basis)
                           if (value := ((t+1)*(seed+1)+seed)%7-3)})
        for chain in chains:
            diff = boundary(chain)
            assert filling(left, right, diff) == chain
            if basis:
                i, k, j, h = basis[0]
                perturbed = dict(diff)
                key = ('L', i, k, j, h+1)
                perturbed[key] = perturbed.get(key, 0)+1
                assert filling(left, right, perturbed) is None
            tests += 1
    return tests


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--chains', help='JSON with left/right slot update counts and '
                        'difference rows [side, slot, update, other_slot, phase, coefficient]')
    args = parser.parse_args()
    if args.chains:
        with open(args.chains) as handle:
            data = json.load(handle)
        diff = Counter()
        for *key, value in data['difference']:
            diff[tuple(key)] += value
        z = filling(data['left'], data['right'], diff)
        print(json.dumps({'boundary': z is not None,
                          'inhabited': z is not None and all(c >= 0 for c in z.values()),
                          'signed_chain': None if z is None else [[*k,v] for k,v in z.items()]}))
    else:
        contexts, movies, pairs = check_movies()
        print(f'{contexts} endpoint charts, {movies} legal movies, {pairs} comparisons, '
              f'{check_chains()} tensor boundary recoveries')
