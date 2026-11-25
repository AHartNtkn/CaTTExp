"""Exact placement counts over a finite-exponent free-group module.

JSON fields: deck_rank, modulus, rank, steps, face, relations. A column is
a list of [word, coordinate, coefficient], words are lists of signed 1-based
deck letters, and module coordinates are 0-based. An optional counts array
requests actual sheets. Optional sheets checks specified [step, word] pairs.
Each returned minimum generates its translate of
modulus * N^number_of_steps. Enumeration is intended for small presentations.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import product
import json
from pathlib import Path


def reduced(word, rank):
    out = []
    for a in word:
        if type(a) is not int or not 1 <= abs(a) <= rank:
            raise ValueError("invalid signed deck letter")
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def add(x, y, modulus):
    return tuple((a + b) % modulus for a, b in zip(x, y, strict=True))


def span(rows, zero, modulus):
    group = {zero}
    for row in rows:
        old = list(group)
        for x in old:
            for _ in range(modulus - 1):
                x = add(x, row, modulus)
                group.add(x)
    return group


def local_names(deck_rank, modulus, rank, inputs):
    if min(deck_rank, rank) < 1 or modulus < 2:
        raise ValueError("positive ranks and modulus >= 2 required")
    names = {((), i) for i in range(rank)}
    columns = []
    for column in inputs:
        terms = []
        for word, i, c in column:
            if not 0 <= i < rank:
                raise ValueError("invalid module coordinate")
            w = reduced(word, deck_rank)
            if c % modulus:
                names.update((w[j:], i) for j in range(len(w) + 1))
                terms.append(((w, i), c))
        columns.append(terms)
    index = {name: j for j, name in enumerate(sorted(names))}
    return index, columns


def compile_tree(deck_rank, modulus, rank, steps, face, relations):
    index, columns = local_names(deck_rank, modulus, rank, [*steps, face, *relations])
    zero = (0,) * len(index)

    def vector(terms):
        v = list(zero)
        for name, c in terms:
            j = index[name]
            v[j] = (v[j] + c) % modulus
        return tuple(v)

    vectors = [vector(col) for col in columns]
    local = span(vectors[len(steps) + 1:], zero, modulus)
    coset = {}
    for v in product(range(modulus), repeat=len(zero)):
        if v not in coset:
            coset.update((add(v, h, modulus), v) for h in local)

    def plus(x, y):
        return coset[add(x, y, modulus)]

    edges = defaultdict(list)
    for w, i in index:
        if w:
            a = w[0]
            x = vector([((w, i), 1)])
            y = vector([((w[1:], i), 1)])
            edges[abs(a)].append(x + y if a > 0 else y + x)
    moves = {}
    for a in range(1, deck_rank + 1):
        moves[a], moves[-a] = defaultdict(set), defaultdict(set)
        for pair in span(edges[a], zero + zero, modulus):
            x, y = coset[pair[:len(zero)]], coset[pair[len(zero):]]
            moves[a][y].add(x)
            moves[-a][x].add(y)
    return zero, plus, moves, [coset[v] for v in vectors[:len(steps)]], coset[vectors[len(steps)]]


def put(table, value, counts, sheets, modulus):
    # Comparable counts must also have the same residue vector.
    def covers(x, y):
        return all(b >= a and (b - a) % modulus == 0 for a, b in zip(x, y, strict=True))

    bucket = table.setdefault(value, {})
    if any(covers(c, counts) for c in bucket):
        return False
    for c in list(bucket):
        if covers(counts, c):
            del bucket[c]
    bucket[counts] = sheets
    return True


def tree_facts(zero, plus, moves, increments, modulus):
    local = {}
    for counts in product(range(modulus), repeat=len(increments)):
        v = zero
        for n, step in zip(counts, increments):
            for _ in range(n):
                v = plus(v, step)
        sheets = tuple((i, ()) for i, n in enumerate(counts) for _ in range(n))
        put(local, v, counts, sheets, modulus)
    states = {incoming: {} for incoming in (0, *moves)}
    while True:
        changed = False
        for incoming, table in states.items():
            partial = local
            for a in moves:
                if a == -incoming:
                    continue
                joined = {v: dict(bucket) for v, bucket in partial.items()}
                for y, child in states[a].items():
                    for x in moves[a].get(y, ()):
                        for v, parent in partial.items():
                            total = plus(v, x)
                            for c, prefix in parent.items():
                                for d, suffix in child.items():
                                    counts = tuple(i + j for i, j in zip(c, d))
                                    sheets = prefix + tuple((i, (a,) + w) for i, w in suffix)
                                    put(joined, total, counts, sheets, modulus)
                partial = joined
            for v, bucket in partial.items():
                for c, sheets in bucket.items():
                    changed |= put(table, v, c, sheets, modulus)
        if not changed:
            return states


def solve(deck_rank, modulus, rank, steps, face, relations):
    zero, plus, moves, increments, target = compile_tree(deck_rank, modulus, rank, steps, face, relations)
    return tree_facts(zero, plus, moves, increments, modulus)[0].get(target, {})


def sheet_checker(deck_rank, modulus, rank, steps, face, relations):
    zero, plus, moves, increments, target = compile_tree(deck_rank, modulus, rank, steps, face, relations)
    empty = tree_facts(zero, plus, moves, [], modulus)

    def accepts(sheets):
        labels = {(): zero}
        children = defaultdict(set)
        for i, word in sheets:
            if type(i) is not int or not 0 <= i < len(increments):
                raise ValueError("invalid step index")
            w = reduced(word, deck_rank)
            labels[w] = plus(labels.get(w, zero), increments[i])
            for j, a in enumerate(w):
                children[w[:j]].add(a)
                labels.setdefault(w[:j], zero)
        values = {}
        for w in sorted(labels, key=len, reverse=True):
            partial = {labels[w]}
            for a in moves:
                if w and a == -w[-1]:
                    continue
                child = values[w + (a,)] if a in children[w] else empty[a]
                transfers = {x for y in child for x in moves[a].get(y, ())}
                partial = {plus(v, x) for v in partial for x in transfers}
            values[w] = partial
        return target in values[()]

    return accepts


def witness(minima, counts, modulus):
    if any(type(c) is not int or c < 0 for c in counts):
        raise ValueError("invalid occurrence count")
    for c, sheets in minima.items():
        extra = [b - a for a, b in zip(c, counts, strict=True)]
        if all(x >= 0 and x % modulus == 0 for x in extra):
            return sorted((*sheets, *((i, ()) for i, n in enumerate(extra) for _ in range(n))))
    return None


def audit():
    def col(*terms):
        return list(terms)

    x, y = col(([], 0, 1)), col(([], 1, 1))
    # a fixes first axis, b fixes second. Each summand is the permutation
    # module on cosets of the corresponding cyclic subgroup.
    axis = [col(([1], 0, 1), ([], 0, -1)), col(([2], 1, 1), ([], 1, -1))]
    cases = 0
    for i, j in product(range(2), repeat=2):
        target = col(([2, 1], 0, i), ([-1], 1, j))
        minima = solve(2, 2, 2, [x, y], target, axis)
        assert set(minima) == {(i, j)}
        for counts in product(range(4), repeat=2):
            sheets = witness(minima, counts, 2)
            assert (sheets is not None) == (counts[0] % 2 == i and counts[1] % 2 == j)
            if sheets is not None:
                parity = set()
                def toggle(k, w):
                    w = list(w)
                    while w and abs(w[-1]) == k + 1:
                        w.pop()
                    key = k, tuple(w)
                    parity.symmetric_difference_update({key})
                for k, w in sheets:
                    toggle(k, w)
                for w, k, c in target:
                    if c:
                        toggle(k, w)
                assert not parity
            cases += 1

    # Independent cyclic Laurent solver, including an off-axis relation
    # witness and a target with several terms. Mixed-sign words are allowed.
    from semistrict_surface_finite_placements import cyclic
    cyclic_cases = 0
    def lift(c):
        return [([1 if n > 0 else -1] * abs(n), k, a) for n, k, a in c]
    for modulus in (2, 3, 4):
        for rel in ([], [[(0, 0, 1), (1, 0, 1)]]):
            for delta in range(-1, 2):
                step = [(0, 0, 1)]
                face = [(delta, 0, 1), (0, 0, 1)]
                minima = solve(1, modulus, 1, [lift(step)], lift(face), list(map(lift, rel)))
                for n in range(4):
                    sheets = witness(minima, (n,), modulus)
                    expected = cyclic(modulus, 1, [step] * n, face, rel)
                    assert (sheets is not None) == (expected is not None)
                    cyclic_cases += 1
    # Placement minima with the SAME residues can be incomparable: over F2
    # take a free permutation module, two copies of the same step, a target
    # supported on two distinct vertices. Two tokens of either type suffice.
    minima = solve(2, 2, 1, [x, x], x + col(([1], 0, 1)), [])
    assert set(minima) == {(2, 0), (1, 1), (0, 2)}
    # The relation b*x=0 kills x via an unmarked child, including at root.
    assert set(solve(2, 2, 1, [], x, [col(([2], 0, 1))])) == {()}
    assert not solve(2, 2, 1, [], x, [])
    # Transport is a genuinely partial action: only the first axis moves
    # along a. Two labelled sheets must lie on their respective axes.
    check = sheet_checker(2, 2, 2, [x, y], x + y, axis)
    words = [w for n in range(3) for w in product((1, -1, 2, -2), repeat=n)
             if reduced(w, 2) == w]
    for w, v in product(words, repeat=2):
        assert check([(0, w), (1, v)]) == (all(abs(a) == 1 for a in w)
                                           and all(abs(a) == 2 for a in v))
    print(f"{cases} independent coset count checks, {cyclic_cases} cyclic differential checks,"
          f" {len(words)**2} fixed sheet pairs, incomparable minima and zero-token branches passed")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path)
    args = parser.parse_args()
    if args.input:
        spec = json.loads(args.input.read_text())
        counts = spec.pop("counts", None)
        sheets = spec.pop("sheets", None)
        if counts is not None and len(counts) != len(spec["steps"]):
            parser.error("supply one count per step")
        minima = solve(**spec)
        result = {"modulus": spec["modulus"], "minima": sorted(minima)}
        if counts is not None:
            result["sheets"] = witness(minima, counts, spec["modulus"])
        if sheets is not None:
            result["accepts_sheets"] = sheet_checker(**spec)(sheets)
        print(json.dumps(result))
    else:
        audit()
