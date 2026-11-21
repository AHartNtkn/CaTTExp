"""Certify all iterated frame consequences of finitely many based relations."""
from argparse import ArgumentParser
from pathlib import Path

from catt import arr, comp2, disc_tree, infer, maximal_vars, src, sub_from, subst_tm, tdim_tm, tgt, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, string_tree
from relative_coherence_state_paths import promote, promote_relation


def add(target, vector, scale):
    for key, value in vector.items():
        total = target.get(key, 0) + scale * value
        if total:
            target[key] = total
        else:
            target.pop(key, None)


def echelon(columns):
    """Unimodular elimination, retaining combinations for each pivot and kernel column."""
    pivots = {}
    kernel = []
    for index, column in enumerate(columns):
        vector, combination = dict(column), {index: 1}
        while vector:
            row = min(vector)
            if row not in pivots:
                if vector[row] < 0:
                    vector = {k: -a for k, a in vector.items()}
                    combination = {k: -a for k, a in combination.items()}
                pivots[row] = vector, combination
                break
            other, witness = pivots[row]
            quotient = vector[row] // other[row]
            add(vector, other, -quotient)
            add(combination, witness, -quotient)
            if row in vector:
                pivots[row] = vector, combination
                vector, combination = other, witness
        else:
            kernel.append(combination)
    return pivots, kernel


def coordinates(pivots, target):
    rest, result = dict(target), {}
    while rest:
        row = min(rest)
        if row not in pivots:
            return None
        vector, combination = pivots[row]
        quotient, remainder = divmod(rest[row], vector[row])
        if remainder:
            return None
        add(rest, vector, -quotient)
        add(result, combination, quotient)
    return result


def combine(columns, coefficients):
    result = {}
    for index, scale in coefficients.items():
        add(result, columns[index], scale)
    return result


def prefix(letter, vector):
    return {(letter,) + word: value for word, value in vector.items()}


def expand(seeds, proof):
    result = {}
    for word, value in proof.items():
        seed = seeds[word[-1]]
        add(result, {word[:-1] + w: a for w, a in seed.items()}, value)
    return result


def consequence(generators, arrows, seeds, target):
    """Return signed placements of seeds, or None for nonmembership."""
    def sort(word):
        vertex = generators[word[-1]]
        for letter in reversed(word[:-1]):
            source, dest = arrows[letter]
            if source != vertex:
                raise ValueError(f'ill-typed frame word {word}')
            vertex = dest
        return vertex

    window = set()
    for vector in (*seeds, target):
        if len({sort(word) for word in vector}) > 1:
            raise ValueError('a relation must have a single output type')
        for word in vector:
            window.update(word[i:] for i in range(len(word)))
    columns = list(seeds)
    proofs = [{(i,): 1} for i in range(len(seeds))]
    while True:
        pivots, _ = echelon(columns)
        solution = coordinates(pivots, target)
        if solution is not None:
            proof = combine(proofs, solution)
            assert expand(seeds, proof) == target
            return proof
        # Drop redundant generators while retaining their expressions in the seeds.
        basis = [v for v, _ in pivots.values()]
        witnesses = [combine(proofs, h) for _, h in pivots.values()]
        columns, proofs = list(basis), list(witnesses)
        for letter in arrows:
            forbidden = [{w: a for w, a in v.items() if (letter,) + w not in window}
                         for v in basis]
            _, kernel = echelon(forbidden)
            for h in kernel:
                vector = prefix(letter, combine(basis, h))
                if coordinates(pivots, vector) is None:
                    columns.append(vector)
                    proofs.append(prefix(letter, combine(witnesses, h)))
        if len(columns) == len(basis):
            return None


def algebra_checks():
    generators = {'g': 0}
    arrows = {a: (0, 0) for a in 'XYZW'}
    # Prefix after cancellation. Some monomials in the expanded proof lie outside the window.
    seeds = [{('X', 'g'): 1, ('Y', 'g'): -1, ('Z', 'g'): 2},
             {('X', 'g'): 1, ('Y', 'g'): -1}]
    word = ('W',) * 15 + ('Z', 'g')
    assert consequence(generators, arrows, seeds, {word: 2}) is not None
    assert consequence(generators, arrows, seeds, {word: 1}) is None
    assert consequence(generators, arrows, seeds, {('Z', 'W', 'g'): 2}) is None
    # Rank stays fixed as successive integral indices decrease.
    g, xg = ('g',), ('X', 'g')
    for bits in (1, 4, 9):
        seeds = [{g: 1, xg: -2}, {xg: 2**bits}]
        assert consequence(generators, arrows, seeds, {g: 1}) is not None
    seeds = [{('g',): 1, ('X', 'h'): -1}, {('Y', 'g'): 1, ('h',): -1}]
    sorts = {'g': 0, 'h': 1}
    typed = {'X': (1, 0), 'Y': (0, 1)}
    assert consequence(sorts, typed, seeds, {('X', 'Y', 'g'): 1, ('g',): -1})
    assert consequence(sorts, typed, seeds, {('g',): 1}) is None


def unary(ctx, term):
    disk = tree_ctx(disc_tree(tdim_tm(ctx, term)))
    top, = maximal_vars(disk)
    return ('coh', disk, disk[top], sub_from(disk, ctx, {top: term}))


def two_slot_split(emitter):
    r = 3
    column = string_tree(r, [r+1, r+1])
    ctx = tree_ctx(column + column)
    a, p, b, q = map(v, maximal_vars(ctx))
    initial = comp2(ctx, 0, src(ctx, a), src(ctx, b))
    finish = comp2(ctx, 0, tgt(ctx, p), tgt(ctx, q))
    last = unary(ctx, finish)
    # Change the second slot first, then the first, then both remaining links.
    moves = [comp2(ctx, 0, src(ctx, a), b), comp2(ctx, 0, a, tgt(ctx, b)),
             comp2(ctx, 0, p, q)]
    trunk = tree_ctx(disc_tree(r) + disc_tree(r))
    i, j = maximal_vars(trunk)
    state = comp2(trunk, 0, v(i), v(j))
    cap = subst_tm(head(trunk, state, unary(trunk, state)),
                   sub_from(trunk, ctx, {i: tgt(ctx, p), j: tgt(ctx, q)}))
    ordered = composite(ctx, r, [*moves, cap])
    direct = head(ctx, initial, last)
    ty = arr(infer(ctx, direct), direct, ordered)
    witness = head(ctx, direct, ordered)
    assert infer(ctx, witness) == ty
    if emitter:
        emitter.check_type('twoSlotSplit', ctx, witness, ty)


def raw_iteration(depth, emitter):
    ctx = tree_ctx(((), ()))
    r = 3
    path = comp2(ctx, 0, v(2), v(4))
    base = ident(ctx, ident(ctx, path))
    state = unary(ctx, base)
    top, = maximal_vars(state[1])
    go, back = head(ctx, base, state), head(ctx, state, base)

    def action(loop):
        return comp2(ctx, r, comp2(ctx, r, go, promote(ctx, state, top, loop)), back)

    def transport(proof):
        middle = promote_relation(ctx, state, top, proof)
        return comp2(ctx, r, comp2(ctx, r, go, middle), back)

    unit, loop = ident(ctx, base), head(ctx, base, base)
    nodes = [loop]
    for _ in range(depth):
        nodes.append(action(nodes[-1]))
    seeds = [{('g',): 1, ('X', 'g'): -1}, {('X',) * depth + ('g',): 1}]
    solution = consequence({'g': 0}, {'X': (0, 0)}, seeds, {('g',): 1})
    expected = {('X',) * j + (0,): 1 for j in range(depth)}
    expected[(1,)] = 1
    assert solution == expected
    cell = head(ctx, nodes[0], nodes[1])
    steps = []
    for j in range(depth):
        assert infer(ctx, cell) == arr(infer(ctx, nodes[j]), nodes[j], nodes[j+1])
        steps.append(cell)
        if j+1 < depth:
            cell = transport(cell)
    steps.append(head(ctx, nodes[-1], unit))
    result = steps[0]
    for step in steps[1:]:
        result = comp2(ctx, r+1, result, step)
    ty = arr(infer(ctx, loop), loop, unit)
    assert infer(ctx, result) == ty
    if emitter:
        emitter.check_type('frameConsequence', ctx, result, ty)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=4)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.depth < 1:
        parser.error('depth must be positive')
    output = Emitter() if args.agda else None
    algebra_checks()
    two_slot_split(output)
    raw_iteration(args.depth, output)
    if output:
        args.agda.write_text(output.module(args.agda.stem, 'Iterated placement of a based comparison.'))
    print(f'Checked typed integral frame consequences and a depth-{args.depth} raw certificate.')
