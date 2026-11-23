"""Validate full binary histories against raw words, strict chains and typed witnesses."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from itertools import permutations, product
from pathlib import Path

from catt import (TypeError_, arr, comp2, disc_tree, glue_tree, infer, maximal_vars,
                  tdim_tm, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_full_binary import (NoWord, WordProblem, compose, evaluate, generators,
                                           infer_surface, type_value, unit, word_representative)
from semistrict_surface_identity_classes import unary


def render(ctx, expr):
    if expr[0] == 'v':
        return expr
    if expr[0] == 'id':
        return identity(ctx, render(ctx, expr[1]))
    return comp2(ctx, expr[1], render(ctx, expr[2]), render(ctx, expr[3]))


def exhaustive(shape, counts, max_size=5):
    ctx = tree_ctx(shape)
    env = generators(ctx)
    words = defaultdict(dict)
    for i in range(len(ctx)):
        term = v(i)
        words[1][term] = (term, (i,))
    groups = {}
    for size in range(1, max_size + 1):
        current = words[size]
        for arg, (word, _) in words[size - 1].items():
            if tdim_tm(ctx, arg) < 3:
                current[identity(ctx, arg)] = (('id', word), ())
        for left_size in range(1, size):
            for (a, (wa, ca)), (b, (wb, cb)) in product(words[left_size].items(), words[size - left_size].items()):
                p, q = tdim_tm(ctx, a), tdim_tm(ctx, b)
                for cut in range(min(p, q)):
                    ta, tb = infer(ctx, a), infer(ctx, b)
                    for _ in range(p - cut - 1):
                        ta = ta[1]
                    for _ in range(q - cut - 1):
                        tb = tb[1]
                    if ta[3] != tb[2]:
                        continue
                    chain = (ca if p >= q else ()) + (cb if q >= p else ())
                    current[comp2(ctx, cut, a, b)] = (('bin', cut, wa, wb), tuple(sorted(chain)))
        for t, (_, chain) in current.items():
            assert infer_surface(ctx, t) == infer(ctx, t)
            h = evaluate(t, env)
            if h.rank == 0:
                continue
            # At fixed old faces in a globular tree the ordinary strict top chain
            # determines the strict cell (the lower rows come from those faces).
            key = infer(ctx, t), chain
            if key in groups:
                assert groups[key] == h
                counts['comparisons at equal strict chains and literal faces'] += 1
            else:
                groups[key] = h
            w = word_representative(ctx, h)
            assert w is not None
            read = render(ctx, w)
            assert evaluate(read, env) == h
            counts['typed word readbacks'] += 1


def complete_shuffles(shape, split, counts, emitter):
    ctx = tree_ctx(shape)
    env = generators(ctx)
    atoms = [v(i) for i in maximal_vars(ctx)]
    rank = tdim_tm(ctx, atoms[0])
    assert all(tdim_tm(ctx, t) == rank for t in atoms)

    def tree(node, values):
        if isinstance(node, int):
            return values[node]
        cut, l, r = node
        return comp2(ctx, cut, tree(l, values), tree(r, values))

    combined = tree(split, atoms)
    value = evaluate(combined, env)
    for order in permutations(range(len(atoms))):
        values = [infer(ctx, a)[2] for a in atoms]
        reading = None
        for k in order:
            values[k] = atoms[k]
            step = tree(split, values)
            reading = step if reading is None else comp2(ctx, rank - 1, reading, step)
            values[k] = infer(ctx, atoms[k])[3]
        assert infer(ctx, reading) == infer(ctx, combined)
        assert evaluate(reading, env) == value
        counts['serial orders compared with the binary paste'] += 1
    witness = render(ctx, word_representative(ctx, value))
    assert evaluate(witness, env) == value
    emitter.check_type(f'shuffle{rank}', ctx, witness, infer(ctx, witness))


def redexes(rank, counts, emitter):
    ctx = tree_ctx(string_tree(rank - 1, [rank, rank]))
    env = generators(ctx)
    a, b = [v(i) for i in maximal_vars(ctx)]
    word = comp2(ctx, rank - 1, a, b)
    plain = head(ctx, word, word)
    hidden = unary(ctx, word)
    special = head(ctx, hidden, hidden)
    assert evaluate(plain, env) == evaluate(identity(ctx, word), env)
    assert word_representative(ctx, evaluate(hidden, env)) is None
    assert evaluate(special, env) != evaluate(identity(ctx, hidden), env)
    # Congruence in the generic type of the binary head. Both raw faces use
    # top-unit padding and the operation must act as the same binary composite.
    if rank >= 2:
        s, t = infer(ctx, word)[2:]
        def pad(z):
            return comp2(ctx, rank - 2, identity(ctx, infer(ctx, z)[2]), z)
        alt = head(ctx, pad(s), pad(t))
        assert alt != word and evaluate(alt, env) == evaluate(word, env)
        emitter.check_type(f'convertedBinary{rank}', ctx, alt, infer(ctx, alt))
    counts['pairs of eligible and ineligible reflexive heads'] += 1


def conversion_only(counts):
    # Left whiskering by a unit changes the literal endpoint of a 2-variable.
    # After conversion it composes with the next 2-variable on this same edge.
    ctx = tree_ctx(glue_tree(2, 1, 2))
    env = generators(ctx)
    a, b = (env[i] for i in maximal_vars(ctx))
    x = env[0]
    moved = compose(0, unit(x), a)
    h = compose(1, moved, b)
    assert word_representative(ctx, moved) is not None
    assert word_representative(ctx, h) is None
    # Both slots move at the same tagged address when the entire chain is whiskered.
    repaired = compose(0, unit(x), compose(1, a, b))
    assert word_representative(ctx, repaired) is not None
    assert h != repaired
    # Write the converted composite in the ordinary raw constructor signature.
    # The middle 1-label is chosen from b; both choices have the same surface value.
    a_raw, b_raw = map(v, maximal_vars(ctx))
    left = comp2(ctx, 0, identity(ctx, v(0)), a_raw)
    _, arity, ty, labels = comp2(ctx, 1, a_raw, b_raw)
    labels = list(labels)
    labels[maximal_vars(arity)[0]] = left
    expr = ('coh', arity, ty, tuple(labels))
    try:
        infer(ctx, expr)
    except TypeError_:
        pass
    else:
        raise AssertionError('the incidence should require unit conversion')
    infer_surface(ctx, expr)
    broken = list(labels)
    broken[maximal_vars(arity)[1]] = a_raw
    try:
        infer_surface(ctx, ('coh', arity, ty, tuple(broken)))
    except ValueError:
        pass
    else:
        raise AssertionError('a different generating seam passed conversion')
    assert evaluate(expr, env) == h
    incident = infer(ctx, b_raw)
    outer_faces = arr(incident[1], infer(ctx, left)[2], incident[3])
    endo = ('coh', ctx, arr(outer_faces, expr, expr), tuple(map(v, range(len(ctx)))))
    expected = arr(outer_faces, expr, expr)
    assert type_value(ctx, infer_surface(ctx, endo)) == type_value(ctx, expected)
    assert evaluate(endo, env) != unit(h)
    counts['conversion-only word and common-address control'] += 1



def prescribed_faces(counts):
    # Two normalized 2-words have equal 1-faces modulo units. To bind them
    # inside one raw expression, their selected literal 1-writings must agree.
    ctx = tree_ctx(glue_tree(2, 1, 2))
    env = generators(ctx)
    a, b = (env[i] for i in maximal_vars(ctx))
    for left_pad, right_pad in product((False, True), repeat=2):
        def pad(cell, before):
            if before:
                return compose(0, unit(env[0]), cell)
            return compose(0, cell, unit(env[1]))
        problem = WordProblem(ctx)
        x, y = (problem.unknown(pad(cell, side)) for cell, side in ((a, left_pad), (b, right_pad)))
        problem.equations.append((problem.face(x, True), problem.face(y, False)))
        try:
            problem.solve(x)
        except NoWord:
            assert left_pad != right_pad
        else:
            assert left_pad == right_pad
            u, w = (render(ctx, problem.resolve(i)) for i in (x, y))
            comp2(ctx, 1, u, w)
        counts['simultaneous literal seam problems'] += 1

    # Acyclicity of a finite literal word is stronger than equality of its
    # normalized value. The two sides have the same normalized 1-path.
    problem = WordProblem(ctx)
    x = problem.unknown(a.source)
    problem.equations.append((x, ('bin', 0, ('id', v(0)), x)))
    try:
        problem.solve(x)
    except NoWord:
        counts['cyclic literal binding rejected'] += 1
    else:
        raise AssertionError('a finite word cannot contain itself properly')


def folded_attachment(counts):
    graph = tree_ctx(((), ()))
    p = comp2(graph, 0, v(2), v(4))
    base = infer(graph, p)
    ctx = graph + (arr(base, p, p), arr(base, p, p))
    a, b = v(len(graph)), v(len(graph) + 1)
    wrapped = comp2(ctx, 1, identity(ctx, p), a)
    ctx += (arr(infer(ctx, a), wrapped, b),)
    env = generators(ctx)
    assert env[-1].source == env[a[1]] and env[-1].target == env[b[1]]
    assert env[-1].source != env[-1].target
    fctx = ctx[:-2] + (arr(infer(ctx, a), wrapped, a),)
    fenv = generators(fctx)
    labels = fenv[:-1] + (fenv[a[1]], fenv[-1])
    assert evaluate(v(len(ctx) - 1), labels) == fenv[-1]
    assert fenv[-1].source == fenv[-1].target
    counts['surface generator typed before and after a computad fold'] += 1


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    counts, emitter = Counter(), Emitter()
    for shape in [((), (), ()), glue_tree(2, 0, 2), glue_tree(2, 1, 2),
                  glue_tree(3, 1, 2), glue_tree(3, 2, 3)]:
        exhaustive(shape, counts)
    for rank in range(2, 5):
        d = disc_tree(rank - 1)
        pair = (disc_tree(rank - 2), disc_tree(rank - 2))
        if rank == 2:
            complete_shuffles((d, d, d), (0, (0, 0, 1), 2), counts, emitter)
        else:
            complete_shuffles((pair, d), (0, (1, 0, 1), 2), counts, emitter)
    for rank in range(1, 5):
        redexes(rank, counts, emitter)
    conversion_only(counts)
    prescribed_faces(counts)
    folded_attachment(counts)
    if args.agda_dir:
        name = 'FullBinaryReadback'
        (args.agda_dir / (name + '.agda')).write_text(emitter.module(name, __doc__))
    for name, count in counts.items():
        print(f'{count:,} {name}')


if __name__ == '__main__':
    main()
