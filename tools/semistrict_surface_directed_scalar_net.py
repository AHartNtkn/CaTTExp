"""Check raw exchanges of positioned scalar 3-cells and their Petri-net firings."""
from argparse import ArgumentParser
from collections import Counter, deque
from itertools import product
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, infer, maximal_vars, src,
                  subst_tm, tdim, tgt, tree_ctx, v)
from ct_suspension import ident, susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, string_tree
from semistrict_surface_directed_power_queries import apply, crossing, row_fit


def row(ctx, *terms):
    return composite(ctx, 1, terms)


def wedge_unit(ctx, edge, left):
    return (comp2(ctx, 0, ident(ctx, src(ctx, edge)), edge) if left else
            comp2(ctx, 0, edge, ident(ctx, tgt(ctx, edge))))


def bridge(ctx, edge, left, out):
    line = tree_ctx(disc_tree(1))
    f = v(2)
    ends = (f, wedge_unit(line, f, left))
    return apply(ctx, (line, head(line, *(ends if out else ends[::-1]))), [edge])


def scalar_exchange():
    point = (STAR,)
    x = v(0)
    unit = ident(point, x)
    loop = arr(infer(point, unit), unit, unit)
    ctx = point + (loop, loop)
    a, b = v(1), v(2)
    outward, inward = [bridge(point, unit, False, out) for out in (True, False)]

    def unary(term, left, expand):
        disk = tree_ctx(disc_tree(2))
        z = v(maximal_vars(disk)[0])
        outer = src(disk, src(disk, z)) if left else tgt(disk, tgt(disk, z))
        fixed = ident(disk, outer)
        placed = comp2(disk, 0, fixed, z) if left else comp2(disk, 0, z, fixed)
        padded = row(disk, bridge(disk, src(disk, z), left, True), placed,
                     bridge(disk, tgt(disk, z), left, False))
        generic = head(disk, z, padded) if expand else head(disk, padded, z)
        factor = apply(ctx, (disk, generic), [term])
        if not left:
            return factor
        # Use the same two point terms at the rim of both whiskerings.
        old_out = bridge(point, unit, True, True)
        old_in = bridge(point, unit, True, False)
        change_out, change_in = ((old_out, outward), (old_in, inward))
        if not expand:
            change_out, change_in = change_out[::-1], change_in[::-1]
        adjust_out = row(ctx, head(point, *change_out), comp2(ctx, 0, unit, term),
                         old_in if expand else inward)
        adjust_in = row(ctx, outward if expand else old_out, comp2(ctx, 0, unit, term),
                        head(point, *change_in))
        tracks = [factor, adjust_out, adjust_in] if expand else [adjust_out, adjust_in, factor]
        return composite(ctx, 2, tracks)

    def fit_pair(left, right, join):
        expanded = row(ctx, row(ctx, outward, left, inward), row(ctx, outward, right, inward))
        pad = row(point, inward, outward)
        separated = row(ctx, outward, left, pad, right, inward)
        rim = wedge_unit(point, unit, False)
        unit_step = ident(point, rim)
        compact = row(ctx, outward, row(ctx, left, right), inward)
        # Cancel the internal pair of point transports, then the temporal unit.
        cancel = head(point, pad, unit_step) if join else head(point, unit_step, pad)
        middle = row(ctx, outward, left, cancel, right, inward)
        arity = tree_ctx(string_tree(1, [2] * 4))
        p, h, k, q = map(v, maximal_vars(arity))
        spaced = row(arity, p, h, ident(arity, tgt(arity, h)), k, q)
        grouped = row(arity, p, row(arity, h, k), q)
        ends = (spaced, grouped) if join else (grouped, spaced)
        clean = apply(ctx, (arity, head(arity, *ends)), [outward, left, right, inward])
        assert (tgt(ctx, clean) if join else src(ctx, clean)) == compact
        steps = ([row_fit(ctx, expanded, separated), middle, clean] if join else
                 [clean, middle, row_fit(ctx, separated, expanded)])
        return composite(ctx, 2, steps)

    native = crossing(ctx, a, b)
    bl, ar = comp2(ctx, 0, unit, b), comp2(ctx, 0, a, unit)
    open_b = unary(b, True, True)
    steps = [row(ctx, open_b, a),
             row(ctx, tgt(ctx, open_b), unary(a, False, True)),
             fit_pair(bl, ar, True), row(ctx, outward, native, inward),
             fit_pair(ar, bl, False), row(ctx, unary(a, False, False), row(ctx, outward, bl, inward)),
             row(ctx, a, unary(b, True, False))]
    term = composite(ctx, 2, steps)
    assert src(ctx, term) == row(ctx, b, a) and tgt(ctx, term) == row(ctx, a, b)
    return susp_ctx(ctx), susp_tm(term)


def edge_word(ctx, term):
    if term[0] == 'v':
        return (term[1],)
    _, arity, _, labels = term
    return tuple(edge for i, ty in enumerate(arity) if tdim(ty) == 0
                 for edge in edge_word(ctx, labels[i]))


def marking(ctx, term):
    if term[0] == 'v':
        return Counter({(term[1], 0): 1})
    _, arity, _, labels = term
    offset = {}
    current = 0
    for i, ty in enumerate(arity):
        if tdim(ty) == 0 and ty[2][1] not in offset:
            offset[ty[2][1]] = current
            current += len(edge_word(ctx, labels[i]))
    tokens = Counter()
    for i, ty in enumerate(arity):
        if tdim(ty) == 2:
            position = ty[1][1][2][1]
            for (letter, start), count in marking(ctx, labels[i]).items():
                tokens[letter, offset[position] + start] += count
    return tokens


def placed_examples(emitter):
    scalar_ctx, swap = scalar_exchange()
    emitter.check_typed('nativeScalarSwap', scalar_ctx, swap)
    ctx = (STAR, arr(STAR, v(0), v(0)))
    x, f = v(0), v(1)
    pole = ident(ctx, f)
    loop = arr(infer(ctx, pole), pole, pole)
    ctx += (loop, loop)
    a, b = v(2), v(3)
    rule = v(len(ctx))
    ctx += (arr(loop, comp2(ctx, 2, a, b), b),)
    empty_face = ident(ctx, ident(ctx, x))
    empty = v(len(ctx))
    ctx += (arr(infer(ctx, empty_face), empty_face, empty_face),)
    line = tree_ctx(((), ()))
    left, right = map(v, maximal_vars(line))

    def positioned(z, second):
        ff = comp2(line, 0, left, right)
        base = (comp2(line, 0, left, ident(line, right)) if second else
                comp2(line, 0, ident(line, left), right))
        to = apply(ctx, (line, head(line, ident(line, ff), base)), (f, f))
        back = apply(ctx, (line, head(line, base, ident(line, ff))), (f, f))
        middle = comp2(ctx, 0, f, z) if second else comp2(ctx, 0, z, f)
        return composite(ctx, 2, [to, middle, back])

    x0, y1 = positioned(a, False), positioned(b, True)
    ff = comp2(ctx, 0, f, f)
    for label, first, second in [('across', x0, y1), ('back', y1, x0)]:
        move = subst_tm(swap, (x, x, ff, first, second))
        target = arr(infer(ctx, second), comp2(ctx, 2, second, first), comp2(ctx, 2, first, second))
        assert infer(ctx, move) == target
        emitter.check_type(label, ctx, move, target)
    assert marking(ctx, comp2(ctx, 2, x0, y1)) == Counter({(2, 0): 1, (3, 1): 1})
    for index in (0, 1):
        firing = comp2(ctx, 0, f, rule) if index else comp2(ctx, 0, rule, f)
        emitter.check_typed('firing' + str(index), ctx, firing)
        assert marking(ctx, src(ctx, firing)) == Counter({(2, index): 1, (3, index): 1})
        assert marking(ctx, tgt(ctx, firing)) == Counter({(3, index): 1})
    gaps = (comp2(ctx, 0, empty, ff), comp2(ctx, 0, comp2(ctx, 0, f, empty), f),
            comp2(ctx, 0, ff, empty))
    for index, event in enumerate(gaps):
        assert marking(ctx, event) == Counter({(empty[1], index): 1})
        emitter.check_typed('gap' + str(index), ctx, event)


def reachable(start, successors):
    seen = {start}
    todo = deque([start])
    while todo:
        for end in successors(todo.popleft()):
            if end not in seen:
                seen.add(end)
                todo.append(end)
    return seen


def check_firings():
    # Compare placed ordered words with markings. The spectator token in each
    # guarded rule is present on both sides and is required to enable it.
    letters = range(4)
    rules = [((0, 1), (1, 1)), ((1, 2), (0, 2)), ((2, 3), (3, 3))]
    def word_steps(word):
        for i in range(len(word) - 1):
            yield word[:i] + (word[i + 1], word[i]) + word[i + 2:]
            for pre, post in rules:
                if word[i:i + 2] == pre:
                    yield word[:i] + post + word[i + 2:]

    def count(word):
        return tuple(word.count(k) for k in letters)

    def net_steps(mark):
        for pre, post in rules:
            need, give = count(pre), count(post)
            if all(a >= b for a, b in zip(mark, need)):
                yield tuple(a - b + c for a, b, c in zip(mark, need, give))

    for n in range(5):
        for start in product(letters, repeat=n):
            assert {count(end) for end in reachable(start, word_steps)} == reachable(count(start), net_steps)
    return sum(4 ** n for n in range(5))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    placed_examples(emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        code = emitter.module('DirectedScalarNet', __doc__)
        (args.agda_dir / 'DirectedScalarNet.agda').write_text(
            code.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))
    print(f'Checked both literal scalar exchanges, the two firings, three gaps and {check_firings()} ordered inputs.')


if __name__ == '__main__':
    main()
