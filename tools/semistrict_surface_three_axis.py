"""Decide length-monotone three-axis returns and test the unrestricted word reduction."""
import argparse
from collections import deque
from itertools import product
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, tgt, tree_ctx, v)
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_scalar_cube import check_cube, exchange

NATIVE = ('121', '212')
REVERSE = NATIVE[::-1]


def successors(word, rules):
    for left, right in rules:
        for start in range(len(word) - len(left) + 1):
            if word.startswith(left, start):
                yield word[:start] + right + word[start + len(left):]


def reaches(start, goal, rules, ceiling):
    """Exhaust exactly the induced graph on words of length at most ceiling."""
    if max(len(start), len(goal)) > ceiling:
        raise ValueError('endpoint outside the search space')
    pending = deque([start])
    seen = {start}
    while pending:
        word = pending.popleft()
        if word == goal:
            return True
        for after in successors(word, rules):
            if len(after) <= ceiling and after not in seen:
                pending.append(after)
                seen.add(after)
    return False


def monotone_return(attachments):
    """Exact cube return when all attachment length changes have the same weak sign."""
    changes = {len(right) - len(left) for left, right in attachments}
    if any(n < 0 for n in changes) and any(n > 0 for n in changes):
        raise ValueError('mixed length changes require unrestricted reachability')
    return reaches(*REVERSE, [NATIVE, *attachments], 3)


def encode_system(rules, start, finish):
    symbols = sorted(set(''.join([start, finish] + [w for pair in rules for w in pair])))
    # The two marker blocks have fresh run lengths. Interior block boundaries
    # are 1111, so matching a complete block synchronizes both ends.
    blocks = {c: '11' + '2' * (i + 2) + '11' for i, c in enumerate(symbols)}
    opening, closing = ('11' + '2' * i + '11' for i in (len(symbols) + 2, len(symbols) + 3))

    def encode(word):
        return ''.join(blocks[c] for c in word)

    def marked(word):
        return opening + encode(word) + closing

    encoded = [(encode(l), encode(r)) for l, r in rules]
    return marked, [NATIVE, (REVERSE[0], marked(start)), *encoded, (marked(finish), REVERSE[1])]


def check_reductions():
    alphabet = 'ab'
    words = [''.join(w) for n in range(1, 4) for w in product(alphabet, repeat=n)]
    checks = 0
    # Check every contextual application directly, including overlaps and length changes.
    for l, r in product(words, repeat=2):
        marked, rules = encode_system([(l, r)], 'aaa', 'bbb')
        for w in words:
            expected = {marked(t) for t in successors(w, [(l, r)])}
            if w == 'bbb':
                expected.add(REVERSE[1])
            assert set(successors(marked(w), rules)) == expected
            checks += 1
    decisions = 0
    for rules in [[('ab', 'ba')], [('aa', 'ab'), ('ab', 'bb')], [('a', 'b'), ('b', 'a')]]:
        for start, finish in product(words, repeat=2):
            marked, encoded = encode_system(rules, start, finish)
            same_size = [w for w in words if len(w) == len(start)]
            limit = max(len(marked(w)) for w in same_size)
            assert reaches(start, finish, rules, max(len(start), len(finish))) == reaches(
                *REVERSE, encoded, limit)
            decisions += 1
    # No single reverse declaration. A length-preserving two-step repair.
    rules = [NATIVE, ('21', '11'), ('112', '121')]
    assert reaches(*REVERSE, rules, 3)
    assert not reaches(*REVERSE, rules[:2], 3)
    assert monotone_return(rules[1:]) and not monotone_return([])
    assert not monotone_return([('212', '1')])
    assert not monotone_return([('212', '1121')])
    print(f'{checks} contextual encodings and {decisions} reachability comparisons passed.')


def specialize(term, paste, ambient, arguments):
    labels = sub_from(paste, ambient, dict(zip(maximal_vars(paste), arguments, strict=True)))
    return subst_tm(term, labels)


def fitted_crossing():
    """Make the directed square a loop on a literal two-scalar writing."""
    point = (STAR,)
    unit = identity(point, v(0))
    ctx = point + (arr(infer(point, unit), unit, unit),)
    a = v(1)
    unit_pair = comp2(point, 0, unit, unit)
    enter, leave = head(point, unit_pair, unit), head(point, unit, unit_pair)
    stationary = composite(ctx, 1, [enter, a, leave])
    disc = tree_ctx(disc_tree(2))
    alpha, = map(v, maximal_vars(disc))
    line = tree_ctx(disc_tree(1))
    edge, = map(v, maximal_vars(line))

    def forms(left):
        def whisker(G, t, f):
            if left:
                return comp2(G, 0, identity(G, src(G, f)), t)
            return comp2(G, 0, t, identity(G, tgt(G, f)))

        padded = whisker(line, edge, edge)
        unit_in = head(line, padded, edge)
        unit_out = head(line, edge, padded)
        before = specialize(unit_in, line, disc, [src(disc, alpha)])
        after = specialize(unit_out, line, disc, [tgt(disc, alpha)])
        middle = composite(disc, 1, [before, alpha, after])
        outside = whisker(disc, alpha, src(disc, alpha))
        actual_in = specialize(unit_in, line, point, [unit])
        actual_out = specialize(unit_out, line, point, [unit])

        def comparison(towards_stationary):
            s, t = (outside, middle) if towards_stationary else (middle, outside)
            disc_move = specialize(head(disc, s, t), disc, ctx, [a])
            i, j = (actual_in, enter) if towards_stationary else (enter, actual_in)
            k, l = (actual_out, leave) if towards_stationary else (leave, actual_out)
            point_move = composite(ctx, 1, [head(point, i, j), a, head(point, k, l)])
            pieces = (disc_move, point_move) if towards_stationary else (point_move, disc_move)
            return comp2(ctx, 2, *pieces)

        return comparison(False), comparison(True)

    from_left, to_left = forms(True)
    from_right, to_right = forms(False)
    crossing = composite(ctx, 2, [comp2(ctx, 1, from_left, from_right), exchange(ctx, a, a),
                                  comp2(ctx, 1, to_right, to_left)])
    return ctx, stationary, crossing


def raw_letters(emitter):
    """Realize both crossing positions as loops at one literal three-scalar writing."""
    ctx, stationary, crossing = fitted_crossing()
    pair = comp2(ctx, 1, stationary, stationary)
    triple = comp2(ctx, 1, pair, stationary)
    arity = tree_ctx(string_tree(1, [2, 2, 2]))
    x, y, z = map(v, maximal_vars(arity))
    ltree = comp2(arity, 1, comp2(arity, 1, x, y), z)
    rtree = comp2(arity, 1, x, comp2(arity, 1, y, z))
    reassoc = [specialize(head(arity, s, t), arity, ctx, [stationary]*3)
               for s, t in [(ltree, rtree), (rtree, ltree)]]
    one = comp2(ctx, 1, crossing, stationary)
    two = composite(ctx, 2, [reassoc[0], comp2(ctx, 1, stationary, crossing), reassoc[1]])
    loop_type = arr(infer(ctx, triple), triple, triple)
    for label, letter in [('one', one), ('two', two)]:
        assert infer(ctx, letter) == loop_type
        emitter.check_type(label, ctx, letter, loop_type)
    return ctx, one, two


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path, help='emit literal Gray typing checks')
    parser.add_argument('--rules', nargs='*', metavar='LEFT:RIGHT',
                        help='decide the fixed cube return for length-monotone crossing rules')
    args = parser.parse_args()
    if args.rules is not None:
        attachments = []
        for pair in args.rules:
            sides = pair.split(':')
            if len(sides) != 2 or any(set(side) - set('12') for side in sides):
                parser.error(f'invalid crossing rule {pair!r}')
            attachments.append(tuple(sides))
        try:
            answer = monotone_return(attachments)
        except ValueError as exc:
            parser.error(str(exc))
        print('raw return exists' if answer else 'raw return absent')
        return
    check_cube()
    check_reductions()
    emitter = Emitter()
    ctx, one, two = raw_letters(emitter)

    def spell(word):
        return composite(ctx, 2, [one if c == '1' else two for c in word])

    # A return via an intermediate 3-cell with strict crossing word 112.
    start, seam, end = map(spell, ('212', '112', '121'))
    base = infer(ctx, start)
    extended = ctx + (arr(base, start, seam), arr(base, seam, end))
    repair = comp2(extended, 3, v(2), v(3))
    assert infer(extended, repair) == arr(base, start, end)
    emitter.check_type('repair', extended, repair, arr(base, start, end))
    if args.agda:
        module = emitter.module(args.agda.stem, 'Raw scalar crossing letters and composite repair.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n', 'open import CaTTExp.Gray.Pure\n'))
    print('Two raw width-three crossing letters and their two-declaration return typechecked.')


if __name__ == '__main__':
    main()
