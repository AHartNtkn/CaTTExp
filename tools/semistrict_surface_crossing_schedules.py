"""Check schedule restriction and raw fourth-degree witnesses across one object span."""
from argparse import ArgumentParser
from itertools import permutations
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, glue_tree, infer, maximal_vars, src,
                  sub_from, subst_tm, tgt, tree_ctx, v)
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_cut import Cut
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_directed_reattachment import specialize


def check_schedules():
    pairs = 0
    for lengths in ((2, 2), (1, 1, 2), (2, 1, 2)):
        columns = tuple(i for i, n in enumerate(lengths) for _ in range(n))
        words = set(permutations(columns))

        def reversed_pairs(word):
            # Name a step by its interval and its position *within* that interval.
            counts = [0] * len(lengths)
            events = []
            for i in word:
                events.append((i, counts[i]))
                counts[i] += 1
            return {(a, b) for j, a in enumerate(events) for b in events[j + 1:] if a[0] > b[0]}

        orders = {word: reversed_pairs(word) for word in words}
        assert len({frozenset(order) for order in orders.values()}) == len(words)
        for start in words:
            reached, pending = {start}, [start]
            while pending:
                word = pending.pop()
                for i in range(len(word) - 1):
                    if word[i] <= word[i + 1]:
                        continue
                    step = word[:i] + (word[i + 1], word[i]) + word[i + 2:]
                    if step not in reached:
                        reached.add(step)
                        pending.append(step)
            assert reached == {word for word in words if orders[word] <= orders[start]}
            pairs += len(words)
    print(f'Checked the two-position readings against directed paths on {pairs} pairs of schedules.')


def compound_query(emitter):
    base = (STAR,) + (arr(STAR, v(0), v(0)),) * 3
    a, b, c = v(1), v(2), v(3)
    ab, cc = comp2(base, 0, a, b), comp2(base, 0, c, c)
    bc, aa = comp2(base, 0, b, c), comp2(base, 0, a, a)
    ctx = base + (arr(infer(base, ab), ab, cc),) * 2 + (arr(infer(base, bc), bc, aa),)
    change, replacement, second = v(4), v(5), v(6)
    ctx += (arr(infer(ctx, change), change, replacement),)
    rule = v(7)
    early, late = temporal_words(ctx, change, second, 0, 1)
    after, _ = temporal_words(ctx, replacement, second, 0, 1)
    native = specialize(ctx, glue_tree(2, 0, 2), (change, second),
                        lambda P, p, q: temporal_words(P, p, q, 0, 1)[::-1])
    placed = comp2(ctx, 1, comp2(ctx, 0, rule, bc), comp2(ctx, 0, cc, second))
    assert src(ctx, placed) == early and tgt(ctx, placed) == after
    witness = comp2(ctx, 2, native, placed)
    for name in ('localGray', 'globalCrossing'):
        emit_ty = arr(infer(ctx, late), late, after)
        assert infer(ctx, witness) == emit_ty
        emitter.check_type(name, ctx, witness, emit_ty)
        if name == 'localGray':
            source_ctx = ctx
            ctx, witness, late, after = susp_ctx(ctx), susp_tm(witness), susp_tm(late), susp_tm(after)
            cut = Cut(ctx, (1,))
            assert cut.context() == source_ctx and cut.term(witness) == comp2(source_ctx, 2, native, placed)

    # Enumerate the actual two-step histories and their placed directed moves.
    rules = (('A', 'ab', 'cc'), ('D', 'ab', 'cc'), ('B', 'bc', 'aa'))
    def histories(word, remaining):
        if not remaining:
            if word == 'ccaa':
                yield ()
            return
        for letter, old, new in rules:
            for pos in range(len(word) - len(old) + 1):
                if word.startswith(old, pos):
                    for rest in histories(word[:pos] + new + word[pos + len(old):], remaining - 1):
                        yield ((pos, letter), *rest)

    states = set(histories('abbc', 2))
    edges = set()
    for path in states:
        (i, first), (j, _) = path
        if j + 2 <= i:
            edges.add((path, path[::-1]))
        for slot, (pos, letter) in enumerate(path):
            if letter == 'A':
                edges.add((path, path[:slot] + ((pos, 'D'),) + path[slot + 1:]))
    assert len(states) == len(edges) == 4
    assert all(s in states and t in states for s, t in edges)
    initial, final = ((2, 'B'), (0, 'A')), ((0, 'D'), (2, 'B'))
    assert any((initial, p) in edges and (p, final) in edges for p in states)
    assert not any(s == final for s, _ in edges)


def stationary_head(emitter):
    # Retain a nonliteral stationary 2-label from the point at the left pole.
    point = tree_ctx(disc_tree(0))
    unit = identity(point, v(0))
    contraction = head(point, comp2(point, 0, unit, unit), unit)
    generic = tree_ctx(glue_tree(2, 0, 2))
    left, right = map(v, maximal_vars(generic))
    early, late = temporal_words(generic, left, right, 0, 1)
    crossing = head(generic, late, early)
    disk = tree_ctx(disc_tree(2))
    value = v(maximal_vars(disk)[0])
    kept = sub_from(generic, disk, {left[1]: contraction, right[1]: value})
    fitted = subst_tm(crossing, kept)
    assert src(disk, fitted) != tgt(disk, fitted)
    # A second representative at these actual written ends. The entire argument
    # now lives on the one active column, whose generic tag is an identity.
    direct = head(disk, src(disk, fitted), tgt(disk, fitted))
    assert fitted != direct
    for label, s, t in (('outerFit', fitted, direct), ('outerReturn', direct, fitted)):
        cell = head(disk, s, t)
        emitter.check_type(label, disk, cell, arr(infer(disk, s), s, t))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_schedules()
    emitter = Emitter()
    compound_query(emitter)
    stationary_head(emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        name = 'CrossingSchedules'
        module = emitter.module(name, __doc__).replace('open import CaTTExp.Pure',
                                                        'open import CaTTExp.Gray.Pure')
        (args.agda_dir / (name + '.agda')).write_text(module)
    print('Checked a compound directed rewrite before and after suspension, and both nonliteral outer fits.')
