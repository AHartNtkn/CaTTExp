"""Compare serial and simultaneous actions in a nested two-slot CaTT term."""

from argparse import ArgumentParser
from pathlib import Path

from catt import (arr, check_ctx, comp2, fv_tm, infer, maximal_vars, src,
                  sub_from, subst_tm, tdim_tm, tgt, tree_ctx, tree_of, v)
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from gray_partial_cylinder_sections import positions
from gray_top_slot_promotion import expand, top_action
from rc2 import functor
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head


def action(target, arity, body, initial, arrows):
    return functor(target, None, arity, tree_of(arity), body, initial, arrows)


def root_path(arity, body, slots):
    """Generic distributor. A repeated slot receives a two-step string."""
    tree = tree_of(arity)
    names = positions(tree)
    lengths = {names[i][0]: slots.count(i) for i in slots}
    wide_tree, ends, stacks = expand(tree, lengths)
    wide = tree_ctx(wide_tree)
    initial = {i: v(ends[0][i]) for i in maximal_vars(arity)}
    state = initial.copy()
    steps = []
    used = dict.fromkeys(slots, 0)
    for i in slots:
        change = v(stacks[i][used[i]])
        used[i] += 1
        steps.append(action(wide, arity, body, state, {i: change}))
        state[i] = tgt(wide, change)
    cut = tdim_tm(arity, body)
    serial = comp2(wide, cut, *steps)
    together = {i: (v(row[0]) if len(row) == 1 else comp2(wide, cut, *map(v, row)))
                for i, row in stacks.items()}
    diagonal = action(wide, arity, body, initial, together)
    return wide, initial, stacks, head(wide, serial, diagonal), head(wide, diagonal, serial)


def factor(source, target, term, initial, changes, order):
    """Both directions, at the literal serial and simultaneous boundaries."""
    _, arity, ty, args = term
    body = ('coh', arity, ty, tuple(map(v, range(len(arity)))))
    slot_of = {}
    for mark in order:
        (slot_of[mark],) = (i for i in maximal_vars(arity) if mark in fv_tm(args[i]))
    slots = [slot_of[j] for j in order]
    wide, start, stacks, forward, backward = root_path(arity, body, slots)
    labels = {start[i][1]: subst_tm(args[i], initial) for i in start if i not in slots}
    state = list(initial)
    used = dict.fromkeys(slots, 0)
    for mark in order:
        i = slot_of[mark]
        nxt = state.copy()
        nxt[mark] = tgt(target, changes[mark])
        labels[stacks[i][used[i]]] = top_action(source, target, args[i], (state, nxt),
                                                 {mark: changes[mark]})
        state = nxt
        used[i] += 1
    sigma = sub_from(wide, target, labels)
    fwd, back = subst_tm(forward, sigma), subst_tm(backward, sigma)
    if slots[0] == slots[1]:
        i = slots[0]
        inner_fwd, inner_back = factor(source, target, args[i], initial, changes, order)
        # Regard the promoted root operation as linear in its one arrow.
        tree = tree_of(arity)
        name = positions(tree)[i][0]
        single, ends, row = expand(tree, {name: 1})
        chart = tree_ctx(single)
        start = {j: v(ends[0][j]) for j in maximal_vars(arity)}
        active = row[i][0]
        raised = action(chart, arity, body, start, {i: v(active)})
        base = {start[j][1]: subst_tm(args[j], initial) for j in start if j != i}
        def whisker(track):
            before = sub_from(chart, target, {**base, active: src(target, track)})
            after = sub_from(chart, target, {**base, active: tgt(target, track)})
            return top_action(chart, target, raised, (before, after), {active: track})
        cut = tdim_tm(source, term) + 1
        fwd = comp2(target, cut, fwd, whisker(inner_fwd))
        back = comp2(target, cut, whisker(inner_back), back)
    return fwd, back


def example():
    path = tree_ctx(((), ()))
    fg = comp2(path, 0, v(2), v(4))
    wire = infer(path, fg)
    # a,b,c,d,e are parallel to the two-edge path fg.
    base = path + (wire,) * 5
    a, b, c, d, e = [v(i) for i in range(len(path), len(base))]
    def two(start, end):
        return arr(wire, start, end)
    source = base + (two(fg, b), two(b, d), two(d, e))
    x, y, rest = map(v, range(len(base), len(source)))
    target = base + (two(fg, a), two(a, b), two(fg, b),
                     two(b, d), two(b, c), two(c, d), two(d, e))
    p, q, x1, y0, r, s, extra = map(v, range(len(base), len(target)))
    x0, y1 = comp2(target, 1, p, q), comp2(target, 1, r, s)
    k = len(target)
    target += (arr(infer(source, x), x0, x1), arr(infer(source, y), y0, y1))
    first = list(map(v, range(len(base)))) + [x0, y0, extra]
    term = comp2(source, 1, comp2(source, 1, x, y), rest)
    return source, target, term, first, {x[1]: v(k), y[1]: v(k + 1)}


def verify(emitter):
    source, target, term, initial, changes = example()
    for rank in range(2, 5):
        check_ctx(source)
        check_ctx(target)
        marks = list(changes)
        serial = []
        tracks = []
        for order in (marks, marks[::-1]):
            state = initial.copy()
            arrows = []
            for i in order:
                after = state.copy()
                after[i] = tgt(target, changes[i])
                arrows.append(top_action(source, target, term, (state, after), {i: changes[i]}))
                state = after
            path = comp2(target, rank, *arrows)
            diagonal = top_action(source, target, term, (initial, state), changes)
            fwd, back = factor(source, target, term, initial, changes, order)
            assert (src(target, fwd), tgt(target, fwd)) == (path, diagonal)
            assert (src(target, back), tgt(target, back)) == (diagonal, path)
            assert top_counts(target, path) == {h[1]: 1 for h in changes.values()}
            serial.append(path)
            tracks.append((fwd, back))
        result = comp2(target, rank + 1, tracks[0][0], tracks[1][1])
        expected = arr(infer(target, serial[0]), *serial)
        assert infer(target, result) == expected and serial[0] != serial[1]
        if rank <= 3:
            emitter.check_type('exchange-' + str(rank), target, result, expected)
        source, target, term = susp_ctx(source), susp_ctx(target), susp_tm(term)
        initial = [v(0), v(1)] + list(map(susp_tm, initial))
        changes = {i + 2: susp_tm(t) for i, t in changes.items()}


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    verify(emitter)
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Nested linear frame over composite boundaries.'))
    print('Both factorizations and the exchange at literal poles in ranks 4, 5 and 6.')
