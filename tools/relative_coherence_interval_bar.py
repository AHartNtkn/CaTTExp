"""Compare raw incidence and normalized interval bar chains in a three-vertex example."""
from argparse import ArgumentParser
from pathlib import Path

from catt import STAR, arr, comp2, infer, subst_tm, v
from ct_suspension import ident, susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_arity_resolution import difference, linear
from relative_coherence_arity_covers import GROUP, cover, presentation as group_presentation
from relative_coherence_cut import Cut, arity_cut, top_counts


def presentation(power, emitter):
    ctx = (STAR, STAR, STAR)
    names = ['x', 'z', 'y']
    cellular = {name: {} for name in names}

    def attach(name, negative, positive):
        nonlocal ctx
        base = infer(ctx, negative)
        assert base == infer(ctx, positive)
        ty = arr(base, negative, positive)
        index = len(ctx)
        ctx += (ty,)
        names.append(name)
        incidence = difference(top_counts(ctx, positive), top_counts(ctx, negative))
        cellular[name] = {names[i]: n for i, n in incidence.items()}
        if emitter:
            emitter.check_type(name, ctx, v(index), ty)
        return v(index)

    f = attach('f', v(0), v(1))
    g = attach('g', v(1), v(2))
    h = attach('h', v(0), v(2))
    attach('a', f, f)
    attach('b', g, g)
    d = attach('d', h, h)
    attach('l', comp2(ctx, 0, f, g), h)
    word = d
    for _ in range(1, power):
        word = comp2(ctx, 1, word, d)
    attach('t', ident(ctx, h), word)
    assert cellular['l'] == {'h': 1, 'f': -1, 'g': -1}
    assert cellular['t'] == {'d': power}
    return cellular


def check(power, emitter=None):
    cellular = presentation(power, emitter)
    # w is the composite fg. A,B,T are the two edges and face of its torus.
    # Each nondegenerate bar two-simplex comes from M(x,z) times M(z,y).
    bar = {name: dict(row) for name, row in cellular.items()}
    bar.update(w={'y': 1, 'x': -1}, l={'h': 1, 'w': -1}, A={}, B={}, T={})
    # Sign convention d = d_vertical + (-1)^q d_horizontal at vertical rank q.
    bar.update(e={'g': 1, 'w': -1, 'f': 1},
               ea={'A': 1, 'a': -1}, eb={'B': 1, 'b': -1}, et={'T': -1})
    include = {name: {name: 1} for name in cellular}
    include['l'] = {'l': 1, 'e': -1}
    for name, row in cellular.items():
        assert linear(include[name], bar.__getitem__) == linear(row, include.__getitem__)
    for row in bar.values():
        assert not linear(row, bar.__getitem__)

    # Independent complement to the cellular subcomplex. In this integral basis
    # the four bar product cells contract onto the four new one-arrow entries.
    extra = {'w': {'w': 1, 'g': -1, 'f': -1},
             'A': {'A': 1, 'a': -1}, 'B': {'B': 1, 'b': -1}, 'T': {'T': 1}}
    paired = {'w': ('e', -1), 'A': ('ea', 1), 'B': ('eb', 1), 'T': ('et', -1)}
    for name, (upper, sign) in paired.items():
        assert bar[upper] == {k: sign * n for k, n in extra[name].items()}
        assert not linear(extra[name], bar.__getitem__)
    # The changed basis has unit diagonal after placing the four upper cells first.
    columns = {**{upper: {upper: 1} for upper, _ in paired.values()}, **include, **extra}
    earlier = set()
    for name, col in columns.items():
        assert col[name] == 1 and set(col) <= earlier | {name}
        earlier.add(name)
    assert earlier == set(bar)


def lift_crossing(term, cut_lift):
    if term[0] == 'v':
        assert cut_lift[0] == 'v'
        return susp_tm(cut_lift)
    _, arity, boundary, labels = term
    right = frozenset(i for i, ty in enumerate(arity) if ty == STAR and labels[i] == v(1))
    cut = arity_cut(arity, right)
    if boundary[1] == STAR:
        crossing_labels = (cut_lift,)
    else:
        assert cut_lift[:3] == ('coh', cut.context(), cut.type(boundary))
        crossing_labels = cut_lift[3]
    lifted = list(labels)
    for i, label in zip(cut.indices, crossing_labels, strict=True):
        lifted[i] = lift_crossing(labels[i], label)
    return ('coh', arity, boundary, tuple(lifted))


def cover_check():
    base = group_presentation()
    sheets, _, _, path = cover(base)
    base_up, sheets_up = susp_ctx(base), susp_ctx(sheets)
    cut = Cut(sheets_up, {1})
    projection = ((v(0),) * 6 + (v(1),) * 6 + (v(2),) * 6
                  + tuple(v(i) for _ in GROUP for i in range(3, 6)))
    projection_up = (v(0), v(1), *map(susp_tm, projection))

    def decorate(ctx, term):
        left, right = (ident(ctx, v(i)) for i in (0, 1))
        return comp2(ctx, 0, left, comp2(ctx, 0, susp_tm(term), right))

    words = [v(1), v(2), comp2(base, 0, v(1), v(2)), comp2(base, 0, v(2), v(1))]
    count = 0
    for word in words:
        original = decorate(base_up, word)
        for sheet in GROUP:
            lifted_word, _ = path(word, sheet)
            expected = decorate(sheets_up, lifted_word)
            for term, answer in ((original, expected), (ident(base_up, original),
                                                         ident(sheets_up, expected))):
                infer(sheets_up, answer)
                assert subst_tm(answer, projection_up) == term
                assert lift_crossing(term, cut.term(answer)) == answer
                count += 1
    return count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    for power in (2, 3, 4, 5, 7):
        check(power, emitter if power == 3 else None)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Directed interval test at power three.'))
    print(f'5 torsion exponents, 5 raw cellular chain maps, 20 integral contraction pairs, '
          f'{cover_check()} suspended covering lifts')
