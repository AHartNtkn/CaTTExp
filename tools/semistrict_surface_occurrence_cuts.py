"""Check occurrence cuts by planar replay and by colouring the vertices of a polyplex."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from catt import STAR, arr, comp2, infer, src, subst_tm, subst_ty, tgt, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity


def trace_ports(width, gates):
    tracks = {(i,) for i in range(width)}
    for start, inputs, outputs in gates:
        tracks = {t + (p,) for t in tracks if start <= t[-1] < start + inputs
                  for p in range(start, start + outputs)}
    return tracks


def chart_graph(width, gates):
    # Occurrences on the two spatial boundaries of a gate are shared; the
    # interior gaps of its output word are fresh, even for a repeated label.
    rows = [tuple(range(width + 1))]
    fresh = width + 1
    poles = []
    for start, inputs, outputs in gates:
        row = rows[-1]
        poles.append((row[start], row[start + inputs]))
        rows.append(row[:start + 1] + tuple(range(fresh, fresh + outputs - 1)) + row[start + inputs:])
        fresh += outputs - 1
    return rows, fresh, poles


def colourings(width, gates):
    rows, fresh, poles = chart_graph(width, gates)
    result = set()
    for colours in product((0, 1), repeat=fresh):
        if any((colours[a], colours[b]) != (0, 1) for a, b in poles):
            continue
        positions = []
        for row in rows:
            word = [colours[p] for p in row]
            if word[0] != 0 or word[-1] != 1 or word != sorted(word):
                break
            positions.append(word.index(1) - 1)
        else:
            result.add(tuple(positions))
    return result


def implications(width, gates, side):
    rows, size, poles = chart_graph(width, gates)
    tagged = [[(side, v) for v in row] for row in rows]
    edges = {(a, b) for row in tagged for a, b in zip(row, row[1:])}
    for v in range(size):
        edges.update({('bottom', (side, v)), ((side, v), 'top')})
    for a, b in poles:
        edges.update({((side, a), 'bottom'), ('top', (side, b))})
    return edges, tagged[0] + tagged[-1]


def closure(edges):
    neighbours = {}
    for a, b in edges:
        neighbours.setdefault(a, set()).add(b)
        neighbours.setdefault(b, set())
    result = {}
    for a in neighbours:
        seen, pending = {a}, [a]
        while pending:
            news = neighbours[pending.pop()] - seen
            seen.update(news)
            pending.extend(news)
        result[a] = seen
    return result


def permits_every_lift(source, whole):
    old, new = closure(source), closure(whole)
    return ('bottom' in old['top'] or
            all((new[a] & old.keys()) <= old[a] for a in old))


def check_extensions(charts):
    checked = 0
    for s in charts:
        source, sb = implications(2, s, 'source')
        sp = {(t[0], t[-1]) for t in trace_ports(2, s)}
        for t in charts:
            target, tb = implications(2, t, 'target')
            if len(sb) != len(tb):
                continue
            seams = set(zip(sb, tb))
            whole = source | target | seams | {(b, a) for a, b in seams}
            tp = {(tr[0], tr[-1]) for tr in trace_ports(2, t)}
            assert permits_every_lift(source, whole) == (sp <= tp)
            checked += 1
    return checked


def check_charts():
    checked = 0
    charts = []

    def visit(initial, width, gates):
        nonlocal checked
        assert trace_ports(initial, gates) == colourings(initial, gates)
        checked += 1
        if initial == 2 and 0 < len(gates) <= 2:
            charts.append(gates)
        if len(gates) == 3:
            return
        for inputs in (1, 2):
            for outputs in (1, 2):
                for start in range(width - inputs + 1):
                    visit(initial, width - inputs + outputs, gates + ((start, inputs, outputs),))

    for width in (1, 2, 3):
        visit(width, width, ())
    # H acts on both slots, L on the left. In H;H the intermediate
    # crossing position belongs to the 2-face and is fixed by a 4-lift.
    h, left = (0, 2, 2), (0, 1, 1)
    hh = colourings(2, (h, h))
    direct = {(s, t) for s in hh for t in hh if (s[0], s[-1]) == (t[0], t[-1])}
    detour = {(s, t) for s, t in direct for middle in colourings(2, (left, h))
              if s[0] == middle[0] == t[0] and s[1:] == middle[1:] == t[1:]}
    assert len(direct) == 16 and len(detour) == 2
    assert ((0, 0, 0), (0, 0, 0)) in detour
    assert ((0, 1, 0), (0, 1, 0)) in direct - detour
    extensions = check_extensions(charts)
    print(f'{checked} planar charts and {extensions} relative extension tests agree. The directed 4-detour accepts 2 of 16 source lifts.')


def positive_example(emitter):
    def build(coloured):
        ctx, fold = (), []

        def declare(ty, image):
            nonlocal ctx
            term = v(len(ctx))
            ctx += (ty,)
            fold.append(v(image))
            return term

        x = declare(STAR, 0)
        y = declare(STAR, 0) if coloured else x
        active = declare(arr(STAR, x, y), 1)
        right = declare(arr(STAR, y, y), 1) if coloured else active
        alpha = declare(arr(infer(ctx, active), active, active), 2)
        path = comp2(ctx, 0, active, right)
        both = declare(arr(infer(ctx, path), path, path), 3)
        left = comp2(ctx, 0, alpha, right)
        update_ty = arr(infer(ctx, left), left, both)
        u = declare(update_ty, 4)
        d = declare(update_ty, 5)
        repair = declare(arr(update_ty, u, d), 6)
        pad = identity(ctx, left)
        term = comp2(ctx, 2, pad, repair)
        ends = (comp2(ctx, 2, pad, u), comp2(ctx, 2, pad, d))
        assert (src(ctx, term), tgt(ctx, term)) == ends
        emitter.check_type('positioned' if coloured else 'repeated', ctx, term,
                           arr(infer(ctx, ends[0]), *ends))
        return ctx, term, tuple(fold)

    base, old, _ = build(False)
    cover, lifted, fold = build(True)
    for i, ty in enumerate(cover):
        assert subst_ty(ty, fold[:i]) == infer(base, fold[i])
    assert subst_tm(lifted, fold) == old
    emitter.check_eq('foldChange', lifted, fold, old)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_charts()
    emitter = Emitter()
    positive_example(emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('OccurrenceCuts', __doc__).replace('open import CaTTExp.Pure',
                                                                   'open import CaTTExp.Gray.Pure')
        (args.agda_dir / 'OccurrenceCuts.agda').write_text(module)
