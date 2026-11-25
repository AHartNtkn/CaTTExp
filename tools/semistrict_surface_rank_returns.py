"""Check occurrence filters on compound high attachments and a two-rule return."""
from argparse import ArgumentParser
from functools import cache
from itertools import product
from pathlib import Path

from catt import STAR, arr, fv_tm, fv_ty, infer, src, tdim, tdim_tm, tgt, v
from ct_suspension import ident
from relative_coherence_exchange_faces import composite
from semistrict_surface_directed_ports import occurrences
from semistrict_surface_empty_returns import return_rules
from semistrict_surface_grid_factors import write_module
from semistrict_surface_inverse_completion import DerivationEmitter
from semistrict_surface_rectangle_subdivision import marked_inputs
from semistrict_surface_thin_subdivision import partition_route


def net(ctx, rank):
    def counts(t):
        return occurrences(ctx, t, rank - 1)
    places = [i for i, ty in enumerate(ctx) if tdim(ty) + 1 == rank - 1]
    rules = {i: (counts(ty[2]), counts(ty[3])) for i, ty in enumerate(ctx) if tdim(ty) + 1 == rank}
    return dict(point_gates=places, rules=rules)


def retained_declarations(ctx, s, t):
    """Return original declaration indices, or None if the grades exclude the query."""
    from semistrict_surface_one_test_reachability import ordinary
    from semistrict_surface_positive_labels import reachable

    assert infer(ctx, s) == infer(ctx, t)
    n = 1 + tdim_tm(ctx, s)
    dims = [1 + tdim(ty) for ty in ctx]
    keep = {i for i, dim in enumerate(dims) if dim <= n}
    while True:
        result = keep.copy()
        for j in range(2, n + 1):
            places = sorted(i for i in keep if dims[i] == j - 1)

            def marking(term, face):
                while tdim_tm(ctx, term) > j - 1:
                    term = face(ctx, term)
                labels = occurrences(ctx, term, j - 1)
                assert set(labels) <= set(places)
                return tuple(labels.count(p) for p in places)

            m, end = marking(s, src), marking(t, tgt)
            grades = {i: (marking(v(i), src), marking(v(i), tgt))
                      for i in keep if dims[i] >= j - 1}
            changes = set(grades[i] for i in keep if dims[i] == j)
            if m != end and not reachable(dict(source=m, target=end, transitions=list(changes))):
                return None
            edges = [(k, k, a, b) for a, b in changes for k in (0, 1)]

            @cache
            def eligible(p, q):
                return reachable(ordinary((0, m), (1, end), edges + [(0, 1, p, q)]))

            result.difference_update(i for i, grade in grades.items() if not eligible(*grade))
        assert set(fv_tm(s)) | set(fv_tm(t)) <= result
        assert all(set(fv_ty(ctx[i])) <= result for i in result)
        if result == keep:
            return result
        keep = result


def bounds_example(emitter):
    ctx, inputs, *_ = marked_inputs(2, True)
    direct, split = [partition_route(ctx, inputs, 2, cuts, True) for cuts in [(2,), (1, 2)]]
    # The lower context may even have a new change opposite an actual 3-history.
    history = src(ctx, direct)
    ctx += (arr(infer(ctx, src(ctx, history)), tgt(ctx, history), src(ctx, history)),)
    p, q = v(len(ctx)), v(len(ctx) + 1)
    ctx += (infer(ctx, direct), infer(ctx, direct))

    def arrow(a, b):
        nonlocal ctx
        assert infer(ctx, a) == infer(ctx, b)
        name = v(len(ctx))
        ctx += (arr(infer(ctx, a), a, b),)
        return name

    birth = arrow(direct, p)
    death = arrow(q, split)
    arrow(p, p)
    arrow(q, q)
    assert not return_rules(net(ctx, 5))
    join = arrow(p, q)
    assert set(return_rules(net(ctx, 5))) == {i for i, ty in enumerate(ctx) if tdim(ty) + 1 == 5}
    repair = composite(ctx, 4, [birth, join, death])
    assert (src(ctx, repair), tgt(ctx, repair)) == (direct, split)
    if emitter:
        emitter.check_type('repairAtOldFaces', ctx, repair, arr(infer(ctx, direct), direct, split))


def monitored_checks():
    options = [((1, 0), (0, 1)), ((0, 1), (1, 0)), ((2, 0), (0, 2)), ((1, 1), (2, 0))]
    marks = [(i, 3 - i) for i in range(4)]

    def fire(m, rule):
        p, q = rule
        if all(a >= b for a, b in zip(m, p)):
            return tuple(a - b + c for a, b, c in zip(m, p, q))
        return None

    for mask in range(1 << len(options)):
        rules = [x for i, x in enumerate(options) if mask & (1 << i)]
        def close(start, transitions):
            seen, todo = {start}, [start]
            while todo:
                m = todo.pop()
                for rule in transitions:
                    t = fire(m, rule)
                    if t is not None and t not in seen:
                        seen.add(t)
                        todo.append(t)
            return seen
        for s, t in product(marks, repeat=2):
            forward = close(s, rules)
            backward = close(t, [(q, p) for p, q in rules])
            for probe in options:
                window = any(fire(m, probe) in backward for m in forward)
                live, todo = {(s, False)}, [(s, False)]
                while todo:
                    m, seen = todo.pop()
                    for rule, flag in [(r, seen) for r in rules] + ([(probe, True)] if not seen else []):
                        out = fire(m, rule)
                        if out is not None and (out, flag) not in live:
                            live.add((out, flag))
                            todo.append((out, flag))
                assert window == ((t, True) in live)


def incidence_encoding(rank, solve):
    """Read the controlled machine back from the attaching terms of a raw context."""
    ctx = (STAR,)
    pole = v(0)
    for _ in range(rank - 2):
        pole = ident(ctx, pole)
    loop_type = arr(infer(ctx, pole), pole, pole)
    start, run, stop, a, b = range(1, 6)
    ctx += (loop_type,) * 5
    ports = [([start], [stop]), ([start], [run, a, a]),
             ([run, a, a], [run, b]), ([run, b], [stop])]
    first = len(ctx)
    for incoming, outgoing in ports:
        s, t = [composite(ctx, rank - 2, list(map(v, side))) for side in (incoming, outgoing)]
        assert infer(ctx, s) == infer(ctx, t)
        ctx += (arr(infer(ctx, s), s, t),)
    assert infer(ctx, v(first)) == arr(loop_type, v(start), v(stop))
    data = net(ctx, rank)
    assert data['point_gates'] == list(range(1, 6))
    assert list(data['rules'].values()) == ports
    if solve:
        assert retained_declarations(ctx, v(start), v(stop)) == set(range(len(ctx)))
        # The bypass still fills. The exit now asks for an extra a after consuming both.
        ctx = ctx[:-1] + (arr(loop_type, composite(ctx, rank - 2, [v(run), v(b), v(a)]), v(stop)),)
        assert retained_declarations(ctx, v(start), v(stop)) == {0, start, stop, first}


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    parser.add_argument('--solve', action='store_true', help='also run the exact filter (requires islpy)')
    args = parser.parse_args()
    emitter = DerivationEmitter() if args.agda_dir else None
    monitored_checks()
    for rank in range(3, 7):
        incidence_encoding(rank, args.solve)
    bounds_example(emitter)
    if emitter:
        write_module(emitter, args.agda_dir, 'RankReturns', __doc__)
    print('Checked 1024 monitored tests, controlled incidence in ranks 3–6, and the fifth-degree repair.')


if __name__ == '__main__':
    main()
