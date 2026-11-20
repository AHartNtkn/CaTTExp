"""Reduce comparison at finitely many literal poles to canonical chart and triangle comparisons."""
from argparse import ArgumentParser
from functools import cache
from itertools import combinations, product
from pathlib import Path

from catt import (STAR, arr, comp2, disc_tree, infer, maximal_vars, ps_dim, src, sub_from, subst_tm, subst_ty, tdim,
                  tdim_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_intermediates import Chart, charts, example, fill_chart, terms_of_rank
from relative_coherence_state_paths import at, boundary, common, temporal


def modes(ambient, s, t, refs):
    r = tdim_tm(ambient, s)
    for a, b in product(charts(ambient, s), charts(ambient, t)):
        p = a.arity
        if p != b.arity or infer(p, a.term) != infer(p, b.term):
            continue
        different = {j for j, (x, y) in enumerate(zip(a.labels, b.labels, strict=True)) if x != y}
        slots = {j for j in maximal_vars(p) if tdim(p[j])+1 == r}
        if not different <= slots:
            continue
        optional = sorted(slots-different)
        for k in range(len(optional)+1):
            for added in combinations(optional, k):
                active = sorted(different.union(added))
                yield fill_chart(ambient, a, b, active, refs)


def columns(arity, ty, args, r):
    trunk, minus, a = boundary(arity, '-', ty[2], r)
    other, plus, b = boundary(arity, '+', ty[3], r)
    assert trunk == other
    first = Chart(trunk, a, tuple(args[i[1]] for i in minus))
    last = Chart(trunk, b, tuple(args[i[1]] for i in plus))
    next_link = {d[2][1]: (i, d[3][1]) for i, d in enumerate(arity) if tdim(d) == r}
    strings = {}
    for j, (x, y) in enumerate(zip(minus, plus, strict=True)):
        i = x[1]
        if i != y[1]:
            strings[j] = []
        while i != y[1]:
            link, i = next_link[i]
            strings[j].append(link)
    return first, last, strings


class BoundaryBasis:
    def __init__(self, ambient, states, refs):
        self.ctx = ambient
        self.r = tdim_tm(ambient, states[0])
        assert ps_dim(ambient) < self.r and all(tdim_tm(ambient, x) == self.r for x in states)
        assert set(terms_of_rank(ambient, states, self.r)) == set(states)
        assert set(refs) == {(x, y) for x, y in product(states, repeat=2) if infer(ambient, x) == infer(ambient, y)}
        self.refs = refs
        self.terms = set(refs.values())
        self.triangles = {}
        for (x, y), edge in refs.items():
            assert infer(ambient, edge) == arr(infer(ambient, x), x, y)
            self.terms.update(modes(ambient, x, y, refs))
            for z in states:
                if (y, z) in refs:
                    term = comp2(ambient, self.r, edge, refs[y, z])
                    self.triangles[x, y, z] = term
                    self.terms.add(term)
        self.certificates = {}

    def reference(self, t):
        return self.refs[src(self.ctx, t), tgt(self.ctx, t)]

    def certificate(self, t, reverse):
        ref = self.reference(t)
        a, b = (ref, t) if reverse else (t, ref)
        return self.certificates[a, b]

    def verify(self, build):
        for op, reverse in product(sorted(self.terms), (False, True)):
            ref = self.reference(op)
            a, b = (ref, op) if reverse else (op, ref)
            if (a, b) not in self.certificates:
                witness = ident(self.ctx, a) if a == b else build(op, ref, reverse)
                assert infer(self.ctx, witness) == arr(infer(self.ctx, a), a, b)
                self.certificates[a, b] = witness

    def join(self, pieces):
        assert all(tgt(self.ctx, a) == src(self.ctx, b) for a, b in zip(pieces, pieces[1:]))
        steps = [t for t in pieces if src(self.ctx, t) != tgt(self.ctx, t)]
        return temporal(self.ctx, src(self.ctx, pieces[0]), steps)

    @cache
    def normalize(self, t, reverse=False):
        ctx, r = self.ctx, self.r
        ref = self.reference(t)
        if t == ref:
            return ident(ctx, t)
        _, p, ty, args = t
        if ps_dim(p) <= r:
            return self.certificate(t, reverse)
        variables = tuple(map(v, range(len(p))))
        a, b, strings = columns(p, ty, variables, r)
        # For each column fold the actual argument comparisons to a single
        # reference arrow. Keys are slot indices so repeated labels stay distinct.
        generic_words = {}
        proofs = {}
        for j, links in strings.items():
            line = [v(i) for i in links]
            generic_words[a.labels[j], b.labels[j]] = temporal(p, a.labels[j], line)
            values = [args[i] for i in links]
            prefix = values[0]
            c = self.normalize(prefix, reverse)
            for value in values[1:]:
                child = self.normalize(value, reverse)
                x, y, z = src(ctx, prefix), tgt(ctx, prefix), tgt(ctx, value)
                triangle = self.certificate(self.triangles[x, y, z], reverse)
                raw = comp2(ctx, r, prefix, value)
                expected = self.triangles[x, y, z]
                generic = (*raw[:3], tuple(map(v, range(len(raw[1])))))
                chart = Chart(raw[1], generic, raw[3])
                other = Chart(raw[1], generic, expected[3])
                first, last = (other, chart) if reverse else (chart, other)
                active = [i for i in maximal_vars(raw[1]) if first.labels[i] != last.labels[i]]
                pair = fill_chart(ctx, first, last, active,
                                  {(src(ctx, w), tgt(ctx, w)): w for w in (c, child)})
                c = self.join([triangle, pair] if reverse else [pair, triangle])
                prefix = raw
            proofs[j] = c
        active = tuple(strings)
        compressed = fill_chart(p, a, b, active, generic_words)
        generic = (*t[:3], variables)
        x, y = (compressed, generic) if reverse else (generic, compressed)
        initial = subst_tm(head(p, x, y), args)
        grouped = subst_tm(compressed, args)
        target = fill_chart(ctx, *columns(p, ty, args, r)[:2], active, self.refs)
        generic_writing = (*grouped[:3], tuple(map(v, range(len(grouped[1])))))
        first = Chart(grouped[1], generic_writing, grouped[3])
        last = Chart(target[1], generic_writing, target[3])
        if reverse:
            first, last = last, first
        moves = [j for j in maximal_vars(grouped[1]) if first.labels[j] != last.labels[j]]
        middle = fill_chart(ctx, first, last, moves, {(src(ctx, w), tgt(ctx, w)): w for w in proofs.values()})
        final = self.certificate(target, reverse)
        steps = [final, middle, initial] if reverse else [initial, middle, final]
        result = self.join(steps)
        assert infer(ctx, result)[2:] == ((ref, t) if reverse else (t, ref))
        return result


def check_unequal_columns(emitter):
    line = tree_ctx(disc_tree(1))
    f = v(2)
    l, k = ident(line, f), head(line, f, f)
    q, back = head(line, l, k), head(line, k, l)
    ctx = tree_ctx(string_tree(0, [1, 1]))
    arity = tree_ctx(string_tree(2, [3, 3]) + string_tree(2, [3, 3, 3]))
    args = []
    for j, items in zip(maximal_vars(ctx), ((q, back), (q, back, q)), strict=True):
        sigma = sub_from(line, ctx, {2: v(j)})
        args.extend(subst_tm(x, sigma) for x in items)
    word = subst_tm(ucomp(arity), sub_from(arity, ctx, dict(zip(maximal_vars(arity), args, strict=True))))
    states = terms_of_rank(ctx, (word,), 2)
    refs = {(s, t): common(ctx, s, t) for s, t in product(states, repeat=2) if infer(ctx, s) == infer(ctx, t)}
    basis = BoundaryBasis(ctx, states, refs)
    basis.verify(lambda op, ref, reverse: common(ctx, ref, op) if reverse else common(ctx, op, ref))
    ref = basis.reference(word)
    for reverse in (False, True):
        a, b = (ref, word) if reverse else (word, ref)
        proof = basis.normalize(word, reverse)
        assert infer(ctx, proof)[2:] == (a, b)
        if emitter:
            label = 'twoColumnsBack' if reverse else 'twoColumns'
            emitter.check_type(label, ctx, proof, arr(infer(ctx, a), a, b))
    print('Normalized adjacent two-link and three-link columns at distinct exterior poles in both directions.')


def check_globe(rank, emitter):
    ctx, u, w, _, _ = example(rank)
    states = terms_of_rank(ctx, (u, w), rank-1)
    line = tree_ctx(disc_tree(1))
    z = v(len(ctx)-1)
    # Identify whiskered states by their changing maximal argument.
    inside = {}
    for t in states:
        if t[0] == 'coh' and z in t[3]:
            j, = [i for i in maximal_vars(t[1]) if tdim(t[1][i])+1 == rank-1]
            inside[t] = t[3][j]
    local = tuple(inside.values())
    assert len(local) == 2 and set(states) == set(local) | set(inside)
    refs = {(s, t): ident(line, s) if s == t else head(line, s, t) for s, t in product(local, repeat=2)}
    refs.update({(s, t): comp2(ctx, 1, refs[a, b], z) for s, a in inside.items() for t, b in inside.items()})
    basis = BoundaryBasis(ctx, states, refs)

    def build(op, ref, reverse):
        a, b = (ref, op) if reverse else (op, ref)
        if src(ctx, op) in local:
            return head(line, a, b)
        direct = common(ctx, a, b)
        if direct is not None:
            return direct
        x, y = (inside[t] for t in infer(ctx, op)[2:])
        inner_ref = refs[x, y]
        for m in sorted(basis.terms):
            if infer(ctx, m) != infer(ctx, inner_ref):
                continue
            middle = comp2(ctx, 1, m, z)
            step = common(ctx, middle, op) if reverse else common(ctx, op, middle)
            if step is None:
                continue
            i, = [i for i in maximal_vars(middle[1]) if tdim(middle[1][i])+1 == rank]
            h = head(line, inner_ref, m) if reverse else head(line, m, inner_ref)
            whiskered = at(ctx, ref if reverse else middle, (i,), h)
            return basis.join([whiskered, step] if reverse else [step, whiskered])
        raise AssertionError('missing inner boundary mode')

    basis.verify(build)
    if emitter:
        for i, ((a, b), witness) in enumerate(basis.certificates.items()):
            emitter.check_type(f'basis{i}', ctx, witness, arr(infer(ctx, a), a, b))
    # Test a held-out long column, composed of nonidentical loops. Its terms
    # were not used for the table of modes or any of its certificates.
    s, t = infer(ctx, w)[2:]
    assert s == t
    length = 5
    p = tree_ctx(string_tree(rank-1, [rank]*length))
    sigma = sub_from(p, ctx, dict(zip(maximal_vars(p), [w, u, w, u, w], strict=True)))
    word = subst_tm(ucomp(p), sigma)
    assert word not in basis.terms
    witness = basis.join([basis.normalize(word), basis.normalize(u, True)])
    assert infer(ctx, witness) == arr(infer(ctx, word), word, u)
    if emitter:
        emitter.check_type('longColumn', ctx, witness, arr(infer(ctx, word), word, u))
    print(f'Rank {rank}: {len(basis.terms)} reference, mode and triangle terms checked both ways '
          f'on four poles; normalized a new {length}-link column.')
    return ctx, u, w, basis


def check_wedge(rank, width, seed, u, w, basis, emitter, check_single):
    from relative_coherence_chart_joins import composite_state
    from relative_coherence_nested_charts import anchor_comparison, promoted_anchors
    f = src(seed, u)
    local = basis.join([basis.normalize(u), basis.normalize(w, True)])
    ctx = (STAR,)
    right_endpoint = v(0)
    proofs = []
    for _ in range(width):
        labels = [right_endpoint]
        for ty in seed[1:]:
            labels.append(v(len(ctx)))
            ctx += (subst_ty(ty, labels),)
        proofs.append(subst_tm(local, labels))
        right_endpoint = labels[1]

    lower = tree_ctx(string_tree(0, [rank-1]*width))
    upper = tree_ctx(string_tree(0, [rank]*width))
    generic_states = list(map(v, maximal_vars(lower)))
    writing = ucomp(upper)
    initial = ident(lower, ucomp(lower))
    inside = composite_state(lower, upper, [ident(lower, t) for t in generic_states])
    actual_states = [src(ctx, src(ctx, p)) for p in proofs]
    assert f == actual_states[0]
    sigma = sub_from(lower, ctx, dict(zip(maximal_vars(lower), actual_states, strict=True)))
    first = subst_tm(head(lower, initial, inside), sigma)

    def view(side):
        labels = sub_from(upper, ctx, dict(zip(maximal_vars(upper), [side(ctx, p) for p in proofs], strict=True)))
        return Chart(upper, writing, labels)

    a, b = view(src), view(tgt)
    second = fill_chart(ctx, a, b, maximal_vars(upper), {infer(ctx, p)[2:]: p for p in proofs})
    answer = comp2(ctx, rank, first, second)
    left = ident(ctx, composite_state(ctx, lower, actual_states))
    right = subst_tm(writing, b.labels)
    assert infer(ctx, answer) == arr(infer(ctx, left), left, right)
    if emitter:
        emitter.check_type('productOfLoops', ctx, answer, arr(infer(ctx, left), left, right))
    if check_single:
        extra = promoted_anchors(ctx, left, right)
        joined = anchor_comparison(ctx, left, right, extra) is not None
        if (rank, width) == (4, 2):
            assert not joined
        status = 'joined' if joined else 'separate'
        print(f'Single-slot closure: {status} with {len(extra)} computed endpoint anchors.')
    print(f'Rank {rank}: checked the comparison across {width} factors.')


if __name__ == '__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('--rank', type=int, default=4)
    cli.add_argument('--agda', type=Path)
    cli.add_argument('--width', type=int, default=2)
    cli.add_argument('--check-single', action='store_true')
    opt = cli.parse_args()
    if opt.rank < 4:
        cli.error('rank must be at least four')
    out = Emitter() if opt.agda else None
    if opt.width < 2:
        cli.error('width must be at least two')
    check_unequal_columns(out)
    seed, u, w, basis = check_globe(opt.rank, out)
    check_wedge(opt.rank, opt.width, seed, u, w, basis, out, opt.check_single)
    if out:
        opt.agda.write_text(out.module(opt.agda.stem, 'Normalization from finite boundary comparisons.'))
