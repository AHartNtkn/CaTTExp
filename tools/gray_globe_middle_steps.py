"""Compare the two growth orders on the four shared (2,3) steps in the three-by-four globe tensor."""
import argparse
from collections import Counter
from functools import cache
from pathlib import Path

from canonical_gray_two_discs import tableau_interpreter
from catt import STAR, arr, check_ctx, comp2, disc_tree, infer, src, tgt, tree_ctx, v
from emit_agda import Emitter
from gray_globe_attachments import ordered_factors
from gray_globe_comparison import atom, face
from gray_globe_corner_prisms import fold
from gray_globe_factorizations import profile
from gray_globe_natural_exchanges import top_sites, word
from gray_globe_pure_extension import raise_argument
from gray_globe_section import EMPTY_ROW, cells
from gray_globe_strip_squares import chart_lift, lift_on
from gray_path_wedge import compose


@cache
def chart_tree(shape, depth=0):
    if isinstance(shape, int):
        return disc_tree(shape-depth)
    cut, *parts = shape
    if depth < cut:
        return (chart_tree(shape, depth+1),)
    assert depth == cut
    return tuple(child for part in parts for child in chart_tree(part, depth))


def pair(a, b, first):
    return (a, b) if first else (b, a)


def split(c, site, cut):
    return ordered_factors(c, cut, {q: int(q == site) for q in profile(c) if sum(q) > cut})


class Growth:
    def __init__(self):
        self.ctx = ()
        self.values = []

    def parameter(self, value, ty):
        term = v(len(self.ctx))
        self.ctx += (ty,)
        self.values.append(value)
        return term

    @cache
    def common(self, c):
        d = len(c)-1
        if d:
            s, t = (self.rep(face(c, side), 'inner') for side in (0, 1))
            ty = arr(infer(self.ctx, s), s, t)
        else:
            ty = STAR
        return self.parameter(c, ty)

    @cache
    def rep(self, c, order):
        d = len(c)-1
        sites = profile(c)
        rules = [((3, 1), 3), ((3, 0), 2), ((0, 4), 3)]
        if order == 'outer':
            rules = [rules[2], *rules[:2]]
        for site, cut in rules:
            if d <= cut or site not in sites or (site == (0, 4) and (1, 4) in sites):
                continue
            if top_sites(c) == (site,):
                if site == (0, 4) and (3, 0) in sites and order == 'outer':
                    parts = split(c, (3, 0), 2)
                    move, = [p for p in parts if len(p) == 5]
                    y = self.rep(move, order)
                    base = self.rep(face(c, 0), order)
                    term = raise_argument(self.ctx, base, src(self.ctx, y), y)
                else:
                    term = self.common(c)
            else:
                parts = split(c, site, cut)
                assert len(parts) == 2
                args = [self.rep(p, order) for p in parts]
                term = comp2(self.ctx, cut, *args)
            break
        else:
            if d == 5 and len(top_sites(c)) > 1:
                args = [self.rep(p, order) for p in word(c)]
                term = fold(self.ctx, 4, args)
            else:
                term = self.common(c)
        if d:
            assert infer(self.ctx, term)[2:] == tuple(self.rep(face(c, s), order) for s in (0, 1))
        return term

    def comparison(self, full, reduced, args, old, new, moving):
        """A square on a globular arity and the two actual lower face comparisons."""
        corners = []
        for boundary in (src, tgt):
            faces = [boundary(self.ctx, t) if t == moving else t for t in args]
            corners.append(lift_on(self.ctx, tree_ctx(chart_tree(reduced)), faces,
                                   boundary(self.ctx, old), boundary(self.ctx, new)))
        start = comp2(self.ctx, 4, old, corners[1])
        end = comp2(self.ctx, 4, corners[0], new)
        proof = lift_on(self.ctx, tree_ctx(chart_tree(full)), args, start, end)
        return (old, new, *corners, proof)

    def whisk_square(self, square, fixed, first):
        old, new, lo, hi, proof = square
        def whisk(t):
            return comp2(self.ctx, 3, *pair(t, fixed, first))
        def distribute(a, b, reverse):
            separate = comp2(self.ctx, 4, whisk(a), whisk(b))
            together = whisk(comp2(self.ctx, 4, a, b))
            slots = (a, b, fixed) if first else (fixed, a, b)
            shape = (3, *pair((4, 5, 5), 4, first))
            return lift_on(self.ctx, tree_ctx(chart_tree(shape)), slots, *pair(together, separate, reverse))
        step = fold(self.ctx, 5, [distribute(old, hi, False), whisk(proof), distribute(lo, new, True)])
        return (whisk(old), whisk(new), whisk(lo), whisk(hi), step)

    def short(self, w):
        """Distribute the two stationary whiskers over each native five-word."""
        mid = self.rep(w, 'inner')
        outer = split(w, (3, 1), 3)
        core, = [c for c in outer if len(c) == 7]
        pure = split(core, (3, 0), 2)
        g, = [c for c in pure if len(c) == 7]
        assert g == atom(w[-1][0][0])
        ends, changes = [], []
        for side, op in enumerate((src, tgt)):
            z = face(w, side)
            args = [self.rep(s, 'inner') for s in word(z)]
            ends.append(fold(self.ctx, 4, args))
            def chart(c):
                if c == g:
                    letters = word(face(g, side))
                    return (4, 5, 5), [self.rep(l, 'inner') for l in letters]
                return len(c)-1, [self.rep(c, 'inner')]
            def join(cut, parts):
                return (cut, *(sh for sh, _ in parts)), [t for _, ts in parts for t in ts]
            inner = join(2, [chart(c) for c in pure])
            # At cut three the attachment is to the whole cut-two product.
            # Distribute outside first on its two-step face. The inner
            # distribution itself lives on a cut-two whiskered five-string.
            pc = [self.rep(q, 'inner') for q in word(face(core, side))]
            lifted = lift_on(self.ctx, tree_ctx(chart_tree(inner[0])), inner[1],
                             *pair(op(self.ctx, self.rep(core, 'inner')), fold(self.ctx, 4, pc), bool(side)))
            fixed, = [self.rep(c, 'inner') for c in outer if c != core]
            wh = lambda t: comp2(self.ctx, 3, *pair(t, fixed, outer[0] == core))
            assert [wh(t) for t in pc] == args
            string = (3, *pair((4, 5, 5), 4, outer[0] == core))
            slots = [*pc, fixed] if outer[0] == core else [fixed, *pc]
            collect = lift_on(self.ctx, tree_ctx(chart_tree(string)), slots,
                              *pair(wh(fold(self.ctx, 4, pc)), ends[-1], bool(side)))
            changes.append([wh(lifted), collect] if side else [collect, wh(lifted)])
        proof = fold(self.ctx, 5, changes[0] + [mid] + changes[1])
        assert infer(self.ctx, proof)[2:] == tuple(ends)
        return proof

    def middle(self, w):
        u, vterm = (self.rep(w, row) for row in ('inner', 'outer'))
        uy, ve = split(w, (3, 1), 3), split(w, (0, 4), 3)
        ucore, = [q for q in uy if len(q) == 6]
        vcore, = [q for q in ve if len(q) == 6]
        pure = split(ucore, (3, 0), 2)
        old, = [q for q in pure if len(q) == 6]
        x, = [q for q in pure if len(q) == 4]
        inside = split(old, (0, 4), 3)
        g, = [q for q in inside if len(q) == 6]
        assert g == atom(w[-1][0][0])
        inner_first = pure[0] == old
        distributed = []
        for c in inside:
            promoted = x + (EMPTY_ROW,)*(len(c)-len(x))
            distributed.append(compose(*pair(c, promoted, inner_first), 2))
        raw = self.rep(ucore, 'inner')
        operands = [self.rep(c, 'outer') for c in distributed]
        spread = comp2(self.ctx, 3, *operands)
        slots = [self.rep(c, 'inner') for c in inside]
        fixed_x = self.rep(x, 'inner')
        args = [*slots, fixed_x] if inner_first else [fixed_x, *slots]
        def layout(h):
            return (2, *pair((3, *(h if c == g else 4 for c in inside)), 3, inner_first))
        stage = self.comparison(layout(5), layout(4), args, raw, spread, self.rep(g, 'inner'))
        e, = [q for q in uy if len(q) == 5]
        first = uy[0] == ucore
        squares = [self.whisk_square(stage, self.rep(e, 'inner'), first)]
        assert squares[0][0] == u
        a = [*distributed, e] if first else [e, *distributed]
        vb = split(vcore, (3, 1), 3)
        y, = [q for q in ve if len(q) == 5]
        b = [*vb, y] if ve[0] == vcore else [y, *vb]
        centre, = [c for c in a if len(c) == 6]
        assert centre in b
        moving = self.rep(centre, 'outer')
        def associate(seq, left, right):
            heights = [len(c)-1 for c in seq]
            return self.comparison((3, *heights), (3, 4, 4, 4),
                                   [self.rep(c, 'outer') for c in seq], left, right, moving)

        if a == b:
            squares.append(associate(a, squares[-1][1], vterm))
        else:
            central_first = a[0] == centre
            assert (a[0] == b[0] == centre) or (a[-1] == b[-1] == centre)
            def grouped(seq):
                left, right = [c for c in seq if c != centre]
                term = comp2(self.ctx, 3, self.rep(left, 'outer'), self.rep(right, 'outer'))
                return compose(left, right, 3), term
            p, pterm = grouped(a)
            q, qterm = grouped(b)
            assert p == q and set(top_sites(p)) == {(0, 4), (3, 1)}
            # Supplied by depth-one naturality of the (3,1) elementary term.
            k = self.parameter(p+(EMPTY_ROW,), arr(infer(self.ctx, pterm), pterm, qterm))
            def product(c, t):
                return comp2(self.ctx, 3, *pair(c, t, central_first))
            middle_a, middle_b = product(moving, pterm), product(moving, qterm)
            squares.append(associate(a, squares[-1][1], middle_a))
            lo, hi = [product(op(self.ctx, moving), k) for op in (src, tgt)]
            square = chart_lift(self.ctx, pair(moving, k, central_first), 3,
                                comp2(self.ctx, 4, middle_a, hi), comp2(self.ctx, 4, lo, middle_b))
            squares.append((middle_a, middle_b, lo, hi, square))
            squares.append(associate(b, middle_b, vterm))

        # Paste the individual squares. All seam changes have their actual four-ends.
        starts = [s[2] for s in squares]
        ends = [s[3] for s in squares]
        vert = lambda a, b: comp2(self.ctx, 4, a, b)
        current = vert(u, fold(self.ctx, 4, ends))
        initial = current
        proof = []
        def reassociate(target, args):
            nonlocal current
            if current != target:
                proof.append(chart_lift(self.ctx, args, 4, current, target))
                current = target
        for i, (left, right, lo, hi, sq) in enumerate(squares):
            assert infer(self.ctx, sq)[2:] == (vert(left, hi), vert(lo, right))
            step = sq
            for before in reversed(starts[:i]):
                step = vert(before, step)
            for after in ends[i+1:]:
                step = vert(step, after)
            reassociate(src(self.ctx, step), [*starts[:i], left, hi, *ends[i+1:]])
            proof.append(step)
            current = tgt(self.ctx, step)
        final = vert(fold(self.ctx, 4, starts), vterm)
        reassociate(final, [*starts, vterm])
        result = fold(self.ctx, 5, proof)
        assert infer(self.ctx, result)[2:] == (initial, final)
        return result, a != b


def check(emitter):
    domain = cells((3, 4)) - {()}
    short = sorted(c for c in domain if top_sites(c) == ((2, 4),) and
                   (3, 1) in profile(c) and (3, 2) not in profile(c))
    middle = sorted(c for c in domain if top_sites(c) == ((2, 3),) and
                    {(0, 4), (3, 1)} <= profile(c))
    corners = {face(c, s) for c in middle for s in (0, 1)}
    assert len(short) == 2 and len(middle) == 4 and len(corners) == 8
    assert corners == {c for c in domain if len(c) == 5 and len(top_sites(c)) == 4}
    assert set(middle) == {p for w in short for s in (0, 1) for p in word(face(w, s))
                           if top_sites(p) == ((2, 3),)}
    counts = Counter()
    for tag, inputs in [('short', short), ('middle', middle)]:
        for i, c in enumerate(inputs):
            model = Growth()
            if tag == 'short':
                term, strict = model.short(c), c
            else:
                term, fork = model.middle(c)
                counts['fork' if fork else 'chain'] += 1
                strict = c + (EMPTY_ROW,)
            check_ctx(model.ctx)
            value = tableau_interpreter(model.ctx, model.values.__getitem__)
            assert value(term) == strict
            if emitter:
                emitter.check_type(tag+'-'+str(i), model.ctx, term, infer(model.ctx, term))
    assert counts == {'chain': 2, 'fork': 2}
    print('Two (2,4) lifts in left-last growth; four middle-step squares in one right-first native convention.')
    print('Eight distinct four-corners, two chains, two forks. All six terms checked at their full strict tableaux.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    check(emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Middle-step comparisons and short native lifts.'))
