"""Compile inverse crossings into finitely many raw declarations on named scalars."""
import argparse
from functools import cache
from itertools import product
from pathlib import Path

from catt import STAR, arr, comp2, infer, maximal_vars, src, tgt, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_three_axis import fitted_exchange, scalar_context, specialize


def signed_spelling(names, signed):
    """Encode in positive crossings and one inverse generator per unordered pair."""
    names = list(names)
    out = []
    for letter in signed:
        i = abs(letter)-1
        a, b = names[i:i+2]
        if letter > 0:
            steps = ('cross',)
        elif a == b:
            steps = ('diagonal-inverse',)
        elif a < b:
            # Input AB. Inverse of the positive crossing BA -> AB.
            steps = ('loop-inverse', 'cross')
        else:
            steps = ('cross', 'loop-inverse')
        decoded = []
        for step in steps:
            u, v_ = names[i:i+2]
            out.append((i+1, u, v_, step))
            if step == 'loop-inverse':
                assert u < v_
                decoded.extend((-1, -1))
            else:
                assert step != 'diagonal-inverse' or u == v_
                names[i:i+2] = [v_, u]
                decoded.append(1 if step == 'cross' else -1)
        assert sum(decoded) == (1 if letter > 0 else -1)
        assert names[i:i+2] == [b, a]
    return tuple(names), out


def cover_trace(k):
    """Literal width-three rewrites proving 1 -> x^(2k-1)y."""
    if k < 1:
        raise ValueError('cover index must be positive')
    steps = [(0, '', 'xy')]
    for j in range(1, k):
        steps = ([(0, '', 'xX')] + [(i+1, a, b) for i, a, b in steps] +
                 [(2*j+1, '', 'xy'), (2*j, 'yxy', 'xyx'), (2*j+2, 'xX', '')])
    w = ''
    for i, a, b in steps:
        assert (a, b) in (('', 'xX'), ('xX', ''), ('', 'xy'), ('yxy', 'xyx'))
        assert w[i:i+len(a)] == a and i <= len(w)
        w = w[:i]+b+w[i+len(a):]
    assert w == 'x'*(2*k-1)+'y'
    return steps


class DerivationEmitter(Emitter):
    """Share kernel derivations for subterms repeated by dependent whiskerings."""

    def lemma(self, statement, proof):
        name = 'proof' + str(len(self.checks))
        self.checks.append(f'{name} : {statement}\n{name} = {proof}\n')
        return name

    @cache
    def well_formed(self, ctx):
        if not ctx:
            return 'ε-wf'
        prefix, ty = ctx[:-1], ctx[-1]
        prev = self.well_formed(prefix)
        if ty != STAR:
            reason = f'arr-wf {self.typed(prefix, ty[2])} {self.typed(prefix, ty[3])}'
        else:
            reason = f'⋆-wf {prev}'
        return self.lemma(f'{self.ctx(ctx)} ⊢ctx', f'▸-wf {prev} ({reason})')

    @cache
    def typed(self, ctx, tm):
        ambient = self.well_formed(ctx)
        if tm[0] == 'v':
            proof = f'var-wf {ambient} refl'
        else:
            _, arity, ty, args = tm
            generic = self.well_formed(arity)
            left, right = self.typed(arity, ty[2]), self.typed(arity, ty[3])
            sub = f'⟨⟩-wf {ambient}'
            for arg in args:
                sub = f',-wf ({sub}) {self.typed(ctx, arg)}'
            proof = (f'coh-wf (from-just (pastable {self.ctx(arity)})) {generic} '
                     f'(arr-wf {left} {right}) tt ({sub})')
        statement = f'{self.ctx(ctx)} ⊢tm {self.tm(tm)} ∶ {self.ty(infer(ctx, tm))}'
        return self.lemma(statement, proof)

    def check_type(self, label, ctx, term, expected):
        proof = self.typed(ctx, term)
        self.checks.append(f'{label} : {self.ctx(ctx)} ⊢tm {self.tm(term)} ∶ {self.ty(expected)}'
                           f'\n{label} = {proof}\n')


def typed_example():
    ctx = scalar_context(2)
    _, b = fitted_exchange(ctx, v(1), v(2))
    _, c = fitted_exchange(ctx, v(2), v(1))
    ab, ba = src(ctx, b), src(ctx, c)
    unit = identity(ctx, ab)
    bc = comp2(ctx, 2, b, c)
    ctx += (arr(infer(ctx, unit), unit, bc),)
    insertion = v(3)
    ctx += (infer(ctx, unit),)
    h = v(4)
    emitter = DerivationEmitter()
    emitter.check_type('inverse-monodromy', ctx, h, infer(ctx, unit))
    cancels = []
    for label, operands in [('bch', (b, c, h)), ('hbc', (h, b, c)), ('chb', (c, h, b))]:
        path = composite(ctx, 2, operands)
        empty = identity(ctx, src(ctx, path))
        for suffix, left, right in [('in', empty, path), ('out', path, empty)]:
            ty = arr(infer(ctx, path), left, right)
            ctx += (ty,)
            cell = v(len(ctx)-1)
            emitter.check_type(label+'-'+suffix, ctx, cell, ty)
            if label == 'chb':
                cancels.append(cell)

    def middle(g, c, move, h, b):
        return comp2(g, 2, c, comp2(g, 2, move, comp2(g, 2, h, b)))

    def tail(g, c, b, move):
        return comp2(g, 2, comp2(g, 2, c, b), move)

    def fit(operands, first, second):
        paste = tree_ctx(string_tree(2, [3]*len(operands)))
        vs = [v(i) for i in maximal_vars(paste)]
        return specialize(head(paste, first(paste, *vs), second(paste, *vs)), paste, ctx, operands)

    def triple(g, c, h, b):
        return composite(g, 2, (c, h, b))

    entry = fit((c,h,b), triple, lambda g,c,h,b: src(g, middle(
        g,c,identity(g,identity(g,tgt(g,c))),h,b)))
    seam = fit((c,b,c,h,b),
               lambda g,c,b,c2,h,b2: tgt(g, middle(g,c,identity(g,comp2(g,2,b,c2)),h,b2)),
               lambda g,c,b,c2,h,b2: src(g, tail(g,c,b,identity(g,triple(g,c2,h,b2)))))
    exit_move = fit((c,b), lambda g,c,b: tgt(g, tail(g,c,b,identity(g,identity(g,tgt(g,b))))),
                    lambda g,c,b: comp2(g,2,c,b))
    result = composite(ctx, 3, [cancels[0], entry, middle(ctx,c,insertion,h,b), seam,
                               tail(ctx,c,b,cancels[1]), exit_move])
    expected = arr(infer(ctx, identity(ctx, ba)), identity(ctx, ba), comp2(ctx, 2, c, b))
    assert infer(ctx, result) == expected
    emitter.check_type('old-opposite-order-filler', ctx, result, expected)
    return emitter


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    parser.add_argument('--cover', type=int)
    args = parser.parse_args()
    if args.cover:
        print(cover_trace(args.cover))
    else:
        traces = 0
        for names in product('ABC', repeat=3):
            for word in product((1, -1, 2, -2), repeat=4):
                end, _ = signed_spelling(names, word)
                positive_end, _ = signed_spelling(names, map(abs, word))
                assert end == positive_end
                traces += 1
        cover_steps = sum(len(cover_trace(k)) for k in range(1, 65))
        emitter = typed_example()
        if args.agda:
            module = emitter.module(args.agda.stem, 'Finite raw inverse completions on named scalars.')
            args.agda.write_text(module.replace('open import CaTTExp.Pure\n',
                                                'open import CaTTExp.Gray.Pure\n'
                                                'open import CaTTExp.Pure using (∅)\n'
                                                'open import CaTTExp.PastingCheck ∅ using () renaming (checkPs to pastable)\n'))
        print(f'{traces} named signed words, {cover_steps} literal cover steps, '
              'typed inverse declarations and a raw opposite-order filler')
