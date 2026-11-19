"""Construct the local 5-comparisons for exchanging exterior globe-pair events."""
import argparse
from collections import Counter
from functools import cache
from itertools import permutations
from pathlib import Path

from canonical_gray_two_discs import strict_interpreter
from catt import (TypeError_, comp2, disc_tree, infer, maximal_vars, src, sub_from, subst_tm,
                  subst_ty, tgt, tree_ctx, v)
from emit_agda import Emitter
from gray_globe_attachments import ordered_factors
from gray_globe_comparison import atom, face, strict_cells
from gray_globe_factorizations import components, orders, profile, rank, truncate
from gray_globe_sector_terms import arrow, verify
from gray_globe_strip_gluing import chart_or_hole
from gray_globe_section import row_map
from gray_path_wedge import compose


def component_data(cell, cut):
    groups = components(profile(cell), cut)
    return groups, {p: i for i, group in enumerate(groups) for p in group}


def mixed_patches():
    """The moving 4-component and one incomparable stationary 3-component at cut two."""
    found = set()
    for cell in strict_cells((5, 5), 4):
        if len(cell[-1][0]) != 1:
            continue
        groups, owner = component_data(cell, 2)
        if len(groups) == 2 and not orders(cell, 2, owner):
            found.add(cell)
    return found


def double_patches():
    """Isolate every adjacent incomparable pair in every word of the 144 labelled endpoints."""
    endpoints = set()
    for cell in strict_cells((5, 5), 5):
        if not cell[-1][0] or chart_or_hole(cell, 2, 2) != (3, 2):
            continue
        for side in (0, 1):
            z = truncate(cell, 4, side)
            if chart_or_hole(z, 2, 2) == (2, 3):
                endpoints.add(z)
    patches = set()
    singletons = set()
    for z in endpoints:
        sites = {rank(g): rank(g)[0] for g in z[-1][0]}
        before = orders(z, 3, sites)
        for word in permutations(sites.values()):
            if any(word.index(a) > word.index(b) for a, b in before):
                continue
            pieces = ordered_factors(z, 3, {p: word.index(a) for p, a in sites.items()})
            singletons.update(pieces)
            for i, (a, b) in enumerate(zip(word, word[1:])):
                if a < b and (a, b) not in before:
                    patches.add(compose(pieces[i], pieces[i+1], 3))
    shapes = set()
    for w in singletons:
        sites = profile(w)
        maxima = tuple(max(p[axis] for p in sites) for axis in range(2))
        assert len(w[-1][0]) == 1 and {(0, 3), (1, 2), (2, 1), (3, 0)} <= sites
        shapes.add(row_map(w, 0, lambda g: tuple((r, 2) if r == m else (r, tag)
                                                for (r, tag), m in zip(g, maxima))))
    counts = Counter(rank(w[-1][0][0])[0] for w in shapes)
    print(f'{len(singletons)} single steps, {len(shapes)} face shapes by site {dict(sorted(counts.items()))}')
    return endpoints, patches


def arity(cut, heights):
    tree = tuple(disc_tree(h-cut-1) for h in heights)
    for _ in range(cut):
        tree = (tree,)
    return tree_ctx(tree)


def route(ctx, cut, heights, order):
    slots = tuple(map(v, maximal_vars(ctx)))
    base = cut+1
    done = set()
    steps = []
    for moving in order:
        args = list(slots)
        for i, height in enumerate(heights):
            if i == moving:
                continue
            endpoint = tgt if i in done else src
            for _ in range(height-base):
                args[i] = endpoint(ctx, args[i])
        term = args[0]
        for other in args[1:]:
            term = comp2(ctx, cut, term, other)
        steps.append(term)
        done.add(moving)
    return comp2(ctx, cut+1, *steps)


def coherence(ctx, source, target):
    return ('coh', ctx, arrow(ctx, source, target), tuple(map(v, range(len(ctx)))))


def chart_preimage(ctx, sigma):
    """Recover literal terms over a spatial chart from their substituted syntax."""
    variables = {term: v(i) for i, term in enumerate(sigma)}
    assert len(variables) == len(ctx)

    @cache
    def recover(term):
        if term in variables:
            return variables[term]
        if term[0] == 'v':
            return None
        _, arity, ty, args = term
        originals = tuple(recover(arg) for arg in args)
        if None in originals:
            return None
        result = ('coh', arity, ty, originals)
        try:
            infer(ctx, result)
        except TypeError_:
            return None
        return result

    return recover


@cache
def comparison(cut, heights):
    ctx = arity(cut, heights)
    active = tuple(i for i, h in enumerate(heights) if h > cut+1)
    assert len(active) == 2
    left = route(ctx, cut, heights, active)
    right = route(ctx, cut, heights, active[::-1])
    if cut == 1:
        # The source/target swaps use the two 3-faces of the 4-slot.
        reduced = tuple(min(h, 3) for h in heights)
        lower = arity(cut, reduced)
        exchange = coherence(lower, route(lower, cut, reduced, active), route(lower, cut, reduced, active[::-1]))
        ends = []
        for endpoint in (src, tgt):
            args = [endpoint(ctx, v(i)) if h == 4 else v(i) for i, h in zip(maximal_vars(ctx), heights)]
            ends.append(subst_tm(exchange, sub_from(lower, ctx, dict(zip(maximal_vars(lower), args)))))
        left = comp2(ctx, 3, left, ends[1])
        right = comp2(ctx, 3, ends[0], right)
    assert left != right
    fwd, rev = coherence(ctx, left, right), coherence(ctx, right, left)
    assert infer(ctx, fwd) == fwd[2] and infer(ctx, rev) == rev[2]
    return fwd, rev


def patch_type(w, cut):
    a = rank(w[-1][0][0])[0]
    if cut == 2:
        return a, rank(w[-1][0][1])[0]
    groups, owner = component_data(w, 2)
    moving = owner[rank(w[-1][0][0])]
    stationary, = groups[1-moving]
    return a, stationary[0]


def certificate(emitter, ctx):
    """Share Agda typing derivations for subterms common to several witnesses."""
    ambient = emitter.ctx(ctx)
    emitter.checks.extend([
        'open import CaTTExp.PastingCheck ∅ renaming (checkPs to certifyPs)',
        f'abstract\n  goodΓ : {ambient} ⊢ctx\n  goodΓ = from-just (checkCtx {ambient})\n',
    ])

    @cache
    def head(pasting, ty):
        p, a = emitter.ctx(pasting), emitter.ty(ty)
        name = f'head-{len(emitter.checks)}'
        wf = f'(from-just (checkCtx {p}))'
        emitter.checks.append(
            f'abstract\n  {name} : ∀ {{Γ σ}} → Γ ⊢sub σ ∶ {p} → Γ ⊢tm coh {p} {a} σ ∶ {a} [ σ ]ty\n'
            f'  {name} = coh-wf (from-just (certifyPs {p})) {wf} (from-just (checkTy {p} {wf} {a})) tt\n')
        return name

    @cache
    def derivation(term):
        if term[0] == 'v':
            return '(var-wf goodΓ refl)'
        _, pasting, ty, sigma = term
        sub_proof = '(⟨⟩-wf goodΓ)'
        for arg in sigma:
            sub_proof = f'(,-wf {sub_proof} {derivation(arg)})'
        rule = head(pasting, ty)
        t, a, s = emitter.tm(term), emitter.ty(ty), emitter.sub(sigma)
        emitter.checks.append(
            f'abstract\n  ok-{t} : {ambient} ⊢tm {t} ∶ {a} [ {s} ]ty\n  ok-{t} = {rule} {sub_proof}\n')
        return f'ok-{t}'

    def check_type(label, term, wanted):
        proof = derivation(term)
        emitter.checks.append(
            f'{label} : {ambient} ⊢tm {emitter.tm(term)} ∶ {emitter.ty(wanted)}\n{label} = {proof}\n')

    return check_type


def check(emitter):
    endpoints, double = double_patches()
    mixed = mixed_patches()
    jobs = []
    needed = set()
    centers = set()
    for cut, patches in ((1, mixed), (2, double)):
        counts = Counter()
        for w in sorted(patches):
            _, owner = component_data(w, cut)
            pieces = ordered_factors(w, cut, owner)
            kind = patch_type(w, cut)
            counts[kind] += 1
            jobs.append((cut, kind, w, pieces))
            for p in pieces:
                if (2, 2) in profile(p):
                    g, = p[-1][0]
                    assert p == atom(g) and rank(g) == (2, 2)
                    centers.add(g)
                    needed.update(face(p, side) for side in (0, 1))
                else:
                    needed.add(p)
        print(f'Cut {cut}: {len(patches)} local cells, {dict(sorted(counts.items()))}', flush=True)
    print(f'{len(endpoints)} labelled endpoints', flush=True)

    ctx, names, chosen = verify(5, 5, None, required=needed)
    for g in sorted(centers):
        p = atom(g)
        ty = arrow(ctx, *(chosen[face(p, side)] for side in (0, 1)))
        names[g] = chosen[p] = v(len(ctx))
        ctx += (ty,)
    evaluate = strict_interpreter(ctx, tuple(names))
    check_type = certificate(emitter, ctx) if emitter else None
    certified = set()
    for cut, kind, w, pieces in jobs:
        heights = tuple(len(p)-1 for p in pieces)
        fwd, rev = comparison(cut, heights)
        ar = fwd[1]
        args = [chosen[p] for p in pieces]
        assert all(evaluate(t) == p for p, t in zip(pieces, args))
        sigma = sub_from(ar, ctx, dict(zip(maximal_vars(ar), args)))
        recover = chart_preimage(ar, sigma)
        for proof in (fwd, rev):
            actual = subst_tm(proof, sigma)
            wanted = subst_ty(proof[2], sigma)
            assert infer(ctx, actual) == wanted and wanted[2] != wanted[3]
            assert recover(actual) == proof
            assert tuple(map(recover, wanted[2:])) == proof[2][2:]
            assert evaluate(wanted[2]) == evaluate(wanted[3]) == w
            assert evaluate(actual) == w + (((), ()),)
            if check_type and (cut, kind) not in certified:
                check_type(f'cut-{cut}-sites-{kind[0]}-{kind[1]}', actual, wanted)
                certified.add((cut, kind))
    print(f'Checked both typed directions and all strict rows for {len(jobs)} swaps')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda else None
    check(emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Local exterior Gray actions.'))
