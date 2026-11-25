"""Find a single ordinary CaTT head at written faces with a finite alphabet of top labels."""

import argparse
from collections import deque
from functools import cache
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, TypeError_, arr, chain_tree, check_ctx, coh_between, comp2, disc_tree,
                  fv_tm, fv_ty, infer, maximal_vars, mk_coh, sub_from, subst_tm,
                  tdim_tm, tgt, tree_ctx, ucomp, v)
from relative_coherence_hidden_seam import identity
from semistrict_surface_equal_rank import suspend
from semistrict_surface_exact_boundary import accepted, run
from semistrict_surface_grid_tracks import temporal
from semistrict_surface_insertion_cut import Assertions
from semistrict_surface_rank_cut import RankCut


@cache
def trees_with_leaves(depth, leaves):
    if leaves == 1 and depth == 0:
        return ((),)
    if depth == 0:
        return ()

    @cache
    def forests(budget):
        if budget == 0:
            return ((),)
        return tuple((first, *rest) for used in range(1, budget + 1)
                     for first in trees_with_leaves(depth - 1, used)
                     for rest in forests(budget - used))

    return (((),) if leaves == 1 else ()) + forests(leaves)


@cache
def syntax_leaves(term):
    return 1 if term[0] == 'v' else sum(map(syntax_leaves, term[3]))


@cache
def subterms(term):
    if term[0] == 'v':
        return frozenset([term])
    return frozenset([term]).union(*(subterms(label) for label in term[3]))


def skeletons(rank, source, target):
    if source[0] == 'v' or target[0] == 'v':
        yield disc_tree(rank)
        return
    limit = min(map(syntax_leaves, (source, target)))
    for leaves in range(1, limit + 1):
        yield from trees_with_leaves(rank, leaves)


def inverse_substitution(shape, sigma):
    @cache
    def lift(actual):
        choices = {v(i) for i, x in enumerate(sigma) if x == actual}
        if actual[0] == 'coh':
            _, arity, ty, args = actual
            mx = maximal_vars(arity)
            for group in product(*(lift(args[i]) for i in mx)):
                try:
                    sub = sub_from(arity, shape, dict(zip(mx, group)))
                    lifted = mk_coh(arity, ty, sub)
                    infer(shape, lifted)
                except TypeError_:
                    continue
                if subst_tm(lifted, sigma) == actual:
                    choices.add(lifted)
        return choices

    return lift


def charts(ctx, term, shape):
    """All full-support templates on shape specializing literally to term."""
    tips = maximal_vars(shape)
    parts = subterms(term)
    domains = [[x for x in parts if tdim_tm(ctx, x) == tdim_tm(shape, v(i))]
               for i in tips]
    for labels in product(*domains):
        try:
            sigma = sub_from(shape, ctx, dict(zip(tips, labels)))
        except TypeError_:
            continue

        for template in inverse_substitution(shape, sigma)(term):
            if len(fv_tm(template) | fv_ty(infer(shape, template))) == len(shape):
                yield template, sigma


def tip_paths(tree):
    """Leaf addresses and the corresponding positive-dimensional cell or root."""
    cursor = iter(range(1, len(tree_ctx(tree))))

    def visit(node, path, cell):
        if not node:
            yield path, cell
        for j, child in enumerate(node):
            next(cursor)
            yield from visit(child, (*path, j), next(cursor))

    return tuple(visit(tree, (), 0))


def routes(segments, edges, counts):
    """Recover one tuple of directed walks, optionally with joint exact counts."""
    if not segments:
        return None if counts and any(counts) else []
    initial = (0, segments[0][0], counts)
    previous = {initial: None}
    queue = deque([initial])

    def enqueue(state, parent, edge):
        if state not in previous:
            previous[state] = (parent, edge)
            queue.append(state)

    while queue:
        state = queue.popleft()
        i, current, budget = state
        if current == segments[i][1]:
            if i + 1 < len(segments):
                enqueue((i + 1, segments[i + 1][0], budget), state, None)
            elif budget is None or not any(budget):
                walks = [[] for _ in segments]
                while previous[state] is not None:
                    state, edge = previous[state]
                    if edge is not None:
                        walks[state[0]].append(edge)
                return [list(reversed(walk)) for walk in walks]
        for j, (start, end) in enumerate(edges):
            if current != start or (budget is not None and budget[j] == 0):
                continue
            rest = None if budget is None else budget[:j] + (budget[j] - 1,) + budget[j + 1:]
            enqueue((i, end, rest), state, j)
    return None


def assemble(ctx, tree, p, q, sigma, paths, alphabet):
    """Grow the chosen walks at their leaves and form the actual typed head."""
    shape = tree_ctx(tree)
    labels = []
    first, last = {}, {}
    cursor = 1

    def grow(node, path, cell):
        nonlocal cursor
        if not node:
            slot, walk = paths[path]
            first[slot] = v(cell)
            end = cell
            for edge in walk:
                end = cursor
                cursor += 2
                labels.append(alphabet[edge])
            last[slot] = v(end)
            if not walk:
                labels.append(sigma[slot])
            return chain_tree(len(walk))
        children = []
        for j, child in enumerate(node):
            child_cell = cursor + 1
            cursor += 2
            children.append(grow(child, (*path, j), child_cell))
        return tuple(children)

    arity = tree_ctx(grow(tree, (), 0))
    lo = subst_tm(p, sub_from(shape, arity, first))
    hi = subst_tm(q, sub_from(shape, arity, last))
    values = sub_from(arity, ctx, dict(zip(maximal_vars(arity), labels, strict=True)))
    return mk_coh(arity, arr(infer(arity, lo), lo, hi), values)


def flat_head(ctx, source, target, alphabet=(), counts=None):
    """Return a raw witness or None. Counts count slots, including repeated labels."""
    ty = infer(ctx, source)
    if infer(ctx, target) != ty:
        raise ValueError('Expected literally parallel faces')
    rank = tdim_tm(ctx, source)
    edges = []
    for label in alphabet:
        if tdim_tm(ctx, label) != rank + 1:
            raise ValueError('Top label has the wrong dimension')
        edges.append(infer(ctx, label)[2:])
    if counts is not None:
        counts = tuple(counts)
        if len(counts) != len(edges) or any(type(n) is not int or n < 0 for n in counts):
            raise ValueError('Expected a nonnegative integer per top label')
    for tree in skeletons(rank, source, target):
        shape = tree_ctx(tree)
        tips = tip_paths(tree)
        lower = [i for i in range(len(shape)) if tdim_tm(shape, v(i)) < rank]
        active = [(path, i) for path, i in tips if len(path) == rank]
        targets = list(charts(ctx, target, shape))
        for p, sigma in charts(ctx, source, shape):
            for q, tau in targets:
                if infer(shape, p) != infer(shape, q) or any(sigma[i] != tau[i] for i in lower):
                    continue
                walks = routes([(sigma[i], tau[i]) for _, i in active], edges, counts)
                if walks is None:
                    continue
                paths = {path: (i, ()) for path, i in tips}
                paths.update({path: (i, w) for (path, i), w in zip(active, walks)})
                witness = assemble(ctx, tree, p, q, sigma, paths, alphabet)
                assert infer(ctx, witness) == arr(ty, source, target)
                return witness
    return None


def word_checks():
    edge_ty = arr(STAR, v(0), v(0))
    a, b = v(1), v(2)
    ctx = (STAR, edge_ty, edge_ty, arr(edge_ty, a, b), arr(edge_ty, b, a))
    labels = (v(3), v(4))
    words = {(x,): x for x in (a, b)}
    words.update({(x, y): temporal(ctx, x, y) for x, y in product((a, b), repeat=2)})
    checked = 0
    for (left, s), (right, t) in product(words.items(), repeat=2):
        forward = sum(x == a and y == b for x, y in zip(left, right))
        back = sum(x == b and y == a for x, y in zip(left, right))
        for g, h in product(range(3), repeat=2):
            expected = len(left) == len(right) and g - forward == h - back >= 0
            assert (flat_head(ctx, s, t, labels, (g, h)) is not None) == expected
            checked += 1
    return checked


def check_weak(checker, ctx, term, expected):
    writer = Assertions()

    def show(ty):
        return '*' if ty == STAR else ' -> '.join(map(writer.term, ty[2:]))

    telescope = ' '.join(f'(x{i} : {show(ty)})' for i, ty in enumerate(ctx))
    command = f'def fitted {telescope} : {show(expected)} = {writer.term(term)}'
    name = 'FlatHeads.catt'
    (checker.directory / name).write_text('\n'.join([*writer.commands, command, '']))
    accepted(run(checker.binary, checker.directory, name), name, ['fitted'])


def seam(rank, width, checker):
    tree = suspend(chain_tree(width), rank - 2)
    base = tree_ctx(tree)
    tips = [v(i) for i in maximal_vars(base)]
    total = ucomp(base)
    loop = arr(infer(base, total), total, total)
    kappa = coh_between(base, tree, tips, total, total)
    unit = identity(base, total)
    z = v(len(base))
    g = v(len(base) + 1)
    ctx = base + (loop, arr(loop, z, z))
    check_ctx(ctx)
    hidden = temporal(ctx, z, kappa)
    visible = temporal(ctx, z, unit)
    for start, end in ((hidden, z), (z, hidden)):
        assert flat_head(ctx, start, end, [g]) is None
    for start, end in ((visible, z), (z, visible)):
        for count in (0, 1, 3):
            assert flat_head(ctx, start, end, [g], [count]) is not None
    results = []
    for rev in (False, True):
        faces = (unit, kappa) if rev else (kappa, unit)
        middle = coh_between(base, tree, tips, *faces)
        whiskered = comp2(ctx, rank - 1, z, middle)
        unitor = flat_head(ctx, z, visible) if rev else flat_head(ctx, visible, z)
        term = temporal(ctx, unitor, whiskered) if rev else temporal(ctx, whiskered, unitor)
        witness = temporal(ctx, g, term) if rev else temporal(ctx, term, g)
        ends = (z, hidden) if rev else (hidden, z)
        assert infer(ctx, witness) == arr(loop, *ends)
        if checker:
            check_weak(checker, ctx, witness, arr(loop, *ends))
            assert checker.published_equal(ctx, witness, g)
        results.append(witness)
    return ctx, tuple(results)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path)
    args = parser.parse_args()
    print(f'{word_checks()} exact occurrence queries match the alternating-walk formula')
    with TemporaryDirectory() as scratch:
        checker = RankCut(6, args.checker.resolve(), Path(scratch)) if args.checker else None
        for rank, width in ((2, 2), (3, 3), (5, 2), (5, 4)):
            seam(rank, width, checker)
            print(f'Degree {rank + 1}, width {width}: both flat exclusions and both nested witnesses')
        if checker:
            print('Checker typed eight raw witnesses and identified each with the named loop under insertion')
