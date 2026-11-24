"""Compare the first fork of a tree with its ordinary strict cell tableaux."""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from pathlib import Path

from catt import arr, check_ctx, comp2, glue_tree, infer, src, tdim, tree_ctx, v
from emit_agda import Emitter
from rc_oracle import strict_image
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from relative_coherence_interval_generator import trees
from steiner import Complex, cdim, cells_upto, comp, ident, image_to_cell, intrinsic_rank, kface


def first_fork(tree):
    if sum(bool(child) for child in tree) >= 2:
        return 0
    depths = [d + 1 for child in tree if (d := first_fork(child)) is not None]
    return min(depths, default=None)


def first_active_match(cells, ranks, height):
    for cut in range(height - 1):
        active = [c for c in cells if ranks[c] >= cut + 2]
        sources = {kface(c, cut, '-') for c in active}
        if any(kface(c, cut, '+') in sources for c in active):
            return cut
    return None


def first_separated_pair(ctx):
    """Find the least cut by multi-source search in the graph of generator faces."""
    dimensions = [tdim(ty) + 1 for ty in ctx]
    for cut in range(max(dimensions, default=0) - 1):
        successors = defaultdict(list)
        starts, goals = set(), set()
        for ty, rank in zip(ctx, dimensions, strict=True):
            if rank == cut + 1:
                successors[ty[2][1]].append(ty[3][1])
            elif rank == cut + 2:
                goals.add(ty[1][2][1])
                starts.add(ty[1][3][1])
        seen = set(starts)
        pending = list(starts)
        while pending:
            pole = pending.pop()
            if pole in goals:
                return cut
            for target in successors[pole]:
                if target not in seen:
                    seen.add(target)
                    pending.append(target)
    return None


def check_structural_generation(table, cells, ranks, height):
    """Close under identities, temporal composition and single-disc whiskers."""
    generated = {table.atom(i) for i, d in enumerate(table.deg) if d <= height}
    frontier = generated.copy()
    while frontier:
        next_cells = {ident(c) for c in frontier if cdim(c) < height}
        for a in frontier:
            for b in generated:
                for cut in range(min(cdim(a), cdim(b))):
                    if min(ranks[a], ranks[b]) > cut + 1:
                        continue
                    for left, right in ((a, b), (b, a)):
                        value = comp(cut, left, right)
                        if value is not None:
                            next_cells.add(value)
        frontier = next_cells - generated
        generated.update(frontier)
    assert generated == {c for c in cells if cdim(c) <= height}
    return len(generated)


def serialize(a, b, cut):
    if min(intrinsic_rank(a), intrinsic_rank(b)) <= cut + 1:
        return comp(cut, a, b)
    first = comp(cut, a, kface(b, cut + 1, '-'))
    second = comp(cut, kface(a, cut + 1, '+'), b)
    return serialize(first, second, cut + 1)


def padded(line, term, count):
    for _ in range(count):
        term = identity(line, term)
    return term


def realized_horizontal(rank, emitter):
    line = tree_ctx(((), ()))
    f, g = v(2), v(4)
    f_pole, g_pole = (padded(line, t, rank - 2) for t in (f, g))
    ctx = line + (arr(infer(line, f_pole), f_pole, f_pole),
                  arr(infer(line, g_pole), g_pole, g_pole))
    a, b = v(len(line)), v(len(line) + 1)
    desired_arrow = comp2(line, 0, identity(line, src(line, f)), comp2(line, 0, f, g))
    desired = padded(line, desired_arrow, rank - 2)

    def fit(word):
        for cut in range(1, rank):
            wanted = padded(line, desired_arrow, cut - 1)
            # Move to the type of the two current cut-faces.
            ty = infer(ctx, word)
            for _ in range(rank - 1 - cut):
                ty = ty[1]
            left, right = ty[2:]
            if left != wanted:
                word = comp2(ctx, cut, head(line, wanted, left), word)
            if right != wanted:
                word = comp2(ctx, cut, word, head(line, right, wanted))
        assert infer(ctx, word) == arr(infer(line, desired), desired, desired)
        return word

    result = comp2(ctx, rank - 1, fit(comp2(ctx, 0, a, g)), fit(comp2(ctx, 0, f, b)))
    value = lambda term: image_to_cell(strict_image(ctx, term))
    assert value(result) == comp(0, value(a), value(b))
    emitter.check_type(f'compoundProduct{rank}', ctx, result, arr(infer(line, desired), desired, desired))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    shapes = {p for size in range(6) for p in trees(size)}
    shapes.add(glue_tree(4, 0, 4))
    # Deep forks and a fork with a stationary gap.
    fork = (((),), (), ((), ()))
    shapes.add(fork)
    for _ in range(3):
        fork = (fork,)
        shapes.add(fork)
    counts = Counter()
    checked = serialized = 0
    for tree in sorted(shapes):
        ctx = tree_ctx(tree)
        table = Complex(ctx)
        cells = cells_upto(table, range(len(table.deg)), table.n)
        ranks = {c: intrinsic_rank(c) for c in cells}
        depth = first_fork(tree)
        assert first_separated_pair(ctx) == depth, tree
        assert first_active_match(cells, ranks, table.n) == depth, tree
        height = table.n if depth is None else depth + 2
        checked += check_structural_generation(table, cells, ranks, height)
        proper = [c for c in cells if ranks[c] == cdim(c)]
        for a in proper:
            for b in proper:
                for cut in range(min(ranks[a], ranks[b]) - 1):
                    if kface(a, cut, '+') == kface(b, cut, '-'):
                        assert serialize(a, b, cut) == comp(cut, a, b)
                        serialized += 1
        counts[depth] += 1
    # A path with three stationary edges between two bigons, and its cyclic fold.
    chain = tree_ctx((((),), (), (), (), ((),)))
    assert first_separated_pair(chain) == 0
    interval = tree_ctx((((),),))
    assert first_separated_pair(interval) is None
    # The return edge in the 1-skeleton lets the same bigon supply both events.
    reverse = arr(interval[1], v(1), v(0))
    cyclic = interval + (reverse,)
    check_ctx(cyclic)
    assert first_separated_pair(cyclic) == 0
    print(f'{len(shapes)} trees, {checked} strict tableaux generated at the claimed ranks.')
    print('First fork (None means no fork):', dict(counts))
    print(f'{serialized} products of two active cells serialized and checked.')
    emitter = Emitter()
    for rank in (3, 4):
        realized_horizontal(rank, emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = 'GlobularForkChecks'
        source = emitter.module(module, __doc__)
        (args.agda_dir / (module + '.agda')).write_text(
            source.replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))


if __name__ == '__main__':
    main()
