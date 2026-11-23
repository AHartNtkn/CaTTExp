"""Check simultaneous unit pruning and the configuration carriers for scalar operations."""
from argparse import ArgumentParser
from itertools import combinations, permutations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import infer, is_ps, maximal_vars, subst_tm, subst_ty, tree_ctx, v
from emit_agda import Emitter
from partial_cylinder_steiner import trees
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_scalar_pairs import branches, positions, trunk


def prune(ctx, picks):
    # Identify each leaf's two faces and replace that leaf by the identity.
    # In a temporal string multiple adjacent identifications can be requested.
    parent = list(range(len(ctx)))
    def root(i):
        while parent[i] != i:
            i = parent[i]
        return i
    for i in picks:
        start, end = ctx[i][2:]
        parent[root(end[1])] = root(start[1])
    labels, pruned, names = [], (), {}
    for i, ty in enumerate(ctx):
        expected = subst_ty(ty, tuple(labels))
        if i in picks:
            image = identity(pruned, labels[ty[2][1]])
        elif root(i) in names:
            image = names[root(i)]
        else:
            image = v(len(pruned))
            pruned += (expected,)
            names[root(i)] = image
        assert infer(pruned, image) == expected
        labels.append(image)
    assert is_ps(pruned)
    return pruned, tuple(labels)


def check_prunings(emitter):
    count = corners = 0
    for size in range(1, 7):
        for shape in trees(size):
            ctx = tree_ctx(shape)
            leaves = maximal_vars(ctx)
            for k in range(1, len(leaves) + 1):
                for selected in combinations(leaves, k):
                    result, labels = prune(ctx, selected)
                    count += 1
                    for leaf in selected:
                        partial, first = prune(ctx, (leaf,))
                        remainder = [first[i][1] for i in selected if i != leaf]
                        final, second = prune(partial, remainder)
                        assert final == result
                        assert tuple(subst_tm(t, second) for t in first) == labels
                        corners += 1
                    if size <= 4 and len(selected) > 1:
                        source, target, sigma = emitter.ctx(result), emitter.ctx(ctx), emitter.sub(labels)
                        name = f'pruning{count}'
                        emitter.checks.append(
                            f'{name} : {source} ⊢sub {sigma} ∶ {target}\n'
                            f'{name} = from-just (checkSub {source} (from-just (checkCtx {source})) '
                            f'{sigma} {target})\n')
    return count, corners


def check_carriers(n, arity):
    names = tuple(range(arity))
    edges = tuple(combinations(names, 2))
    # An edge value has a level and a direction. Strict comparison of its
    # levels allows either sign. At equal levels the signs must coincide.
    def above(edge, bottom):
        return edge == bottom or edge // 2 > bottom // 2
    def orders(values, keep):
        pairs = [pair for pair in edges if set(pair) <= keep]
        wins = dict.fromkeys(keep, 0)
        for (i, j) in pairs:
            wins[(i, j)[values[(i, j)] % 2]] += 1
        assert sorted(wins.values()) == list(range(len(keep)))
    subsets = [set(s) for k in range(1, arity + 1) for s in combinations(names, k)]
    count = restrictions = 0
    # Each ordered tree gives the slot order and divergence levels.
    partitions = [tuple([x] for x in names), ([0], list(names[1:]))]
    if arity >= 4:
        partitions.append(([0, 2], [1, 3]))
    for blocks in partitions:
        index = {x: k for k, block in enumerate(blocks) for x in block}
        external = [pair for pair in edges if index[pair[0]] != index[pair[1]]]
        # A tree on the slots can have a distinct cut at each adjacent gap.
        for gaps in product(range(n), repeat=len(blocks)-1):
            fixed = {}
            for i, j in external:
                lo, hi = sorted((index[i], index[j]))
                fixed[i, j] = 2 * min(gaps[lo:hi]) + int(index[i] > index[j])
            for order in permutations(names):
                signs = {e: int(order.index(e[0]) > order.index(e[1])) for e in edges}
                choices = [[2*l + signs[e] for l in range(n)
                            if e not in fixed or above(2*l + signs[e], fixed[e])] for e in edges]
                for levels in product(*choices):
                    graph = dict(zip(edges, levels))
                    collapsed = graph | fixed
                    orders(collapsed, set(names))
                    assert all(above(graph[e], collapsed[e]) for e in edges)
                    for keep in subsets:
                        restricted = {e: value for e, value in graph.items() if set(e) <= keep}
                        split = {e: fixed[e] for e in restricted if e in fixed}
                        assert restricted | split == {e: collapsed[e] for e in restricted}
                        restrictions += 1
                    count += 1
    return count, restrictions


def check_trunks():
    checks = 0
    shapes = [t for size in range(1, 6) for t in trees(size)]
    for n in range(2, 5):
        for local in shapes:
            if trunk(local) == max(map(len, _leaves(local))):
                continue
            grouped = local
            for _ in range(n):
                grouped = (grouped,)
            for branch, _ in branches(grouped):
                for split in shapes:
                    if len(positions(split, n)) < 2:
                        continue
                    assert trunk(split) < n <= len(branch)-1
                    checks += 1
    return checks


def _leaves(tree, prefix=()):
    if not tree:
        yield prefix
    for i, child in enumerate(tree):
        yield from _leaves(child, prefix + (i,))


def check_rice(checkout):
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        (folder / 'Triple.catt').write_text('''import examples/syllepsis-su
def triple (x : *) (a : id(id(x)) -> id(id(x))) (b : id(id(x)) -> id(id(x))) (c : id(id(x)) -> id(id(x))) = comp[[[syllepsis_su(x,a,b)]],c]
def keep_pair (x : *) (a : id(id(x)) -> id(id(x))) (b : id(id(x)) -> id(id(x))) : triple(x,a,b,id(id(id(x)))) -> syllepsis_su(x,a,b) = id(syllepsis_su(x,a,b))
''')
        (folder / 'Wrong.catt').write_text('''import Triple
def wrong (x : *) (a : id(id(x)) -> id(id(x))) (b : id(id(x)) -> id(id(x))) : triple(x,a,b,id(id(id(x)))) -> syllepsis_su(x,b,a) = id(syllepsis_su(x,a,b))
''')
        for mode in ('--su', '--sua'):
            accepted(run(binary, folder, 'Triple.catt', [mode]), 'Triple.catt', ['triple', 'keep_pair'])
            rejected(run(binary, folder, 'Wrong.catt', [mode]), 'Wrong.catt', 'wrong')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    print('pruning quotients and iterated factorizations:', *check_prunings(emitter))
    for n, r in [(2, 3), (3, 3), (2, 4)]:
        print(f'levels {n}, particles {r}, graph contractions and restrictions:', *check_carriers(n, r))
    print('grouped/split insertion height checks:', check_trunks())
    if args.agda_dir:
        name = 'SimultaneousScalarPruning'
        (args.agda_dir / (name + '.agda')).write_text(emitter.module(name, __doc__))
    if args.catt_strict:
        check_rice(args.catt_strict.resolve())


if __name__ == '__main__':
    main()
