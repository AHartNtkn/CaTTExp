"""Check two local Gray compositors and mixed spatial/temporal exchanges."""
from argparse import ArgumentParser
from functools import lru_cache
from itertools import permutations, product
from math import comb
from pathlib import Path

from catt import comp2, disc_tree, infer, maximal_vars, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head
from semistrict_surface_shared_edge import braid_image


def pile(word, pairs):
    """Trace-group piling for the commuting pairs of opposite ordered paths."""
    stacks = {p: [] for p in pairs}
    for p, sign in word:
        dependent = [
            q for q in pairs
            if p != q and (p[0] - q[0]) * (p[1] - q[1]) <= 0
        ]
        if stacks[p] and stacks[p][-1] == -sign:
            stacks[p].pop()
            for q in dependent:
                assert stacks[q].pop() == 0
        else:
            stacks[p].append(sign)
            for q in dependent:
                stacks[q].append(0)
    return tuple(tuple(stack) for stack in stacks.values())


def check_squares(m, n):
    start = tuple(range(m + n))
    pairs = list(product(range(m), range(n)))
    paths = {start: ()}
    pending = [start]
    count = 0
    while pending:
        w = pending.pop()

        def move(word, i, sheet):
            a, b = word[i:i + 2]
            p = (a, b - m) if a < m else (b, a - m)
            switched = (*word[:i], b, a, *word[i + 2:])
            label = ((p, 1 if a < m else -1),) if sheet else ()
            return switched, label

        directions = [i for i in range(len(w) - 1) if (w[i] < m) != (w[i + 1] < m)]
        for i in directions:
            next_word, label = move(w, i, True)
            if w[i] < m:
                path = paths[w] + label
                if next_word not in paths:
                    paths[next_word] = path
                    pending.append(next_word)
                else:
                    assert pile(path, pairs) == pile(paths[next_word], pairs)
            for j in directions:
                if j <= i + 1:
                    continue
                for s, t in product((False, True), repeat=2):
                    a, x = move(w, i, s)
                    b, y = move(w, j, t)
                    end_a, yy = move(a, j, t)
                    end_b, xx = move(b, i, s)
                    assert end_a == end_b and pile(x + yy, pairs) == pile(y + xx, pairs)
                    count += 1
    assert len(paths) == comb(m + n, m)
    full = paths[tuple(range(m, m + n)) + tuple(range(m))]
    assert len(full) == m * n
    # Separately move left or right subblocks. This is multiplicativity
    # in each input of the Gray interchanger on the second sheet.
    for axis, length in enumerate((m, n)):
        for k in range(length + 1):
            if axis == 0:
                first = tuple(x for x in full if x[0][0] >= k)
            else:
                first = tuple(x for x in full if x[0][1] < k)
            rest = tuple(x for x in full if x not in first)
            assert pile(first + rest, pairs) == pile(full, pairs)
    return count


def check_mixed(emitter):
    # In each outer column the 3-cells form a temporal string of 3-discs
    # along 1. In the second shape the two rows each span both columns.
    two = (disc_tree(1), disc_tree(1))
    fixtures = [
        ((two, disc_tree(2)), (0, (1, 0, 1), 2), (0, 0, 1)),
        ((two, two), (1, (0, 0, 2), (0, 1, 3)), (0, 0, 1, 1)),
    ]
    hexagons = 0
    for fixture, (arity, shape, col) in enumerate(fixtures):
        ctx = tree_ctx(arity)
        atoms = tuple(map(v, maximal_vars(ctx)))
        assert len(atoms) == len(col)

        def paste(subtree, values):
            if isinstance(subtree, int):
                return values[subtree]
            cut, left, right = subtree
            return comp2(ctx, cut, paste(left, values), paste(right, values))

        @lru_cache(maxsize=None)
        def serial(order):
            values = [infer(ctx, a)[2] for a in atoms]
            steps = []
            for k in order:
                values[k] = atoms[k]
                steps.append(paste(shape, values))
                values[k] = infer(ctx, atoms[k])[3]
            return composite(ctx, 2, steps)

        def route(initial, moves):
            order = list(initial)
            path = []
            local = [[], []]
            for pos in moves:
                before = serial(tuple(order))
                a, b = order[pos:pos + 2]
                if col[a] == col[b]:
                    lane = col[a]
                    local_pos = 1 + sum(col[k] == lane for k in order[:pos])
                    local[lane].append(local_pos if a < b else -local_pos)
                order[pos:pos + 2] = (b, a)
                after = serial(tuple(order))
                path.append(head(ctx, before, after))
            return composite(ctx, 3, path), [braid_image(col.count(i), w) for i, w in enumerate(local)]

        for initial in permutations(range(len(atoms))):
            for pos in range(len(atoms) - 2):
                left, lbraids = route(initial, (pos, pos + 1, pos))
                right, rbraids = route(initial, (pos + 1, pos, pos + 1))
                assert lbraids == rbraids and infer(ctx, left) == infer(ctx, right)
                if initial == tuple(range(len(atoms))) and pos == 0:
                    filler = head(ctx, left, right)
                    assert infer(ctx, filler)[2:] == (left, right)
                    emitter.check_type(f'mixed{fixture}', ctx, filler, infer(ctx, filler))
                hexagons += 1
    return hexagons


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    count = sum(check_squares(m, n) for m, n in product(range(1, 5), repeat=2))
    letters = list(product(range(2), repeat=2))
    c, x, d = (1, 0), (0, 0), (0, 1)
    word = [(c, 1), (x, -1), (d, 1), (x, 1), (c, -1), (x, -1), (d, -1), (x, 1)]
    assert pile(word, letters) != pile((), letters)
    emitter = Emitter()
    hexagons = check_mixed(emitter)
    if args.agda_dir:
        name = 'CartesianGrayExchanges'
        (args.agda_dir / (name + '.agda')).write_text(emitter.module(name, __doc__))
    print(f'Checked {count} oriented square/sheet choices and {hexagons} mixed exchange hexagons.')
    print('Both block multiplicativities passed; the track model distinguishes the four-letter commutator.')
