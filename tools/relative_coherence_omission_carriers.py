"""Test cubical omission carriers and the orientation of their simplex instructions."""
from argparse import ArgumentParser
from collections import Counter
from functools import reduce
from itertools import combinations, permutations, product
from pathlib import Path

from catt import STAR, arr, chain_tree, comp2, infer, maximal_vars, sub_from, subst_tm, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import head

from relative_coherence_forced_edges import tree_from_prufer
from relative_coherence_simplex_carrier import facets, nonzero


def available(face, edges, names):
    return names - {edges[i][bit] for i, bit in enumerate(face) if bit != 2}


def cells(edges, names, wanted):
    return {face for face in product(range(3), repeat=len(edges)) if available(face, edges, names) <= wanted}


def erase_leaf(edges, v):
    index, = [i for i, e in enumerate(edges) if v in e]
    edge = edges[index]
    u = next(x for x in edge if x != v)
    return index, edge.index(u), u


def check_carriers(n):
    names = frozenset(range(n))
    count = 0
    for code in product(range(n), repeat=n-2):
        adj = tree_from_prufer(code)
        edges = [(i, j) for i in names for j in adj[i] if i < j]
        v = next(i for i in names if len(adj[i]) == 1)
        index, into_u, u = erase_leaf(edges, v)
        shortened = edges[:index]+edges[index+1:]
        for bits in range(1, 1 << n):
            wanted = {i for i in names if bits >> i & 1}
            chart = cells(edges, names, wanted)
            assert max(face.count(2) for face in chart) == len(wanted)-1
            layer = [{f[:index]+f[index+1:] for f in chart if f[index] == bit} for bit in range(3)]
            base = wanted - {v}
            fixed = cells(shortened, names-{v}, base)
            if v not in wanted:
                assert layer[1-into_u] == fixed and not layer[into_u] and not layer[2]
            else:
                extended = cells(shortened, names-{v}, base|{u})
                assert layer[1-into_u] == layer[2] == fixed and layer[into_u] == extended
            count += 1
    return count


def directed_tests(n):
    counts = Counter()
    for code in product(range(n), repeat=n-2):
        adj = tree_from_prufer(code)
        edge_list = [(i, j) for i in range(n) for j in adj[i] if i < j]
        for edges in permutations(edge_list):
            # At a forced root, each arrowhead is its endpoint further from the root.
            roots = []
            for root in range(n):
                level = {root: 0}
                stack = [root]
                while stack:
                    v = stack.pop()
                    for u in adj[v] - level.keys():
                        level[u] = level[v]+1
                        stack.append(u)
                roots.append(sum((level[b] > level[a]) << i for i, (a, b) in enumerate(edges)))
            for bits in range(1 << (n-1)):
                states = sorted((r^bits for r in roots), key=int.bit_count)
                counts['all'] += 1
                if any(a & ~b for a, b in zip(states, states[1:])):
                    continue
                counts['arrows'] += 1
                changes = [(b^a).bit_length()-1 for a, b in zip(states, states[1:])]
                # The shortcut crosses the second gap before the first one.
                # The positive tensor square changes high-first to low-first.
                if all(a < b for a, b in zip(changes, changes[1:])):
                    counts['triangles'] += 1
    return counts


def instruction(k, vertices):
    words = [(1,)*vertices[0]]
    for a, b in zip(vertices, vertices[1:]):
        paths = [(0,)*i+(2,)+(1,)*(b-a-1-i) for i in range(b-a)]
        words = [w+t for w in words for t in paths]
    return [w+(0,)*(k-vertices[-1]) for w in words]


def cubical_boundary(rows):
    chain = Counter()
    for w in rows:
        sign = 1
        for i, val in enumerate(w):
            if val != 2:
                continue
            for bit in (0, 1):
                chain[w[:i]+(bit,)+w[i+1:]] += sign*(2*bit-1)
            sign = -sign
    return nonzero(chain)


def positive_map(k):
    ascending = list(range(k+1))
    # At the all-zero root, each omission is the endpoint further to its right.
    edges = [(i+1, i) for i in range(k)]
    for length in range(1, k+2):
        for vertices in combinations(ascending, length):
            cells = instruction(k, vertices)
            assert len(set(cells)) == len(cells)
            for w in cells:
                assert w.count(2) == length-1 and available(w, edges, set(ascending)) == set(vertices)
            expected = Counter()
            if length > 1:
                for face, sign in facets(vertices):
                    expected.update({w: sign for w in instruction(k, face)})
            assert cubical_boundary(cells) == nonzero(expected)


def directed_square(output):
    ctx = (STAR,)*4
    def declare(s, t):
        nonlocal ctx
        value = v(len(ctx))
        ctx += (arr(infer(ctx, s), s, t),)
        return value
    bottom, right, left, top = (declare(v(s), v(t)) for s, t in ((0,1), (1,3), (0,2), (2,3)))
    early, late = comp2(ctx, 0, bottom, right), comp2(ctx, 0, left, top)
    square = declare(late, early)
    l, r = declare(v(0), v(0)), declare(v(3), v(3))
    chart = tree_ctx(chain_tree(3))
    a, b, c = map(v, maximal_vars(chart))
    first = comp2(chart, 0, comp2(chart, 0, a, b), c)
    second = comp2(chart, 0, a, comp2(chart, 0, b, c))
    emitter = Emitter()
    for k in (0, 1, 5):
        power = lambda x, p: reduce(lambda y,z: comp2(ctx, 0, y, z), [x]*k) if k else ident(ctx,p)
        prefix, suffix = power(l, v(0)), power(r, v(3))
        def labels(path):
            return sub_from(chart, ctx, dict(zip(maximal_vars(chart), (prefix, path, suffix))))
        forwards, backwards = (subst_tm(head(chart, x, y), labels(early))
                               for x,y in ((first,second),(second,first)))
        move = comp2(ctx, 0, comp2(ctx, 0, prefix, square), suffix)
        start = subst_tm(first, labels(late))
        m, end = (subst_tm(t, labels(early)) for t in (first,second))
        for tag, term, x, y in (('move', comp2(ctx, 1, move, forwards), start, end),
                               ('reassociate', forwards, m, end), ('return', backwards, end, m)):
            ty = arr(infer(ctx, x), x, y)
            assert infer(ctx, term) == ty
            if output:
                emitter.check_type(tag+str(k), ctx, term, ty)
    if output:
        output.write_text(emitter.module(output.stem, 'Directed triangle and reversible boundary reassociation.'))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--trees', type=int, default=5)
    parser.add_argument('--cube', type=int, default=8)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    directed_square(args.agda)
    for n in range(2, args.trees+1):
        count = check_carriers(n)
        result = directed_tests(n)
        print(f'{n} names: {count} carrier recursions, {dict(result)}', flush=True)
    for k in range(1, args.cube+1):
        positive_map(k)
    print(f'All simplex instructions positive with exact boundaries through cube dimension {args.cube}.')
