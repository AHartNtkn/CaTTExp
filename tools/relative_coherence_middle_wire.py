"""Check the CaTT input, generic exchange and endpoint necklace graph of R5 response 3."""

from collections import defaultdict
from itertools import product
from sys import argv

from catt import (
    STAR, arr, chain_tree, check_ctx, comp2, disc_tree, fv_tm, glue_tree, infer,
    maximal_vars, sub_from, subst_tm, tree_ctx, v,
)


def check_context():
    context = (STAR,) * 4
    edges = [(0, 1), (0, 1), (1, 2), (2, 3), (2, 3)]
    context += tuple(arr(STAR, v(a), v(b)) for a, b in edges)
    for a, b in [(4, 5), (4, 5), (7, 8), (7, 8)]:
        context += (arr(infer(context, v(a)), v(a), v(b)),)
    left = [comp2(context, 0, v(i), v(6)) for i in (9, 10)]
    right = [comp2(context, 0, v(6), v(j)) for j in (11, 12)]
    for source, target in [left, right]:
        context += (arr(infer(context, source), source, target),)
    check_ctx(context)
    return context


def check_generic_exchange():
    context = tree_ctx(glue_tree(3, 1, 3))
    a, b = map(v, maximal_vars(context))
    a0, a1 = infer(context, a)[2:]
    b0, b1 = infer(context, b)[2:]
    corners = {(i, j): comp2(context, 1, x, y)
               for i, x in enumerate((a0, a1)) for j, y in enumerate((b0, b1))}
    sides_a = [comp2(context, 1, a, y) for y in (b0, b1)]
    sides_b = [comp2(context, 1, x, b) for x in (a0, a1)]
    for j, side in enumerate(sides_a):
        assert infer(context, side)[2:] == (corners[0, j], corners[1, j])
    for i, side in enumerate(sides_b):
        assert infer(context, side)[2:] == (corners[i, 0], corners[i, 1])
    ab = comp2(context, 2, sides_a[0], sides_b[1])
    ba = comp2(context, 2, sides_b[0], sides_a[1])
    boundary = arr(infer(context, ab), ab, ba)
    identity_sub = tuple(map(v, range(len(context))))
    exchange = ('coh', context, boundary, identity_sub)
    assert infer(context, exchange) == boundary
    return context, exchange, corners


def comparison(context, tree, generators, start, end):
    """Use the coherence head on the pasting supporting these two parallel terms."""
    paste = tree_ctx(tree)
    inclusion = sub_from(paste, context, dict(zip(maximal_vars(paste), generators)))
    inverse = {term[1]: v(i) for i, term in enumerate(inclusion)}
    assert all(term[0] == 'v' for term in inclusion)
    assert fv_tm(start) | fv_tm(end) <= inverse.keys()
    first, last = subst_tm(start, inverse), subst_tm(end, inverse)
    result = ('coh', paste, arr(infer(paste, first), first, last), inclusion)
    assert infer(context, result)[2:] == (start, end)
    return result


def check_tiles(context, paste, exchange, corners):
    def row(term, ends):
        for side, (f, h) in enumerate(ends):
            wires = [v(f), v(6), v(h)]
            chosen = comp2(context, 0, comp2(context, 0, wires[0], wires[1]), wires[2])
            actual = infer(context, infer(context, term)[2])[2 + side]
            if chosen == actual:
                continue
            source, target = (chosen, actual) if side == 0 else (actual, chosen)
            change = comparison(context, chain_tree(3), wires, source, target)
            term = (comp2(context, 1, change, term) if side == 0
                    else comp2(context, 1, term, change))
        return term

    a_first = row(comp2(context, 0, v(13), v(7)), [(4, 7), (5, 7)])
    b_last = row(comp2(context, 0, v(5), v(14)), [(5, 7), (5, 8)])
    b_first = row(comp2(context, 0, v(4), v(14)), [(4, 7), (4, 8)])
    a_last = row(comp2(context, 0, v(13), v(8)), [(4, 8), (5, 8)])
    frames = [sub_from(paste, context, dict(zip(maximal_vars(paste), rows)))
              for rows in [(a_first, b_last), (b_first, a_last)]]
    # Reverse the generic head for the second row order so both tiles run
    # from the A-first perimeter route to the B-first perimeter route.
    _, arity, ty, sigma = exchange
    reverse = ('coh', arity, arr(ty[1], ty[3], ty[2]), sigma)
    tiles = [subst_tm(head, frame) for head, frame in zip((exchange, reverse), frames)]
    for tile in tiles:
        infer(context, tile)
    corner_changes = []
    for (i, j), generic in corners.items():
        first = subst_tm(generic, frames[0])
        last = subst_tm(corners[j, i], frames[1])
        corner_changes.append(comparison(
            context, (disc_tree(1), (), disc_tree(1)), [v(9+i), v(6), v(11+j)], first, last))
    return tiles, corner_changes


def check_diagonal_necklaces():
    # Nondegenerate simplices in the double square are strict chains in
    # {0,1}^2. Keep the two copies distinct precisely off their common perimeter.
    corners = list(product(range(2), repeat=2))
    def chains(path):
        yield path
        for p in corners:
            if p != path[-1] and all(a <= b for a, b in zip(path[-1], p)):
                yield from chains(path + (p,))
    simplices = set()
    for origin in corners:
        for chain in chains((origin,)):
            spans = all(len({p[k] for p in chain}) > 1 for k in range(2))
            for sheet in (('L', 'R') if spans else ('edge',)):
                simplices.add((chain, sheet))
    edges = sorted((p[0], p[1], tag) for p, tag in simplices if len(p) == 2)
    def paths(start):
        if start == (1, 1):
            yield ()
        for e in edges:
            if e[0] == start:
                for rest in paths(e[1]):
                    yield (e,) + rest
    vertices = set(paths((0, 0)))
    adjacency = defaultdict(set)
    for triangle, tag in simplices:
        if len(triangle) != 3:
            continue
        a, b, c = triangle
        via = ((a, b, 'edge'), (b, c, 'edge'))
        diag = ((a, c, tag),)
        assert via in vertices and diag in vertices
        adjacency[via].add(diag)
        adjacency[diag].add(via)
    assert all(len(adjacency[path]) == 2 for path in vertices)
    reached = set()
    stack = [next(iter(vertices))]
    while stack:
        path = stack.pop()
        if path not in reached:
            reached.add(path)
            stack.extend(adjacency[path] - reached)
    assert reached == vertices
    assert sorted(len(path) for path in vertices) == [1, 1, 2, 2]
    assert max(len(chain) for chain, _ in simplices) == 3
    return len(vertices), sum(map(len, adjacency.values())) // 2


if __name__ == '__main__':
    context = check_context()
    paste, exchange, corners = check_generic_exchange()
    tiles, changes = check_tiles(context, paste, exchange, corners)
    v_count, e_count = check_diagonal_necklaces()
    if argv[1:] == ['--agda']:
        from emit_agda import Emitter
        emitter = Emitter()
        emitter.check_typed('generic', paste, exchange)
        for i, term in enumerate(tiles + changes):
            emitter.check_typed(f'witness{i}', context, term)
        print(emitter.module('MiddleWire', 'Context, generic exchange, both tiles and corner comparisons.'))
    else:
        assert not argv[1:], 'the only option is --agda'
        print(f'{len(context)} declarations and the generic exchange checked')
        print(f'{len(tiles)} instantiated exchange terms and {len(changes)} corner comparisons checked')
        print(f'Connected necklace graph: {v_count} vertices, {e_count} edges, rank {e_count-v_count+1}')
