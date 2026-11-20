"""Replace a two-bracket by triangles in its support, allowing repeated edges."""
from collections import Counter
from functools import reduce

from catt import STAR, arr, chain_tree, check_ctx, comp2, fv_ty, infer, subst_tm, tree_ctx, v
from rc2 import kappa, path
from relative_coherence_based_columns import Brackets, difference
from relative_coherence_cut import top_counts
from relative_coherence_hidden_seam import identity


def vertex(position):
    return v(2 * position - 1) if position else v(0)


def unroll(term, position):
    """Rebuild the given literal path on distinct successive positions."""
    if term[0] == 'v':
        return v(2 * position + 2), position + 1
    _, arity, ty, labels = term
    assert arity == tree_ctx(chain_tree((len(arity) - 1) // 2))
    new = [vertex(position)]
    for i in range(2, len(arity), 2):
        edge, position = unroll(labels[i], position)
        new.extend((vertex(position), edge))
    return ('coh', arity, ty, tuple(new)), position


def cone(p, q, term):
    word, start, end = path(p.ctx, term)
    first = p.bracket(v(q), v(start))
    generic = tree_ctx(chain_tree(1 + len(word)))
    lifted, last = unroll(term, 1)
    assert last == len(word) + 1
    labels = [v(q), v(start), first]
    for i in word:
        labels.extend((p.ctx[i][3], v(i)))
    assert subst_tm(lifted, labels) == term
    source = comp2(generic, 0, v(2), lifted)
    flat = reduce(lambda a, b: comp2(generic, 0, a, b),
                  (v(i) for i in range(2, len(generic), 2)))
    route = subst_tm(kappa(generic, source, flat), labels)
    counts = Counter()
    for j, edge in enumerate(word):
        x, y = p.ctx[edge][2:]
        qx, qy = p.bracket(v(q), x), p.bracket(v(q), y)
        step = p.bracket(comp2(p.ctx, 0, qx, v(edge)), qy)
        counts[step[1]] += 1
        for later in word[j + 1:]:
            step = comp2(p.ctx, 0, step, v(later))
        route = comp2(p.ctx, 1, route, step)
    target = p.bracket(v(q), v(end))
    assert infer(p.ctx, route)[2:] == (comp2(p.ctx, 0, first, term), target)
    assert top_counts(p.ctx, route) == counts
    return route


def replace(p, q, generator):
    source, target = infer(p.ctx, generator)[2:]
    a, b = cone(p, q, source), cone(p, q, target)
    leg = p.bracket(v(q), infer(p.ctx, source)[2])
    route = comp2(p.ctx, 1, comp2(p.ctx, 0, leg, generator), b)
    expected = Counter({generator[1]: 1})
    expected.update(top_counts(p.ctx, b))
    expected.subtract(top_counts(p.ctx, a))
    assert difference(p.ctx, a, route) == {i: n for i, n in expected.items() if n}
    witness = p.bracket(a, route)
    assert infer(p.ctx, witness) == arr(infer(p.ctx, a), a, route)
    return witness


def verify():
    p = Brackets(5)
    def edge(x, y):
        return p.bracket(v(x), v(y))

    def right_word(vertices):
        term = identity(p.ctx, v(vertices[-1]))
        for x, y in reversed(list(zip(vertices, vertices[1:]))):
            letter = edge(x, y)
            term = comp2(p.ctx, 0, letter, term)
        return term

    # All three paths share endpoints. Their oriented comparison cycle is literal.
    first = right_word([1, 2, 3, 2, 3, 2, 4])
    second = right_word([1, 1, 4])
    last = edge(1, 4)
    cycle = Counter()
    for a, b, q, n in ((first, second, 1, 1), (second, last, 4, 1), (first, last, 2, -1)):
        g = p.bracket(a, b)
        cycle[g[1]] += n
        witness = replace(p, q, g)
        left, right = infer(p.ctx, witness)[2:]
        for i, delta in difference(p.ctx, left, right).items():
            cycle[i] -= n * delta
    # Change from three local cone vertices to a single global one.
    for i, n in list(cycle.items()):
        if n:
            witness = replace(p, 0, v(i))
            left, right = infer(p.ctx, witness)[2:]
            for j, delta in difference(p.ctx, left, right).items():
                cycle[j] -= n * delta
    assert not any(cycle.values())
    empty = identity(p.ctx, v(1))
    repeated = p.bracket(empty, right_word([1, 1, 1, 1]))
    replace(p, 0, repeated)
    check_ctx(p.ctx)
    supports = []
    for i, ty in enumerate(p.ctx):
        supports.append({i} if ty == STAR else set().union(*(supports[j] for j in fv_ty(ty))))
    assert max(map(len, supports)) == 4
    print(f'{len(p.ctx)} typed declarations, maximum four names per generator.')
    print('Local triangle replacements and the common-vertex contraction fill the entire two-cycle.')


if __name__ == '__main__':
    verify()
