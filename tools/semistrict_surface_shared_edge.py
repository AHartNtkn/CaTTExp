"""Check the two exchange squares across a shared edge and their planar braid images."""
from argparse import ArgumentParser
from collections import deque
from itertools import combinations, product
from pathlib import Path

from catt import arr, comp2, disc_tree, infer, subst_tm, subst_ty, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from relative_coherence_middle_wire import check_context, check_generic_exchange, check_tiles
from semistrict_surface_planar_tiers import artin_step, reduce_letters


def inverse(word):
    return tuple(-k for k in reversed(word))


def conjugate(u, v):
    return u + v + inverse(u)


def braid_image(strands, word):
    images = tuple((j + 1,) for j in range(strands))
    for gen in word:
        i = abs(gen) - 1
        if gen > 0:
            images = artin_step(images, i)
        else:
            a, b = images[i:i + 2]
            images = (*images[:i], b, reduce_letters(inverse(b) + a + b), *images[i + 2:])
    return images


def meridians(m, n):
    start = tuple(range(m + n))
    routes = {start: ()}
    queue = deque([start])
    loops = {}
    squares = set()
    while queue:
        word = queue.popleft()
        moves = [i for i in range(len(word) - 1) if word[i] < m <= word[i + 1]]
        for i in moves:
            next_word = (*word[:i], word[i + 1], word[i], *word[i + 2:])
            route = routes[word] + (i + 1,)
            if next_word not in routes:
                routes[next_word] = route
                queue.append(next_word)
            else:
                assert braid_image(m + n, route) == braid_image(m + n, routes[next_word])
            address = (word[i], word[i + 1] - m)
            loop = conjugate(routes[word], (i + 1, i + 1))
            if address in loops:
                assert braid_image(m + n, loop) == braid_image(m + n, loops[address])
            else:
                loops[address] = loop
        for i, j in combinations(moves, 2):
            assert j > i + 1
            squares.add(((word[i], word[i + 1] - m), (word[j], word[j + 1] - m)))
    incomparable = {((i, j), (k, l)) for i in range(m) for k in range(i+1, m)
                    for j in range(n) for l in range(j+1, n)}
    assert squares == incomparable and len(loops) == m * n
    for a, b in squares:
        assert braid_image(m + n, loops[a] + loops[b]) == braid_image(m + n, loops[b] + loops[a])
    return loops


def check_groups():
    for m, n in product(range(1, 5), repeat=2):
        meridians(m, n)
    count = 0
    for m in range(1, 5):
        loops = meridians(m, 1)
        images = {}
        for length in range(4):
            for letters in product((*range(1, m+1), *range(-m, 0)), repeat=length):
                if reduce_letters(letters) != letters:
                    continue
                braid = ()
                for letter in letters:
                    lasso = loops[(abs(letter)-1, 0)]
                    braid += lasso if letter > 0 else inverse(lasso)
                action = braid_image(m+1, braid)
                assert action not in images or images[action] == letters
                images[action] = letters
                count += 1
    loops = meridians(2, 2)
    c, x, d = (loops[p] for p in ((1, 0), (0, 0), (0, 1)))
    other = conjugate(inverse(x), d)
    commutator = c + other + inverse(c) + inverse(other)
    assert braid_image(4, commutator) == braid_image(4, ())
    assert braid_image(4, c + d) != braid_image(4, d + c)
    # Forgetting the two incomparable generators is a homomorphism out
    # of <c,x,y,d | xy=yx>. Its free-group value detects the same loop.
    assert reduce_letters((1, 2, -1, -2)) == (1, 2, -1, -2)
    print(f'Checked all square labels through a four-by-four grid and {count} reduced one-blue words.')
    print('The conjugated four-strand commutator maps to the identity; the unconjugated one does not.')


def check_cut(emitter):
    source = check_context()
    pole = tree_ctx(disc_tree(1))
    g = v(2)
    unit_g = identity(pole, g)
    scalar_type = arr(infer(pole, unit_g), unit_g, unit_g)
    target = pole + (scalar_type, scalar_type)
    il, ir = identity(pole, v(0)), identity(pole, v(1))
    sub = [v(0), v(0), v(1), v(1), il, il, g, ir, ir]
    sub += [identity(pole, il)] * 2 + [identity(pole, ir)] * 2
    for index, scalar in enumerate((v(3), v(4))):
        wrapped = comp2(target, 0, il, scalar) if index == 0 else comp2(target, 0, scalar, ir)
        actual = subst_ty(source[13 + index], sub)[2]
        other = infer(target, wrapped)[2]
        enter, leave = head(pole, actual, other), head(pole, other, actual)
        sub.append(comp2(target, 2, comp2(target, 2, enter, wrapped), leave))
    for j, ty in enumerate(source):
        assert infer(target, sub[j]) == subst_ty(ty, sub[:j])
    arity, generic, corners = check_generic_exchange()
    tiles, changes = check_tiles(source, arity, generic, corners)
    for j, term in enumerate(tiles + changes):
        cut = subst_tm(term, sub)
        ty = subst_ty(infer(source, term), sub)
        assert infer(target, cut) == ty
        emitter.check_type(f'cut{j}', target, cut, ty)
    a, b, subname = emitter.ctx(target), emitter.ctx(source), emitter.sub(sub)
    emitter.checks.append(f'cutMap : {a} ⊢sub {subname} ∶ {b}\n'
                          f'cutMap = from-just (checkSub {a} (from-just (checkCtx {a})) {subname} {b})\n')
    print('Checked the raw substitution on all 15 declarations, both square tiles and their four corners.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_groups()
    emitter = Emitter()
    check_cut(emitter)
    if args.agda_dir:
        name = 'SharedEdgeBraidCut'
        (args.agda_dir / (name + '.agda')).write_text(emitter.module(name, __doc__))
