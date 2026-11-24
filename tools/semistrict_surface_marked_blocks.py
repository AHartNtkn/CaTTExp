"""Check protected path factorizations and their raw CaTT boundary projections."""

import argparse
from collections import defaultdict
from functools import cache
from itertools import product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, maximal_vars, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_contextual_cut import DecoratedCut


LEFT = {'F': 'a', 'G': 'b'}
RIGHT = {'F': 'b', 'G': 'ab'}


@cache
def normals(word):
    """All terminal grades under single-letter absorption, ignoring object tags."""
    descendants = set()
    for i, (x, y) in enumerate(zip(word, word[1:])):
        if y in LEFT and x in LEFT[y]:
            descendants.update(normals(word[:i] + word[i + 1:]))
        if x in RIGHT and y in RIGHT[x]:
            descendants.update(normals(word[:i + 1] + word[i + 2:]))
    return descendants or {word}


def grade(word):
    result, = normals(word)
    return result


def protected(normal):
    return all(not (x in RIGHT and y in LEFT and set(RIGHT[x]) & set(LEFT[y]))
               for x, y in zip(normal, normal[1:]))


def sector_positions(word):
    """Independently address each vertex using the neighbouring marked occurrences."""
    marks = [(i, edge) for i, edge in enumerate(word) if edge in LEFT]
    if not marks:
        return [('seam', i) for i in range(len(word) + 1)]
    positions = [None] * (len(word) + 1)
    seam = 0
    previous_end = 0
    for index, (i, edge) in enumerate(marks):
        start = i
        while start and word[start - 1] in LEFT[edge]:
            start -= 1
        end = i + 1
        while end < len(word) and word[end] in RIGHT[edge]:
            end += 1
        assert previous_end <= start
        for j in range(previous_end, start + 1):
            positions[j] = ('seam', seam + j - previous_end)
        seam += start - previous_end
        for j in range(start + 1, i + 1):
            positions[j] = ('left', index, word[start:j])
        for j in range(i + 1, end):
            positions[j] = ('right', index, word[j:end])
        seam += 1
        previous_end = end
    for j in range(previous_end, len(word) + 1):
        positions[j] = ('seam', seam + j - previous_end)
    return positions


def check_frames():
    frames = defaultdict(dict)
    positions = defaultdict(dict)
    checked = skipped = 0
    for length in range(7):
        for letters in product('ab#FG', repeat=length):
            word = ''.join(letters)
            normal = grade(word)
            if not protected(normal):
                skipped += 1
                continue
            for i, position in enumerate(sector_positions(word)):
                frame = (grade(word[:i]), grade(word[i:]))
                assert frames[normal].setdefault(frame, position) == position
                assert positions[normal].setdefault(position, frame) == frame
                checked += 1
    assert not protected(grade('FbG'))
    assert (grade('F'), grade('bG')) == (grade('Fb'), grade('G'))
    assert protected(grade('Fb#bG'))
    assert sector_positions('Fb#bG')[1:5] == [
        ('right', 0, 'b'), ('seam', 1), ('seam', 2), ('left', 1, 'b')]
    print(f'{checked} positions compared in both directions on {len(frames)} protected grades; '
          f'{skipped} words with ambiguous grade excluded')


def check_repeated_rules():
    for n in range(1, 8):
        states = {''.join(bits) for bits in product(('lf', 'fr'), repeat=n)}
        for word in states:
            neighbours = {word[:i] + target + word[i + 2:]
                          for source, target in [('lf', 'fr'), ('fr', 'lf')]
                          for i in range(len(word) - 1) if word.startswith(source, i)}
            expected = {word[:i] + ('fr' if word[i:i+2] == 'lf' else 'lf') + word[i+2:]
                        for i in range(0, 2*n, 2)}
            assert neighbours == expected <= states
    print('Every positioned move agrees with one coordinate flip on cubes of ranks 1 through 7')


@cache
def typed_normals(path):
    descendants = set()
    for i, ((x, s, t), (y, u, vtx)) in enumerate(zip(path, path[1:])):
        assert t == u
        for marker, allowed in ((y, x in LEFT.get(y, '')), (x, y in RIGHT.get(x, ''))):
            if allowed:
                shorter = path[:i] + ((marker, s, vtx),) + path[i + 2:]
                descendants.update(typed_normals(shorter))
    return descendants or {path}


def check_typed_seams():
    edges = [('a', 1, 0), ('b', 0, 1), ('#', 1, 1)]
    edges += [(m, s, t) for m in LEFT for s, t in product(range(2), repeat=2)]
    paths = [()]
    checked = 0
    for _ in range(5):
        paths = [p + (e,) for p in paths for e in edges if not p or p[-1][2] == e[1]]
        for p in paths:
            normal = grade(''.join(e[0] for e in p))
            if protected(normal):
                result, = typed_normals(p)
                assert ''.join(e[0] for e in result) == normal
                assert (result[0][1], result[-1][2]) == (p[0][1], p[-1][2])
                checked += 1
    overlap = (('F', 0, 0), ('b', 0, 1), ('G', 1, 1))
    assert typed_normals(overlap) == {
        (('F', 0, 0), ('G', 0, 1)), (('F', 0, 1), ('G', 1, 1))}
    print(f'{checked} protected two-object paths have a unique typed normal form; '
          'the overlap realizes both seam vertices')


def raw_blocks(count, emitter):
    """One finite part of the actual factorization interval on (lf)^count."""
    ctx = (STAR,)

    def declare(ty):
        nonlocal ctx
        term = v(len(ctx))
        ctx += (ty,)
        return term

    def between(s, t):
        ty = infer(ctx, s)
        assert infer(ctx, t) == ty
        return declare(arr(ty, s, t))

    entry = v(0)
    bubbles = []
    for i in range(count):
        left, right, exit_vertex = (declare(STAR) for _ in range(3))
        l, fl = between(entry, left), between(left, exit_vertex)
        fr, r = between(entry, right), between(right, exit_vertex)
        start, end = comp2(ctx, 0, l, fl), comp2(ctx, 0, fr, r)
        forward, back = between(start, end), between(end, start)
        tour = comp2(ctx, 1, forward, back)
        positive = between(tour, comp2(ctx, 1, tour, tour))
        unit = identity(ctx, start)
        birth, death = between(unit, tour), between(tour, unit)
        bubble = comp2(ctx, 2, birth, death)
        assert infer(ctx, bubble) == arr(infer(ctx, unit), unit, unit)
        if count == 1:
            cut = DecoratedCut(ctx, {right[1], exit_vertex[1]})
            lower = cut.term(bubble, (), ())
            source, target = infer(tuple(cut.lower), lower)[2:]
            assert source == target == cut.term(unit, (), ())
            assert cut.labels[cut.term(start, (), ())] == ((l[1],), fl[1], ())
            assert cut.labels[cut.term(end, (), ())] == ((), fr[1], (r[1],))
            assert [cut.labels[lower[3][j]][1] for j in maximal_vars(lower[1])] == [
                birth[1], death[1]]
            projected = cut.term(positive, (), ())
            check_ctx(tuple(cut.lower))
            lower_unit = cut.term(unit, (), ())
            emitter.check_type('projected-bubble', tuple(cut.lower), lower,
                               arr(infer(tuple(cut.lower), lower_unit), lower_unit, lower_unit))
            emitter.check_typed('projected-positive', tuple(cut.lower), projected)
        bubbles.append(bubble)
        entry = exit_vertex
    full = bubbles[0]
    for bubble in bubbles[1:]:
        full = comp2(ctx, 0, full, bubble)
    check_ctx(ctx)
    emitter.check_typed('block-bubbles-' + str(count), ctx, full)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_frames()
    check_typed_seams()
    check_repeated_rules()
    emitter = Emitter()
    for count in (1, 2, 3):
        raw_blocks(count, emitter)
    print('Checked the indexed raw bubble, its moving 1-poles, and composites on 1–3 blocks')
    if args.agda_dir:
        name = 'MarkedBlocks'
        (args.agda_dir / (name + '.agda')).write_text(
            emitter.module(name, 'Indexed and spatially composed raw block boundaries.'))


if __name__ == '__main__':
    main()
