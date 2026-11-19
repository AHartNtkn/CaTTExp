"""Construct the pure CaTT section of the three-interval Gray cube (outbox CT, Q2)."""
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, src, tdim, tgt, v
from emit_agda import Emitter
from rc2 import kappa, lfold, path, rcomp


def mask(axes):
    return sum(1 << axis for axis in axes)


def square_chain(term):
    """Strict 2-chain of the constructors used here, with multiplicity."""
    if term[0] == 'v':
        return Counter([term])
    _, arity, _, substitution = term
    result = Counter()
    # A path correction contributes zero. A whisker or vertical composite
    # uses each square of its two-globe arity once.
    for boundary, argument in zip(arity, substitution):
        if tdim(boundary) == 1:
            result.update(square_chain(argument))
    return result


def build_cube():
    # A vertex is its set of completed moves. Words list the remaining moves in order.
    axes = range(3)
    context = (STAR,) * 8
    checks = []

    def declare(boundary):
        nonlocal context
        term = v(len(context))
        context += (boundary,)
        return term

    def arrow(a, b):
        base = infer(context, a)
        assert infer(context, b) == base
        return arr(base, a, b)

    edges = {}
    for vertex in range(8):
        for axis in axes:
            bit = 1 << axis
            if not vertex & bit:
                edges[vertex, axis] = declare(arrow(v(vertex), v(vertex | bit)))

    def word_name(word):
        return "".join(str(axis + 1) for axis in word)

    paths = {}
    for vertex in range(8):
        available = [i for i in axes if not vertex & (1 << i)]
        for length in range(1, len(available) + 1):
            for word in permutations(available, length):
                letters = [edges[vertex | mask(word[:j]), axis] for j, axis in enumerate(word)]
                term = rcomp(context, letters)
                assert path(context, term)[0] == tuple(edge[1] for edge in letters)
                paths[vertex, word] = term
                label = f"path-{vertex}-{word_name(word)}"
                checks.append((label, term, arrow(v(vertex), v(vertex | mask(word)))))

    squares = {}
    for vertex in range(8):
        for low, high in combinations(axes, 2):
            if not vertex & mask((low, high)):
                squares[vertex, low, high] = declare(
                    arrow(paths[vertex, (high, low)], paths[vertex, (low, high)]))

    def steps(vertex, word):
        """Every outgoing square instance, with its two path boundaries corrected."""
        for j, (high, low) in enumerate(zip(word, word[1:])):
            if high <= low:
                continue
            prefix, suffix = word[:j], word[j + 2:]
            after = prefix + (low, high) + suffix
            face = vertex | mask(prefix), low, high
            raw = squares[face]
            if prefix:
                raw = comp2(context, 0, paths[vertex, prefix], raw)
            if suffix:
                raw = comp2(context, 0, raw, paths[vertex | mask(word[:j + 2]), suffix])
            a, b = paths[vertex, word], paths[vertex, after]
            factors = []
            if a != src(context, raw):
                factors.append(kappa(context, a, src(context, raw)))
            factors.append(raw)
            if tgt(context, raw) != b:
                factors.append(kappa(context, tgt(context, raw), b))
            yield after, face, lfold(context, 1, factors)

    hemispheres = {}

    def extend(vertex, route, visited_faces, previous):
        start, word = route[0], route[-1]
        for after, face, step in steps(vertex, word):
            term = step if previous is None else comp2(context, 1, previous, step)
            faces = visited_faces + (face,)
            assert square_chain(term) == Counter(squares[f] for f in faces)
            if len(start) == 2:
                assert term == squares[face]
            new_route = (*route, after)
            label = f"route-{vertex}-" + "-".join(map(word_name, new_route))
            checks.append((label, term, arrow(paths[vertex, start], paths[vertex, after])))
            if len(faces) == 3:
                hemispheres[frozenset(faces)] = term
            extend(vertex, new_route, faces, term)

    for vertex, word in paths:
        extend(vertex, (word,), (), None)

    # The tensor differential is the alternating sum of upper minus lower faces.
    def face_set(positive):
        faces = set()
        for fixed in axes:
            low, high = [axis for axis in axes if axis != fixed]
            upper = positive ^ bool(fixed % 2)
            faces.add((int(upper) << fixed, low, high))
        return frozenset(faces)

    assert set(hemispheres) == {face_set(False), face_set(True)}
    top_type = arrow(hemispheres[face_set(False)], hemispheres[face_set(True)])
    checks.append(("cube", declare(top_type), top_type))
    check_ctx(context)
    assert len(context) == 27 and len(paths) == 30 and len(checks) == 30 + 18 + 1
    for _, term, expected in checks:
        assert infer(context, term) == expected
    return context, checks


if __name__ == '__main__':
    context, checks = build_cube()
    emitter = Emitter()
    for label, term, expected in checks:
        emitter.check_type(label, context, term, expected)
    module = emitter.module('CaTTExp.Generated.CanonicalGrayCube', 'From tools/canonical_gray_cube.py.')
    target = Path(__file__).resolve().parents[1] / 'src/CaTTExp/Generated/CanonicalGrayCube.agda'
    target.write_text(module)
    print(f'{target.name}: 27 declarations, 30 paths, 18 nonidentity 2-cells, 1 top cell.')
