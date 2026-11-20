"""Check the two signed face maps for the double shift and their CaTT square."""
import argparse
from collections import Counter
from itertools import product
from pathlib import Path

from canonical_gray_two_discs import strict_interpreter
from catt import comp2, infer, src, subst_tm, subst_ty, tgt, v
from emit_agda import Emitter
from gray_globe_comparison import atom, boundary, globe
from gray_globe_cubical_corner import map_rows
from gray_globe_double_shift import column, section
from gray_globe_exterior_actions import certificate
from gray_globe_factorizations import truncate
from gray_globe_pure_extension import raise_argument, two_by_two
from gray_globe_run_transport import peak, replace_tag
from gray_path_wedge import compose
from gray_globe_sector_terms import arrow, boundary_bridge, tile


def growth(g, axis, bound, sign):
    """Image of a basis element, with sign measured in the larger target."""
    if g[axis][0] != bound:
        return (g,)
    transverse, corner = g[1-axis]
    if transverse == 0:
        tag = corner if axis else corner ^ (bound % 2)
        return (replace_tag(g, axis, bound, tag),)
    signed = replace_tag(g, axis, bound, sign)
    if transverse > 1:
        return (signed,)
    if axis:
        pure = ((0, 1-sign), (bound+1, 2))
    else:
        pure = ((bound+1, 2), (0, sign ^ ((bound-1) % 2)))
    return (signed, pure)


def linear(chain, images):
    result = Counter()
    for g, coefficient in chain.items():
        for h, weight in images(g).items():
            result[h] += coefficient * weight
    return result


def raise_column(g, axis, bound):
    """Degree-one column homotopy for growth of a transverse globe."""
    if g[axis][0] != bound:
        return Counter()
    raised = list(g)
    raised[axis] = (bound+1, 2)
    coefficient = (-1)**g[0][0] if axis else 1
    return Counter({tuple(raised): coefficient})


def check_whisker(g, axis, bound, sign):
    native = atom(replace_tag(g, axis, bound, sign))
    side = 1-sign
    pole = truncate(native, bound, side)
    old, = (h for h in pole[-1][0] if h[axis][0] == bound)
    corner = list(old)
    corner[axis] = (bound+1, 2)
    pure = tuple(corner)
    ends = tuple(tuple(sorted(replace_tag(h, axis, bound, t) for h in pole[-1][0]))
                 for t in (0, 1))
    step = pole[:-1] + (ends, ((pure,), (pure,)))
    padded = step + (((), ()),) * (len(native)-len(step))
    before, after = (padded, native) if sign else (native, padded)
    assert compose(before, after, bound) == map_rows(atom(g), lambda h: growth(h, axis, bound, sign))


def check_strict(limit):
    instances = 0
    for m, n in product(range(1, limit+1), repeat=2):
        for axis, bound in enumerate((m, n)):
            for sign in (0, 1):
                def move(g):
                    return Counter(growth(g, axis, bound, sign))

                for g in product(globe(m), globe(n)):
                    assert linear(move(g), boundary) == linear(boundary(g), move)
                    # The next pair of parallel maps agree on this face.
                    sides = [linear(move(g), lambda h: Counter(growth(h, axis, bound+1, t)))
                             for t in (0, 1)]
                    assert sides[0] == sides[1]
                    for other in (0, 1):
                        def across(h):
                            return Counter(growth(h, 1-axis, (n, m)[axis], other))
                        assert linear(move(g), across) == linear(across(g), move)
                    def raise_transverse(h):
                        return raise_column(h, 1-axis, (n, m)[axis])
                    assert linear(move(g), raise_transverse) == linear(raise_transverse(g), move)
                    if g[axis][0] == bound and g[1-axis][0] > 0:
                        check_whisker(g, axis, bound, sign)
                    instances += 1

                larger = (m+1, n) if axis == 0 else (m, n+1)
                assert map_rows(peak(m, n)[:2], move) == peak(*larger)[:2]
                for g in product(globe(m-1), globe(n-1)):
                    native = Counter(column(m, n, g))
                    tag = 1-sign if axis else sign
                    signed = replace_tag(g, axis, bound-1, tag)
                    assert linear(native, move) == Counter(column(*larger, signed))

    # The two ordinary (2,2) faces of (3,2) meet at this lower vertex.
    vertex = atom(((0, 0), (0, 0)))
    shifted = section(2, 2, vertex)
    poles = [map_rows(shifted, lambda g: (replace_tag(g, 0, 2, s),)) for s in (0, 1)]
    assert poles[0] != poles[1]
    assert [tuple(g for g in c[2][0] if g[0][0] == 2) for c in poles] == [
        (((2, s), (0, 0)),) for s in (0, 1)]
    print(f'{instances} signed basis instances passed boundary, globularity and interchange checks; '
          f'shift squares passed through {limit} by {limit}.')


def strip_substitution(source, generators, target, names, axis, bound, sign):
    """Act on labels in the edge strip, also admitting unchanged deeper labels."""
    sigma = []
    evaluate = strict_interpreter(target, tuple(names))
    for g, ty in zip(generators, source):
        wanted = subst_ty(ty, sigma)
        chain = growth(g, axis, bound, sign)
        if len(chain) == 1:
            term = names[chain[0]]
        else:
            native, pure = (names[h] for h in chain)
            _, _, old_source, old_target = infer(target, native)
            new_source, new_target = wanted[2:]
            change_from = infer(target, pure)[2]
            if new_source != old_source:
                assert new_target == old_target
                step = raise_argument(target, new_source, change_from, pure)
                term = comp2(target, bound, step, native)
            else:
                assert new_target != old_target
                step = raise_argument(target, old_target, change_from, pure)
                term = comp2(target, bound, native, step)
        assert infer(target, term) == wanted
        assert evaluate(term) == map_rows(atom(g), lambda h: growth(h, axis, bound, sign))
        sigma.append(term)
    return tuple(sigma)


def check_terms(height, emitter):
    labels_checked = 0
    for axis, sign in product((0, 1), repeat=2):
        source, generators, _ = tile(height, axis)
        target, labels, _ = tile(height+1, axis)
        names = {g: v(i) for i, g in enumerate(labels)}
        sigma = strip_substitution(source, generators, target, names, axis, height, sign)
        labels_checked += len(sigma)

    target, names, _ = two_by_two()
    certify = certificate(emitter, target) if emitter else None
    evaluate = strict_interpreter(target, tuple(names))
    for left, right in product((0, 1), repeat=2):
        paths = []
        for axis in (0, 1):
            signs = (left, right)
            square_context, generators, _ = tile(1, axis)
            middle, mids, _ = tile(2, axis)
            mid_names = {g: v(i) for i, g in enumerate(mids)}
            first = strip_substitution(square_context, generators, middle, mid_names, axis, 1, signs[axis])
            # Only the first image's dependency closure is needed. Its only
            # label of rank two is the pure corner, never the mixed (2,1) tile.
            top = first[generators.index(((1, 2), (1, 2)))]
            assert tuple(rank for rank, _ in mids[-1])[axis] == 2
            assert sum(rank for rank, _ in mids[-1]) == 3
            second = strip_substitution(middle[:-1], mids[:-1], target, names,
                                        1-axis, 1, signs[1-axis])
            paths.append(subst_tm(top, second))

        a, b = paths
        assert a != b and infer(target, a) == infer(target, b)
        assert evaluate(a) == evaluate(b) and len(evaluate(a)[-1][0]) == 3
        for s, t in ((a, b), (b, a)):
            proof = boundary_bridge(target, evaluate, names, s, t)
            wanted = arrow(target, s, t)
            assert infer(target, proof) == wanted
            assert evaluate(proof) == evaluate(s) + (((), ()),)
            if certify:
                direction = 'forward' if s == a else 'back'
                certify(f'square-{left}-{right}-{direction}', proof, wanted)
    for axis, sign in product((0, 1), repeat=2):
        source, generators, _ = tile(2, 1-axis)
        g = generators[-1]
        assert (g[axis][0], g[1-axis][0]) == (1, 2)
        sigma = strip_substitution(source[:-1], generators[:-1], target, names, axis, 1, sign)
        wanted = subst_ty(source[-1], sigma)
        native = names[replace_tag(g, axis, 1, sign)]
        pure = names[((0, 1-sign), (2, 2)) if axis else ((2, 2), (0, sign))]
        if sign:
            start = src(target, wanted[2])
            step = raise_argument(target, start, src(target, pure), pure)
            direct = comp2(target, 1, step, native)
        else:
            end = tgt(target, tgt(target, native))
            step = raise_argument(target, end, src(target, pure), pure)
            direct = comp2(target, 1, native, step)
        initial = boundary_bridge(target, evaluate, names, wanted[2], src(target, direct))
        final = boundary_bridge(target, evaluate, names, tgt(target, direct), wanted[3])
        result = comp2(target, 2, comp2(target, 2, initial, direct), final)
        assert infer(target, result) == wanted
        assert evaluate(result) == map_rows(atom(g), lambda h: growth(h, axis, 1, sign))
        if certify:
            certify(f'transverse-two-{axis}-{sign}', result, wanted)
    print(f'{labels_checked} strip labels typed at bound {height}; '
          'eight square comparisons and four transverse-rank-two images typed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bound', type=int)
    parser.add_argument('--strip', type=int, default=3)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if min(args.bound, args.strip) < 1:
        parser.error('expected positive bounds')
    check_strict(args.bound)
    emitter = Emitter() if args.agda else None
    check_terms(args.strip, emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Comparing the two shifted face orders.'))
