"""Check the common middle parameter for the two mixed end decompositions."""
import argparse
from collections import Counter, defaultdict
from functools import cache
from itertools import product
from pathlib import Path

from catt import comp2, infer, maximal_vars, src, tgt, v
from emit_agda import Emitter
from gray_globe_comparison import boundary, globe
from gray_globe_cubical_corner import cube_label, projected_chain
from gray_globe_end_charts import peel, span
from gray_globe_exterior_actions import arity, certificate
from gray_globe_factorizations import truncate
from gray_globe_pure_extension import raise_argument
from gray_globe_run_transport import box, peak, replace_tag, restrict
from gray_globe_section import cells
from gray_globe_sector_terms import arrow
from gray_globe_strip_squares import chart_lift


def full_state(m, n, k, bits):
    chain = projected_chain(m, n, m+n-k, cube_label(bits))
    return peak(m, n)[:k] + ((chain, chain),)


def native_part(ambient, k, part):
    """Recover the input and the signed inclusion used by its unary operation."""
    m, n = ambient
    lo, hi = span(part, k)
    bounds = box(m, n, k-1, lo, hi)
    source, target = (truncate(part, k-1, side) for side in (0, 1))
    tags = tuple(next((g[axis][1] for g in source[-1][0] if g[axis][0] == bound), 2)
                 for axis, bound in enumerate(bounds))

    def embed(g):
        return replace_tag(replace_tag(g, 0, bounds[0], tags[0]), 1, bounds[1], tags[1])

    value = restrict(part, m, n, k-1, lo, hi)
    operation = (ambient, (lo, hi), source, target, tags)
    return operation, value, bounds, embed


def writing(ambient, k, state, first, last):
    """Describe the nested operations, recording a hole in place of the middle input."""
    factors, at = peel(state, k, first)
    outer, retained, smaller, include_outer = native_part(ambient, k, factors[at])
    fixed, fixed_atom, _, _ = native_part(ambient, k, factors[1-at])
    inner_factors, middle_at = peel(retained, k, last)
    inner, middle, bounds, include_inner = native_part(smaller, k, inner_factors[middle_at])
    other, other_atom, _, _ = native_part(smaller, k, inner_factors[1-middle_at])
    assert fixed_atom == peak(*box(*ambient, k-1, first, first))
    assert other_atom == peak(*box(*smaller, k-1, last, last))
    signature = (at, fixed, outer, middle_at, other, inner)
    return signature, middle, bounds, lambda g: include_outer(include_inner(g))


@cache
def closure(g):
    return frozenset((g,)).union(*(closure(facet) for facet in boundary(g)))


def check_intersections(ends, middle_faces, outer_faces, k, h, signs):
    left, right = (closure(g) for g in ends)
    middle = frozenset().union(*(closure(g) for side in middle_faces for g in side))
    def common_facet(a, b, dim):
        shared = a & b
        top, = (g for g in shared if sum(r for r, _ in g) == dim)
        assert shared == closure(top)
        return shared
    left_facet = common_facet(left, middle, k-1)
    right_facet = common_facet(middle, right, k-1)
    assert common_facet(left, right, k-h) == left_facet & right_facet
    support = left | middle | right
    assert all(g in support for row in outer_faces for side in row for g in side)
    for side, facets in enumerate(middle_faces):
        shared = sum(g in left_facet or g in right_facet for g in facets)
        # If the first bit is zero the left arm feeds the middle. If the last
        # bit is one the right arm feeds it. The two junctions are distinct.
        assert shared == int(signs[0] == side) + int(signs[1] != side)
        assert len(facets) == h


def check_box(m, n, k, independent):
    h = m+n-k
    first, last = k-n, m
    classes = defaultdict(set)
    poles = peak(m-1, n-1)[k-1]
    all_states = set()
    expected_orders = {
        (0, 0): ('LMR', 'LMR'),
        (0, 1): ('LRM', 'RLM'),
        (1, 0): ('MRL', 'MLR'),
        (1, 1): ('RML', 'RML'),
    }
    for bits in product((0, 1), repeat=h):
        state = full_state(m, n, k, bits)
        all_states.add(state)
        a, p, bounds, f = writing((m, n), k, state, first, last)
        b, q, other_bounds, g = writing((m, n), k, state, last, first)
        assert bounds == other_bounds == (m-1, n-1)
        assert p == q == full_state(*bounds, k, bits[1:-1])
        signs = bits[0], bits[-1]
        for description, outer, inner, expected in zip(
                (a, b), 'LR', 'RL', expected_orders[signs], strict=True):
            at, _, _, middle_at, _, _ = description
            nested = inner+'M' if middle_at else 'M'+inner
            assert (outer+nested if at else nested+outer) == expected
        # Extract the actual signs on both native globe bounds.
        expected_left = bits[-1]
        expected_right = bits[0] ^ ((first+1) % 2)
        for label in product(globe(m-1), globe(n-1)):
            expected = replace_tag(replace_tag(label, 0, m-1, expected_left), 1, n-1, expected_right)
            assert f(label) == g(label) == expected
        end_labels = (state[k][0][0], state[k][0][-1])
        assert tuple(map(f, p[k][0])) == state[k][0][1:-1]
        # Differential and both poles for the formal three-generator cell.
        central_boundary = Counter(map(f, poles[1]))
        central_boundary.subtract(map(f, poles[0]))
        total = central_boundary.copy()
        for label in end_labels:
            total.update(boundary(label))
        outer_boundary = Counter(state[k-1][1])
        outer_boundary.subtract(state[k-1][0])
        assert total == outer_boundary
        if not classes[signs]:
            check_intersections(end_labels, [tuple(map(f, side)) for side in poles], state[:k], k, h, signs)
        # At this insertion point every negative facet precedes every positive
        # facet in the lexicographic strong Steiner order on the rectangle.
        def order_key(label):
            (i, x), (j, y) = label
            left = i if x != 1 else 2*m-i
            right = j if y != 1 else 2*n-j
            return left, -right if i % 2 else right
        assert max(order_key(f(t)) for t in poles[0]) < min(order_key(f(t)) for t in poles[1])
        classes[bits[0], bits[-1]].add((a, b, end_labels, expected_left, expected_right))
    if independent is not None:
        assert all_states == {c for c in independent if len(c) == k+1 and len(c[k][0]) == h+1}
    assert len(classes) == 4 and all(len(items) == 1 for items in classes.values())
    return 2**h, len(classes)


def check(limit):
    totals = Counter()
    for m, n in product(range(3, limit+1), repeat=2):
        independent = cells((m, n)) if max(m, n) <= 5 else None
        for k in range(max(m, n)+1, m+n-1):
            states, charts = check_box(m, n, k, independent)
            totals['states'] += states
            totals['charts'] += charts
            totals['boxes and degrees'] += 1
    print(f'Bounds through {limit}: {dict(totals)}.')


def change_example(emitter):
    """Change the middle input in a comparison of the two ternary bracketings."""
    k = 3
    ctx = arity(k-1, (k, k+2, k))
    left, top, right = (v(i) for i in maximal_vars(ctx))
    certify = certificate(emitter, ctx) if emitter else None

    @cache
    def comparison(slot, level):
        if level == 0:
            a = comp2(ctx, k-1, comp2(ctx, k-1, left, slot), right)
            b = comp2(ctx, k-1, left, comp2(ctx, k-1, slot, right))
        else:
            x, y = src(ctx, slot), tgt(ctx, slot)
            e0, e1 = comparison(x, level-1), comparison(y, level-1)
            d = k+level-1
            a = comp2(ctx, d, e0, raise_argument(ctx, tgt(ctx, e0), x, slot))
            b = comp2(ctx, d, raise_argument(ctx, src(ctx, e0), x, slot), e1)
        result = chart_lift(ctx, (left, slot, right), k-1, a, b)
        assert infer(ctx, result) == arrow(ctx, a, b)
        if certify:
            certify(f'change-{level}-{slot[1]}', result, arrow(ctx, a, b))
        return result

    comparison(top, 2)
    print('Checked changes of the open comparison through degree six.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bound', type=int)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.bound < 3:
        parser.error('mixed end tests start at bound three')
    check(args.bound)
    emitter = Emitter() if args.agda else None
    change_example(emitter)
    if emitter:
        args.agda.write_text(emitter.module(args.agda.stem, 'Changing the middle in a ternary comparison.'))
