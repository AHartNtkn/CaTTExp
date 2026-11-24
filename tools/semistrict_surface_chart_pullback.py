"""Compute the common raw algebra of two labelled computads and test globular frame changes."""
from functools import lru_cache
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, check_ty_cached, comp2, infer, subst_tm, subst_ty, tdim_tm, v
from ct_suspension import ident
from semistrict_surface_boundary_tracks import inverse_terms, pattern, specialize
from semistrict_surface_exact_boundary import accepted, run
from semistrict_surface_insertion_cut import Assertions


class ChartPullback:
    def __init__(self, left, right):
        p, sigma = left
        q, tau = right
        p_inv, q_inv = inverse_terms(p, sigma), inverse_terms(q, tau)
        atoms = {(v(i), t) for i, image in enumerate(sigma) for t in q_inv(image)}
        atoms.update((s, v(i)) for i, image in enumerate(tau) for s in p_inv(image))
        self.generators = sorted(atoms, key=lambda a: (tdim_tm(p, a[0]), a))
        self.variables = {a: v(i) for i, a in enumerate(self.generators)}
        declarations = []
        for s, t in self.generators:
            ty = self.pair_type(infer(p, s), infer(q, t))
            check_ty_cached(tuple(declarations), ty)
            declarations.append(ty)
        self.ctx = tuple(declarations)
        self.projections = tuple(tuple(a[i] for a in self.generators) for i in range(2))
        for i, (s, t) in enumerate(self.generators):
            assert all(subst_ty(self.ctx[i], lab) == infer(ctx, term) for lab, ctx, term in
                       zip(self.projections, (p, q), (s, t), strict=True))
            assert subst_tm(s, sigma) == subst_tm(t, tau)

    def pair_term(self, s, t):
        if s[0] == 'v' or t[0] == 'v':
            return self.variables[s, t]
        if s[:3] != t[:3]:
            raise ValueError('terms have different generic heads')
        inputs = tuple(self.pair_term(a, b) for a, b in zip(s[3], t[3], strict=True))
        return (*s[:3], inputs)

    def pair_type(self, a, b):
        if a == STAR or b == STAR:
            if a != b:
                raise ValueError('types have different dimensions')
            return STAR
        return arr(self.pair_type(a[1], b[1]), self.pair_term(a[2], b[2]), self.pair_term(a[3], b[3]))


def frame_path(charts, domains, old_frames, same_class):
    """Find compatible lower-frame choices at all junctions, or return None."""
    if len(domains) != len(charts) or len(charts) != len(old_frames) + 1:
        raise ValueError('one frame domain per junction and one old pair per step required')
    layers = [dict.fromkeys(domains[0])]
    for i, old in enumerate(old_frames):
        common = ChartPullback(charts[i], charts[i+1])
        old_pair = common.pair_type(*old)
        parents = {}
        for nxt in domains[i+1]:
            for prev in layers[-1]:
                if same_class(common.ctx, old_pair, common.pair_type(prev, nxt)):
                    parents[nxt] = prev
                    break
        if not parents:
            return None
        layers.append(parents)
    if not layers[-1]:
        return None
    solution = [next(iter(layers[-1]))]
    for parents in reversed(layers[1:]):
        solution.append(parents[solution[-1]])
    return tuple(reversed(solution))


def type_equality(binary, width):
    @lru_cache(None)
    def same(ctx, a, b):
        if a == b:
            return True
        if STAR in (a, b) or not same(ctx, a[1], b[1]):
            return False
        code = Assertions()

        def show(ty):
            return '*' if ty == STAR else ' -> '.join(code.term(t) for t in ty[2:])

        decl = ' '.join(f'(x{i} : {show(ty)})' for i, ty in enumerate(ctx))
        checks = [f'assert {code.term(s)} = {code.term(t)} in {decl}' for s, t in zip(a[2:], b[2:], strict=True)]
        with TemporaryDirectory() as tmp:
            directory = Path(tmp)
            (directory/'Types.catt').write_text('\n'.join(code.commands + checks) + '\n')
            output = run(binary, directory, 'Types.catt', ['--insertion-width', str(width)])
        if 'Error: Assertion failed:' in output and 'are not equal' in output:
            return False
        accepted(output, 'Types.catt', [])
        assert output.count('are equal') == len(checks)
        return True
    return same


def folded_edges(binary):
    edge, (x,) = pattern([1])
    pt = (STAR,)
    chart = edge, specialize(edge, pt, (ident(pt, v(0)),))
    square = ChartPullback(chart, chart)
    assert len(square.ctx) == 9   # four vertices, four side edges and one diagonal
    # Each chart sees the same edge by units. The two common paths instead
    # follow opposite sides of the square of atom pairs.
    left_unit = comp2(edge, 0, ident(edge, v(0)), x)
    right_unit = comp2(edge, 0, x, ident(edge, v(1)))
    def parallel(t):
        return arr(infer(edge, t), t, t)
    a, b = parallel(right_unit), parallel(left_unit)
    same = type_equality(binary, 2)
    assert same(edge, a, b)
    paths = [square.pair_term(s, t) for s, t in ((right_unit, left_unit), (left_unit, right_unit))]
    sides = [[arg for arg in path[3] if tdim_tm(square.ctx, arg) == 1] for path in paths]
    assert len(set(sides[0] + sides[1])) == 4
    assert frame_path((chart, chart), ((b,), (a,)), ((a, b),), same) is None
    assert frame_path((chart, chart), ((b, a), (a, b)), ((a, b),), same) == (a, b)
    for (s, t), term in zip(((right_unit, left_unit), (left_unit, right_unit)), paths, strict=True):
        assert tuple(subst_tm(term, p) for p in square.projections) == (s, t)
        assert subst_tm(s, chart[1]) == subst_tm(t, chart[1])


def check_path_charts():
    """Compare reconstruction with bounded raw enumeration and count paths in positive pullbacks."""
    from collections import defaultdict
    from itertools import product

    ambient = (STAR, arr(STAR, v(0), v(0)))
    a = v(1)
    unit = ident(ambient, v(0))
    aa = comp2(ambient, 0, a, a)
    choices = (a, aa, comp2(ambient, 0, aa, a), comp2(ambient, 0, a, aa),
               comp2(ambient, 0, a, unit), unit)
    charts = []
    for length in (1, 2):
        ctx, slots = pattern([1] * length)
        identities = [ident(ctx, v(i)) for i, ty in enumerate(ctx) if ty == STAR]
        simple = [*slots, *identities]
        pool = [*simple, *(comp2(ctx, 0, s, t) for s, t in product(simple, repeat=2)
                           if infer(ctx, s)[3] == infer(ctx, t)[2])]
        for assignment in product(choices, repeat=length):
            lab = specialize(ctx, ambient, assignment)
            by_image = defaultdict(list)
            for t in pool:
                by_image[subst_tm(t, lab)].append(t)
            charts.append(((ctx, lab), by_image, unit not in assignment))
    positive = pairs = 0
    for (chart1, images1, pos1), (chart2, images2, pos2) in product(charts, repeat=2):
        common = ChartPullback(chart1, chart2)
        for image in images1.keys() & images2.keys():
            for s, t in product(images1[image], images2[image]):
                lifted = common.pair_term(s, t)
                assert infer(common.ctx, lifted) == common.pair_type(infer(chart1[0], s), infer(chart2[0], t))
                assert tuple(subst_tm(lifted, p) for p in common.projections) == (s, t)
                pairs += 1
        if pos1 and pos2:
            # On two linear charts the projected paths are determined by their
            # endpoints. Count paths directly, including possible parallel edges.
            successors = defaultdict(list)
            for ty in common.ctx:
                if ty != STAR:
                    successors[ty[2]].append(ty[3])
            for i, ty in enumerate(common.ctx):
                if ty != STAR:
                    continue
                pending = [v(i)]
                reached = set()
                while pending:
                    vertex = pending.pop()
                    assert vertex not in reached
                    reached.add(vertex)
                    pending.extend(successors[vertex])
            positive += 1
    return len(charts) ** 2, pairs, positive


def mixed_leg(rank, binary):
    """A folded generating relabelling against a substitution by a spatial composite."""
    from semistrict_surface_boundary_tracks import bracket
    ambient, (f, z, h) = pattern([1, rank, 1])
    p = (*ambient, infer(ambient, z))
    zp = v(len(ambient))
    alpha = (*map(v, range(len(ambient))), z)
    row, (y, tail) = pattern([rank, 1])
    q = (*row, infer(row, y))
    yp = v(len(row))
    inner = comp2(ambient, 0, f, z)
    beta = (*specialize(row, ambient, (inner, h)), inner)
    common = ChartPullback((p, alpha), (q, beta))
    assert all(t[0] == 'v' for _, t in common.generators)
    same = type_equality(binary, rank)
    terms = []
    for central in (z, zp):
        first = bracket(p, (f, central, h), 'left')
        for token in (y, yp):
            second = comp2(q, 0, token, tail)
            term = common.pair_term(first, second)
            terms.append(term)
            terms.append(comp2(common.ctx, rank-1, term, ident(common.ctx, infer(common.ctx, term)[3])))
    matches = set()
    for i, s in enumerate(terms):
        for t in terms[i:]:
            a, b = (arr(infer(common.ctx, x), x, x) for x in (s, t))
            observed = tuple(same(c, subst_ty(a, lab), subst_ty(b, lab))
                             for c, lab in zip((p, q), common.projections, strict=True))
            assert same(common.ctx, a, b) == all(observed)
            matches.add(observed)
    assert len(matches) == 4
