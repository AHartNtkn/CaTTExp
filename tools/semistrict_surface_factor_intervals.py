"""Lift literal CaTT queries at two-sided path factorizations, including a bicyclic cut."""
from argparse import ArgumentParser
from functools import cache
from itertools import permutations, product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, fv_tm, fv_ty, infer, restrict, subst_tm, subst_ty, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_return_edges import attachment, check_native_square, clamp
from semistrict_surface_weighted_arity_cover import poles


class Placement:
    """Build just the dependency-closed part used by the requested lifts."""

    def __init__(self, ctx, edges, unit, multiply):
        self.ctx, self.unit, self.mul = ctx, unit, multiply
        self.tags = {}
        self.copies, self.declarations, self.fold = {}, [], []
        for i, ty in enumerate(ctx):
            if ty == STAR:
                self.tags[i] = unit
            elif ty[1] == STAR:
                self.tags[i] = edges[i]
            else:
                self.tags[i] = self.tag(ty[2])
                assert self.tags[i] == self.tag(ty[3])

    @cache
    def spine(self, term):
        _, arity, ty, labels = term
        vertices = [i for i, t in enumerate(arity) if t == STAR]
        by_source = {}
        for entry, label in zip(arity, labels, strict=True):
            if entry != STAR and entry[1] == STAR:
                s, t = poles(entry)
                branch = (t, self.tag(label))
                assert by_source.setdefault(s, branch) == branch
        assert poles(ty) == (vertices[0], vertices[-1])
        before, after = {vertices[0]: self.unit}, {vertices[-1]: self.unit}
        for s, t in zip(vertices, vertices[1:]):
            end, value = by_source[s]
            assert end == t
            before[t] = self.mul(before[s], value)
        for s in reversed(vertices[:-1]):
            end, value = by_source[s]
            after[s] = self.mul(value, after[end])
        return before, after

    @cache
    def tag(self, term):
        if term[0] == 'v':
            return self.tags[term[1]]
        before, _ = self.spine(term)
        return before[poles(term[2])[1]]

    @cache
    def lift(self, term, left, right):
        if term[0] == 'v':
            i = term[1]
            ty = self.lift_type(self.ctx[i], self.tags[i], left, right)
            index = len(self.declarations)
            self.declarations.append(ty)
            self.fold.append(term)
            self.copies[index] = (i, left, right)
            return v(index)
        _, arity, ty, labels = term
        before, after = self.spine(term)
        placed = []
        for i, (entry, label) in enumerate(zip(arity, labels, strict=True)):
            s, t = (i, i) if entry == STAR else poles(entry)
            placed.append(self.lift(label, self.mul(left, before[s]), self.mul(after[t], right)))
        return 'coh', arity, ty, tuple(placed)

    def lift_type(self, ty, value, left, right):
        if ty == STAR:
            return STAR
        if ty[1] == STAR:
            return arr(STAR, self.lift(ty[2], left, self.mul(value, right)),
                       self.lift(ty[3], self.mul(left, value), right))
        return arr(self.lift_type(ty[1], value, left, right),
                   self.lift(ty[2], left, right), self.lift(ty[3], left, right))

    def check(self, term, left, right):
        placed = self.lift(term, left, right)
        expected = self.lift_type(infer(self.ctx, term), self.tag(term), left, right)
        assert infer(tuple(self.declarations), placed) == expected
        assert subst_tm(placed, tuple(self.fold)) == term
        return placed

    def verify_context(self):
        check_ctx(tuple(self.declarations))
        for ty, term in zip(self.declarations, self.fold, strict=True):
            assert subst_ty(ty, tuple(self.fold)) == self.ctx[term[1]]


def extension():
    ctx, words = attachment()

    def declare(ty):
        nonlocal ctx
        name = v(len(ctx))
        ctx += (ty,)
        return name

    x, y, forward = v(0), v(1), v(2)
    p, q = (declare(arr(STAR, x, x)) for _ in range(2))
    back = declare(arr(STAR, y, x))
    data = [(comp2(ctx, 0, p, q), identity(ctx, x)),
            (comp2(ctx, 0, q, p), comp2(ctx, 0, forward, back)),
            (comp2(ctx, 0, back, forward), identity(ctx, y))]
    guards = [declare(arr(infer(ctx, a), a, b)) for a, b in data]
    return ctx, words, (p, q, back), guards


def bicyclic(a, b):
    matched = min(a[1], b[0])
    return a[0] + b[0] - matched, a[1] + b[1] - matched


def cut_substitution(chart):
    bare, base_labels = clamp()
    result = []
    for i, lifted_type in enumerate(chart.declarations):
        old, left, _ = chart.copies[i]
        start = int(left[0] > 0)
        end = int(bicyclic(left, chart.tags[old])[0] > 0)
        expected = subst_ty(lifted_type, result)
        if expected == STAR:
            term = base_labels[start]
        elif start < end and old < len(base_labels):
            term = base_labels[old]
        elif expected[1] == STAR:
            term = base_labels[2] if start < end else identity(bare, base_labels[start])
        else:
            # All other higher declarations collapse to a structural comparison on a point or edge.
            support = set(fv_ty(expected))
            for j in reversed(range(len(bare))):
                if j in support:
                    support.update(fv_ty(bare[j]))
            arity, inclusion = restrict(bare, support)
            assert len(arity) in (1, 3)
            renaming = {entry[1]: v(j) for j, entry in enumerate(inclusion)}
            term = 'coh', arity, subst_ty(expected, renaming), inclusion
        assert infer(bare, term) == expected
        result.append(term)
    return bare, tuple(result)


def cut_check(emitter):
    ctx, words, (p, q, back), guards = extension()
    one, down, up = (0, 0), (1, 0), (0, 1)
    tags = {i: down for i in range(2, 6)}
    tags.update({p[1]: up, q[1]: down, back[1]: up})
    chart = Placement(ctx, tags, one, bicyclic)
    u, vterm = (chart.check(t, one, one) for t in words)
    # Place each guard at every sampled valid frame over the same query.
    values = list(product(range(4), repeat=2))
    count = 0
    for term, left, right in product(guards, values, values):
        if bicyclic(bicyclic(left, chart.tag(term)), right) == down:
            chart.check(term, left, right)
            count += 1
    chart.verify_context()
    for i, (old, before, _) in chart.copies.items():
        if ctx[old] == STAR or ctx[old][1] != STAR:
            continue
        source, target = poles(chart.declarations[i])
        assert chart.copies[source][1] == before
        assert (before[0] > 0) <= (chart.copies[target][1][0] > 0)
    ty = arr(infer(tuple(chart.declarations), u), u, vterm)
    assert subst_ty(ty, tuple(chart.fold)) == arr(infer(ctx, words[0]), *words)
    bare, assignment = cut_substitution(chart)
    _, original_clamp = clamp()
    assert tuple(subst_tm(t, assignment) for t in (u, vterm)) == tuple(
        subst_tm(t, original_clamp) for t in words)
    emitter.check_typed('leftSchedule', ctx, words[0])
    emitter.check_typed('rightSchedule', ctx, words[1])
    for j, term in enumerate(guards):
        emitter.check_typed(f'guard{j}', ctx, term)
    for i, (old, _, _) in chart.copies.items():
        if v(old) in guards:
            emitter.check_type(f'placedGuard{i}', bare, assignment[i],
                               subst_ty(chart.declarations[i], assignment))
    for j, term in enumerate((u, vterm)):
        # Every higher dependency precedes this prefix; its typing also holds in the full chart.
        emitter.check_typed(f'placed{j}', tuple(chart.declarations[:max(fv_tm(term))+1]), term)
    return count


def finite_check():
    # Exhaust all functions on two points, including the constants.
    functions = list(product(range(2), repeat=2))
    unit = (0, 1)

    def compose(a, b):
        return tuple(b[i] for i in a)

    ctx, words = attachment()
    count = 0
    for tag in functions:
        chart = Placement(ctx, {i: tag for i in range(2, 6)}, unit, compose)
        for left, right in product(functions, repeat=2):
            for term in words:
                chart.check(term, left, right)
                count += 1
        chart.verify_context()

    # Independently replay noncommuting edge products on a three-edge raw word.
    ctx = (STAR,) + (arr(STAR, v(0), v(0)),)*3
    word = comp2(ctx, 0, v(1), comp2(ctx, 0, v(2), v(3)))
    for a, b, c in product(functions, repeat=3):
        chart = Placement(ctx, {1: a, 2: b, 3: c}, unit, compose)
        chart.check(word, unit, unit)
        frames = set(chart.copies.values())
        assert {(1, unit, compose(b, c)), (2, a, c), (3, compose(a, b), unit)} <= frames
        chart.verify_context()
    return count


def degree_six_chart(emitter):
    # Recognize a b^+ on a one-object graph with no nonzero additive edge grading.
    source = (STAR,) + (arr(STAR, v(0), v(0)),)*2
    a, b = v(1), v(2)
    ab, ba = comp2(source, 0, a, b), comp2(source, 0, b, a)
    def declare(left, right):
        nonlocal source
        term = v(len(source))
        assert infer(source, left) == infer(source, right)
        source += (arr(infer(source, left), left, right),)
        return term

    rule = declare(ab, comp2(source, 0, ab, b))
    hidden = declare(ba, comp2(source, 0, ba, a))
    hidden_change = declare(hidden, hidden)
    stationary = identity(source, rule)
    k = declare(stationary, stationary)
    z = declare(k, k)
    top = declare(z, z)

    def then(f, g):
        return tuple(g[i] for i in f)

    letters = {1: (1, 3, 3, 3), 2: (3, 2, 2, 3)}
    unit = tuple(range(4))
    monoid, pending = {unit}, [unit]
    while pending:
        start = pending.pop()
        for letter in letters.values():
            end = then(start, letter)
            if end not in monoid:
                monoid.add(end)
                pending.append(end)
    chart = Placement(source, letters, unit, then)
    width = chart.tag(ab)
    active = set()
    for i, left, right in product(range(len(source)), monoid, monoid):
        end = then(left, chart.tags[i])
        if then(end, right) == width:
            chart.check(v(i), left, right)
            assert left[0] != 3 and end[0] != 3
            assert (left[0] != 0) <= (end[0] != 0)
            if i > 2:
                assert left[0] == 0 and end[0] != 0
                active.add(v(i))
    assert active == {rule, k, z, top}
    assert {hidden, hidden_change}.isdisjoint(active)
    chart.verify_context()
    lifted = chart.check(top, unit, unit)
    emitter.check_typed('crossingSix', tuple(chart.declarations), lifted)
    return len(monoid), len(chart.declarations)


def split_maps():
    group = list(permutations(range(3)))
    points = list(product(group, range(2)))
    def then(f, g):
        return tuple(g[i] for i in f)

    action = {g: tuple(points.index((then(h, g), y)) for h, y in points) for g in group}
    for h, g in product(group, repeat=2):
        assert then(action[h], action[g]) == action[then(h, g)]
    a = tuple(points.index((tuple(range(3)), y)) for y in range(2))
    for u, vword in product(group, repeat=2):
        b = tuple(y if h == vword else 0 for h, y in points)
        f = (0, 1) if u == vword else (0, 0)
        r = tuple(sorted(set(f)))
        assert then(then(a, action[vword]), b) == (0, 1)
        assert then(then(a, action[u]), b) == then(f, r)
        assert then(r, f) == tuple(range(len(r)))
        assert (len(set(f)) == 2) == (u == vword)
    return len(group)**2


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    guards = cut_check(emitter)
    print(f'{guards} bicyclic guard placements, {finite_check()} finite schedule placements, '
          'and all 64 three-edge products checked.')
    size, copies = degree_six_chart(emitter)
    print(f'Degree-six query: {size} transition maps, {copies} lifted declarations, '
          'all active declarations cross the cut and none has degree three.')
    print(f'{split_maps()} pairs in the finite group split-map construction checked.')
    check_native_square()
    print('The native bare square has only its forward comparison.')
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = 'FactorIntervalChecks'
        (args.agda_dir / f'{module}.agda').write_text(emitter.module(module, __doc__).replace(
            'open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure'))
