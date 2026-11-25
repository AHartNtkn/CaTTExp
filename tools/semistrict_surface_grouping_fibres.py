"""Compute first-rank grouping counts and check spatial groupings in Catt_sua."""
from argparse import ArgumentParser
from functools import cache
from itertools import combinations, permutations
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, chain_tree, comp2, disc_tree, maximal_vars, src, sub_from,
                  subst_tm, subst_ty, tdim, tdim_tm, tgt, tree_ctx, ucomp, v)
from ct_suspension import ident, susp_ctx, susp_tm
from relative_coherence_exchange_faces import head
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_insertion_cut import Assertions, shape, variables
from semistrict_surface_equal_rank import suspend
from semistrict_surface_rank_cut import RankCut


def compatible(left, right):
    i, j = left
    k, l = right
    return not (i < k < j < l or k < i < l < j)


def count_readings(length, allowed):
    def forests(i, j):
        choices = 2 if (i, j) in allowed else 1
        return choices * proper(i, j)

    @cache
    def proper(i, j):
        if j == i + 1:
            return 1
        count = forests(i + 1, j)
        for k in range(i + 2, j):
            if (i, k) in allowed:
                count += proper(i, k) * forests(k, j)
        return count

    return proper(0, length)


def tree_readings(i, j):
    """Generate plane trees by ordered children, independently of interval tests."""
    if j == i + 1:
        yield frozenset()
        return
    for cuts in range(1, j - i):
        for seams in combinations(range(i + 1, j), cuts):
            families = [frozenset()]
            for a, b in zip((i,) + seams, seams + (j,), strict=True):
                edge = {(a, b)} if b > a + 1 else set()
                families = [old | inside | edge for inside in tree_readings(a, b) for old in families]
            yield from families


def count_tests():
    total = 0
    for n in range(2, 6):
        intervals = [(i, j) for i in range(n) for j in range(i + 2, n + 1) if j - i < n]
        trees = set(tree_readings(0, n))
        for mask in range(1 << len(intervals)):
            allowed = {item for k, item in enumerate(intervals) if mask >> k & 1}
            assert count_readings(n, allowed) == sum(t <= allowed for t in trees)
            assert (frozenset(allowed) in trees) == all(compatible(a, b) for a, b in combinations(allowed, 2))
            total += 1
    return total


RANK = 3
NCOLS = 5


def columns(n):
    return tree_ctx((disc_tree(RANK - 1),) * n)


def children(i, j, brackets):
    pos = i
    while pos < j:
        end = max((b for a, b in brackets if a == pos and b <= j and (a, b) != (i, j)),
                  default=pos + 1)
        yield pos, end
        pos = end


def reading(ty, brackets):
    """Collapse each maximal block to its first tip and insert its grouped label."""
    flat = columns(NCOLS)
    tips = [v(i) for i in maximal_vars(flat)]

    def block(i, j):
        if j == i + 1:
            return tips[i]
        parts = list(children(i, j, brackets))
        ctx = columns(len(parts))
        labels = sub_from(ctx, flat, {k: block(a, b) for k, (a, b) in zip(maximal_vars(ctx), parts, strict=True)})
        return ('coh', ctx, ucomp(ctx)[2], labels)

    parts = list(children(0, NCOLS, brackets))
    outer = columns(len(parts))
    collapsed = {}
    for k, (i, j) in zip(maximal_vars(outer), parts, strict=True):
        collapsed[maximal_vars(flat)[i]] = v(k)
        pole = v(k)
        for _ in range(RANK):
            pole = tgt(outer, pole)
        unit = pole
        for _ in range(RANK):
            unit = ident(outer, unit)
        for n in range(i + 1, j):
            collapsed[maximal_vars(flat)[n]] = unit
    restricted = subst_ty(ty, sub_from(flat, outer, collapsed))
    labels = sub_from(outer, flat, {k: block(a, b) for k, (a, b) in zip(maximal_vars(outer), parts, strict=True)})
    return ('coh', outer, restricted, labels)


def path_term(checker, ctx, steps):
    """Label a temporal row with all its coordinates, including each shared face."""
    rank = tdim_tm(ctx, steps[0])
    row = tree_ctx(suspend(chain_tree(len(steps)), rank - 1))
    entries = {}

    def put(slot, value):
        if slot in entries:
            return
        entries[slot] = value
        ty = row[slot]
        if ty != STAR:
            actual = checker.infer(ctx, value)
            put(ty[2][1], actual[2])
            put(ty[3][1], actual[3])

    for slot, step in zip(maximal_vars(row), steps, strict=True):
        put(slot, step)
    return subst_tm(ucomp(row), tuple(entries[i] for i in range(len(row))))


def rank_checks(binary, directory, ty, brackets, front_order, back_order, moving=False):
    flat = columns(NCOLS)
    checker = RankCut(2, binary, directory)
    tower = (STAR,)
    for i in range(RANK):
        tower += (arr(tower[-1], v(i), v(i)),)

    def compare(ctx, left, right):
        return ('coh', ctx, arr(checker.infer(ctx, left), left, right), variables(ctx))

    if moving:
        # Two brackets and an independent, directed update in the middle column.
        brackets = frozenset({(0, 3), (3, 5)})
        depths = (3, 3, 4, 3, 3)
        generic = tree_ctx(tuple(disc_tree(depth - 1) for depth in depths))
        tops = list(map(v, maximal_vars(generic)))
        negative, positive = [], []
        for label, depth in zip(tops, depths, strict=True):
            negative.append(src(generic, label) if depth == 4 else label)
            positive.append(tgt(generic, label) if depth == 4 else label)
        sections = [sub_from(flat, generic, dict(zip(maximal_vars(flat), end, strict=True)))
                    for end in (negative, positive)]
        compound = comp2(tower, RANK - 1, v(RANK), v(RANK))
        update = len(tower)
        tower += (arr(checker.infer(tower, compound), compound, compound),)
        labels = sub_from(generic, tower, {slot: v(update if depth == 4 else RANK)
                                          for slot, depth in zip(maximal_vars(generic), depths, strict=True)})
    else:
        generic = flat
        sections = [variables(flat)]
        labels = tuple(v(tdim(t) + 1) for t in flat)

    ordered = sorted(brackets)

    @cache
    def path(perm):
        here = brackets
        section = sections[0]
        steps = []
        for index in perm:
            before = reading(ty, here)
            if moving and index == 2:
                steps.append(compare(generic, subst_tm(before, section), subst_tm(before, sections[1])))
                section = sections[1]
            else:
                there = here - {ordered[index]}
                steps.append(subst_tm(compare(flat, before, reading(ty, there)), section))
                here = there
        return path_term(checker, generic, steps)

    def route(order):
        comparisons = [compare(generic, path(a), path(b)) for a, b in zip(order, order[1:])]
        return path_term(checker, generic, comparisons)

    front, back = route(front_order), route(back_order)
    crossings = (front, back, compare(generic, front, back), compare(generic, back, front))
    front_at, back_at, across, reverse = (subst_tm(t, labels) for t in crossings)
    attached = arr(checker.infer(tower, back_at), back_at, back_at)
    ctx = tower + (attached,)
    z = v(len(tower))
    fitted = path_term(checker, ctx, [across, z, reverse])
    expected = arr(checker.infer(tower, front_at), front_at, front_at)
    assert checker.checks(ctx, fitted, expected)
    assert not checker.checks(ctx, z, expected)
    if not moving:
        higher = RankCut(3, binary, directory)
        assert higher.checks(ctx, z, expected)
        assert not higher.equal_term(ctx, fitted, z)
    assert RankCut(6, binary, directory).equal_term(ctx, fitted, z)


def primitive_rank_checks(binary, directory):
    arrow = tree_ctx(disc_tree(1))
    f = v(maximal_vars(arrow)[0])
    padded = comp2(arrow, 0, ident(arrow, src(arrow, f)), f)
    rank_one = RankCut(1, binary, directory)
    assert rank_one.equal_term(arrow, padded, f)
    assert not rank_one.equal_term(susp_ctx(arrow), susp_tm(padded), susp_tm(f))
    assert RankCut(2, binary, directory).equal_term(susp_ctx(arrow), susp_tm(padded), susp_tm(f))

    point = tree_ctx(disc_tree(0))
    axis = ident(point, ident(point, v(0)))
    endo = head(point, axis, axis)
    unit = ident(point, axis)
    assert not RankCut(2, binary, directory).equal_term(point, endo, unit)
    assert RankCut(3, binary, directory).equal_term(point, endo, unit)


def check_checker(binary, directory):
    primitive_rank_checks(binary, directory)
    flat = columns(NCOLS)
    pair = columns(2)
    a, b = map(v, maximal_vars(pair))
    s, t = src(pair, a), src(pair, b)
    first = comp2(pair, 0, s, src(pair, t))
    second = comp2(pair, 0, tgt(pair, s), t)
    tag = head(pair, comp2(pair, RANK - 2, first, second), comp2(pair, 0, tgt(pair, a), tgt(pair, b)))
    # Transport this nonstandard head from two blocks of lengths three and two.
    split = reading(ucomp(flat)[2], {(0, 3), (3, 5)})[3]
    ty = subst_ty(tag[2], split)
    code = Assertions()
    trees = list(tree_readings(0, NCOLS))
    syntax = {brackets: code.term(reading(ty, brackets)) for brackets in trees}
    (directory / 'Heads.catt').write_text('\n'.join(code.commands) + '\n')
    p = shape(flat)
    def file(name, lines):
        (directory / name).write_text('import Heads\n' + '\n'.join(lines) + '\n')

    def equal(left, right, flags, compare_types=False):
        file('Equal.catt', [f'assert {left} = {right} in {p}'])
        output = run(binary, directory, 'Equal.catt', flags)
        if 'Error: Assertion failed:' in output and 'are not equal' in output:
            return False
        if compare_types and 'Error: Terms ' in output and 'do not have matching types' in output:
            return False
        accepted(output, 'Equal.catt', [])
        assert 'are equal' in output
        return True

    upper = ['--sua']
    lower = ['--insertion-width', '2']
    merged = syntax[frozenset()]
    actual = {t for t in trees if equal(merged, syntax[t], upper, compare_types=True)}
    allowed = {next(iter(t)) for t in actual if len(t) == 1}
    assert actual == {t for t in trees if t <= allowed}
    assert len(actual) == count_readings(NCOLS, allowed)
    assert 0 < len(allowed) < 9
    for a, b in combinations(actual, 2):
        assert not equal(syntax[a], syntax[b], lower)

    # Compose the six orders around a cube with one nested bracket.
    initial = frozenset({(0, 2), (0, 3), (3, 5)})
    assert initial in actual
    ordered = sorted(initial)
    defs = []
    params = ','.join(f'x{i}' for i in maximal_vars(flat))
    def coherence(name, left, right):
        defs.append(f'def {name} = coh [ {p} : {left} -> {right} ]')
        return f'{name}({params})'

    edges = {}
    paths = {}
    for perm in permutations(range(3)):
        here = initial
        steps = []
        for i in perm:
            there = here - {ordered[i]}
            key = (here, there)
            if key not in edges:
                edges[key] = coherence('edge' + str(len(edges)), syntax[here], syntax[there])
            steps.append(edges[key])
            here = there
        paths[perm] = 'comp[' + ','.join(steps) + ']'
    def route(perms):
        faces = [coherence('square' + str(len(defs)), paths[a], paths[b])
                 for a, b in zip(perms, perms[1:])]
        return 'comp[' + ','.join(faces) + ']'

    front_order = [(0, 1, 2), (1, 0, 2), (1, 2, 0), (2, 1, 0)]
    back_order = [(0, 1, 2), (0, 2, 1), (2, 0, 1), (2, 1, 0)]
    front = route(front_order)
    back = route(back_order)
    defs.extend([f'def front {p} = {front}', f'def back {p} = {back}'])
    coherence('across', front, back)
    coherence('reverse', back, front)
    file('Cube.catt', defs)
    ctx = '(x : *) (f : x -> x) (a : f -> f) (b : a -> a)'
    args = '(b,b,b,b,b)'
    ctx += f' (z : back{args} -> back{args})'
    fitted = f'comp[across{args},z,reverse{args}]'
    def cube_file(name, decl):
        (directory / name).write_text('import Cube\n' + decl + '\n')
    cube_file('Fit.catt', f'def fitted {ctx} : front{args} -> front{args} = {fitted}')
    cube_file('Direct.catt', f'def direct {ctx} : front{args} -> front{args} = z')
    cube_file('Class.catt', f'def retained {ctx} : {fitted} -> z = id(z)')
    accepted(run(binary, directory, 'Fit.catt', lower), 'Fit.catt', ['fitted'])
    rejected(run(binary, directory, 'Direct.catt', lower), 'Direct.catt', 'direct')
    for moving in (False, True):
        rank_checks(binary, directory, ty, initial, front_order, back_order, moving)
    accepted(run(binary, directory, 'Class.catt', upper), 'Class.catt', ['retained'])
    print(f'{len(actual)} distinct width-two readings of the nonstandard head among {len(trees)} groupings; '
          f'{len(allowed)} admissible single intervals. Both stationary and moving rank-two fits preserve the 6-generator.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('binary', type=Path, help='Rice checker with --insertion-width')
    args = parser.parse_args()
    print(f'Checked the flag test and counting recurrence for {count_tests()} interval families.')
    with TemporaryDirectory() as scratch:
        check_checker(args.binary.resolve(), Path(scratch))
