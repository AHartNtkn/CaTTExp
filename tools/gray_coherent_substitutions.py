"""Checks for canonical-gray-terms-r10. Pass --agda FILE to emit a certificate."""
import argparse
from functools import cache
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path

from canonical_gray_two_discs import atom, build_cube, cube_generators, strict_interpreter
from catt import (STAR, arr, chain_tree, comp_tree, disc_tree, infer, ps_boundary_vars, ps_dim,
                  side_ok, sub_from, subst_tm, subst_ty, tdim, tdim_tm, tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_section_functoriality import edge, vertex, unary
from rc2 import path, struct_cell


# A finite category of ordinal maps containing a split retraction.
def compose(first, second):
    source, middle, f = first
    assert middle == second[0]
    return source, second[1], tuple(second[2][i] for i in f)


def identity(arrow):
    source, target, f = arrow
    return source == target and f == tuple(range(source + 1))


def cut_word(word, mask):
    """Vertex of the resolution, as a word of nonidentity composites."""
    if not word:
        return ()
    blocks = []
    block = word[0]
    for i, arrow in enumerate(word[1:]):
        if mask & (1 << i):
            blocks.append(block)
            block = arrow
        else:
            block = compose(block, arrow)
    blocks.append(block)
    return tuple(arrow for arrow in blocks if not identity(arrow))


def delete_bit(mask, j):
    return (mask & ((1 << j) - 1)) | ((mask >> (j + 1)) << j)


def unit_mask(mask, index, length):
    if length == 1:
        return 0
    if index == 0:
        return mask >> 1
    if index == length - 1:
        return mask & ((1 << (length - 2)) - 1)
    joined = delete_bit(mask, index)
    return joined | (((mask >> index) & 1) << (index - 1))


def coherent_words():
    arrows = [(a, b, f) for a, b in product(range(2), repeat=2)
              for f in combinations_with_replacement(range(b + 1), a + 1)]
    words = [(a,) for a in arrows]
    vertices = 0
    for length in range(1, 6):
        for word in words:
            for mask in range(1 << (length - 1)):
                value = cut_word(word, mask)
                vertices += 1
                for j, arrow in enumerate(word):
                    if identity(arrow):
                        assert value == cut_word(word[:j] + word[j+1:],
                                                 unit_mask(mask, j, length))
                for j in range(length - 1):
                    if mask & (1 << j):
                        assert value == (cut_word(word[:j+1], mask & ((1 << j) - 1))
                                         + cut_word(word[j+1:], mask >> (j + 1)))
                    else:
                        reduced = word[:j] + (compose(word[j], word[j+1]),) + word[j+2:]
                        assert value == cut_word(reduced, delete_bit(mask, j))
        words = [word + (a,) for word in words for a in arrows if word[-1][1] == a[0]]
    return vertices


def quotient_checks():
    """Every pair of prescribed quotients agrees via its join on all common quotients."""
    def quotient(size, merges):
        values = [0]
        for i in range(size):
            values.append(values[-1] + int(not (merges & (1 << i))))
        return tuple(values)

    def factor(smaller, larger):
        # Does the second ordinal map factor through the first?
        return all(x != y or u == v for x, y, u, v in
                   zip(smaller, smaller[1:], larger, larger[1:]))

    cases = 0
    for degree in range(1, 7):
        maps = {m: quotient(degree, m) for m in range(1 << degree)}
        for i, s in maps.items():
            for j, t in maps.items():
                join = maps[i | j]
                for q in maps.values():
                    assert factor(join, q) == (factor(s, q) and factor(t, q))
                    cases += 1
    return cases


def cube_tableaux():
    """Compare row-linear evaluation with the existing evaluator using inferred poles."""
    context, tests = build_cube()
    labels = list(cube_generators())
    reference = strict_interpreter(context, labels)

    @cache
    def rows(raw):
        if raw[0] == 'v':
            return atom(labels[raw[1]])
        _, arity, annotation, entries = raw
        height = ps_dim(arity)
        result = []
        for k in range(height + 1):
            pair = []
            for sign in ('-', '+'):
                indices = (range(len(arity)) if k == height else
                           ps_boundary_vars(arity, k, sign))
                chain = tuple(sorted(basis for i in indices if tdim(arity[i]) + 1 == k
                                     for basis in rows(entries[i])[-1][0]))
                pair.append(chain)
            result.append(tuple(pair))
        return tuple(result) + (((), ()),) * (tdim(annotation) + 1 - height)

    inputs = [v(i) for i in range(len(context))] + [t for _, t, _ in tests]
    for raw in inputs:
        assert rows(raw) == reference(raw)
        raised = ident(context, raw)
        assert rows(raised) == reference(raised) == rows(raw) + (((), ()),)
    return 2 * len(inputs)


@cache
def hierarchies(start, end):
    if end - start == 1:
        return (start,)
    out = []
    for count in range(1, end - start):
        for cuts in combinations(range(start + 1, end), count):
            stops = (start,) + cuts + (end,)
            out.extend(product(*(hierarchies(a, b) for a, b in zip(stops, stops[1:]))))
    return tuple(out)


@cache
def term(size, hierarchy):
    if isinstance(hierarchy, int):
        return edge(hierarchy)
    context = tree_ctx(chain_tree(size))
    return comp_tree(chain_tree(len(hierarchy)), context, [term(size, h) for h in hierarchy])


@cache
def path_sections(size):
    intervals = [(i, j) for i in range(size + 1) for j in range(i, size + 1)]
    ctx = tree_ctx(chain_tree(size))
    options = [([ident(ctx, vertex(i))] if i == j else
                [term(size, h) for h in hierarchies(i, j)]) for i, j in intervals]
    return [dict(zip(intervals, ts)) for ts in product(*options)]


def strict_on(left, right, f):
    sub = [vertex(f[0])]
    for a, b in zip(f, f[1:]):
        sub.extend((vertex(b), right[a, b]))
    return all(subst_tm(t, sub) == right[f[i], f[j]] for (i, j), t in left.items())


def path_class(emitter):
    count = admitted = 0
    for source, target in product(range(4), repeat=2):
        for f in combinations_with_replacement(range(target + 1), source + 1):
            candidates = ((s, s) for s in path_sections(source)) if source == target else (
                product(path_sections(source), path_sections(target)))
            actual = any(strict_on(s, t, f) for s, t in candidates)
            assert actual == (source < 2 or all(a < b for a, b in zip(f, f[1:])))
            count += 1
            admitted += actual
    a, b = (0, 1, 3), (0, 2, 3)
    binary, = path_sections(2)
    targets = path_sections(3)
    first = [t for t in targets if strict_on(binary, t, a)]
    second = [t for t in targets if strict_on(binary, t, b)]
    assert first and second and not any(t in second for t in first)
    ctx = tree_ctx(chain_tree(3))
    left, right = first[0][0, 3], second[0][0, 3]
    assert path(ctx, left) == path(ctx, right) and left != right
    comparison = struct_cell(ctx, left, right)
    comparison_type = arr(infer(ctx, left), left, right)
    emitter.check_type('subdivision-comparison', ctx, comparison, comparison_type)
    bad = emitter.ctx(ctx + (arr(comparison_type, comparison, ident(ctx, left)),))
    emitter.checks.append(f'canonical-identity-rejected : is-just (checkCtx {bad}) ≡ false\n'
                          'canonical-identity-rejected = refl')
    return count, admitted


def preimages(raw, entries):
    """All slot cuts, leaving the scope of a retained head alone."""
    cuts = {v(i) for i, image in enumerate(entries) if image == raw}
    if raw[0] == 'coh':
        _, arity, ty, args = raw
        for pre_args in product(*(preimages(arg, entries) for arg in args)):
            cuts.add(('coh', arity, ty, pre_args))
    return cuts


def cut_checks(emitter):
    arity = tree_ctx(chain_tree(2))
    ctx = tree_ctx(chain_tree(3))
    path3 = term(3, (0, (1, 2)))
    pairs = {2: edge(0), 4: term(3, (1, 2))}
    labels = sub_from(arity, ctx, pairs)
    # At the right-hand endpoint a second writing with the identical strict path
    # constrains the same head. Test what survives common cuts of both slots.
    generic = ucomp(arity)
    assert subst_tm(generic, labels) == path3
    lifted = (path3, unary(ctx, path3))
    candidates = []
    for end in lifted:
        cuts = preimages(end, labels)
        assert all(subst_tm(cut, labels) == end for cut in cuts)
        heads = {arr(infer(arity, generic), generic, cut) for cut in cuts
                 if infer(arity, cut) == infer(arity, generic)
                 and side_ok(arity, infer(arity, generic), generic, cut)}
        assert heads
        candidates.append(heads)
        for head in heads:
            result = ('coh', arity, head, labels)
            assert infer(ctx, result) == arr(infer(ctx, path3), path3, end)
    assert candidates[0].isdisjoint(candidates[1])
    actual = ('coh', arity, arr(infer(arity, generic), generic, unary(arity, generic)), labels)
    emitter.check_type('cut-head', ctx, actual, arr(infer(ctx, path3), path3, lifted[1]))
    # Repeated entries supply multiple valid inverse variable cuts.
    collapsed = (v(0), v(0), ident((STAR,), v(0)))
    assert preimages(v(0), collapsed) == {v(0), v(1)}


@cache
def tree_size(raw):
    return 1 + sum(tree_size(x) for x in raw if isinstance(x, tuple))


def excess_checks(emitter):
    bounds = [1]
    for k in range(1, 4097):
        bounds.append(sum(bounds[:(k - 1) // 2 + 1]))
    for q in range(1, 7):
        assert bounds[4**q] >= 4**(q * (q - 1) // 2)
    # Independent minimum cost of the *two* sets of subtrees, allowing every
    # arity height p (relative to the ambient height) from 0 to k.
    costs = [1]
    for k in range(1, 161):
        candidates = []
        for p in range(k):  # p=k already has an entry of the desired rank
            entries = sum(costs[:p+1])
            poles = sum(costs[:k-p])
            candidates.append(1 + entries + poles)
        costs.append(min(candidates))
        assert costs[-1] >= bounds[k]
    point = (STAR,)
    towers = [v(0)]
    for _ in range(5):
        towers.append(ident(point, towers[-1]))
    for base in range(4):
        disc = tree_ctx(disc_tree(base))
        generic = v(len(disc) - 1)
        renaming = sub_from(disc, point, {len(disc) - 1: towers[base]})
        slot_vars = tuple(v(i) for i in range(len(disc)))
        for degree in range(base + 1, 7):
            generic = ('coh', disc, arr(infer(disc, generic), generic, generic), slot_vars)
            written = subst_tm(generic, renaming)
            expected = subst_ty(infer(disc, generic), renaming)
            assert tdim_tm(point, written) == degree and tree_size(written) >= bounds[degree]
            if degree == 5:
                emitter.check_type(f'excess-{base}', point, written, expected)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    vertices = coherent_words()
    quotients = quotient_checks()
    tableaux = cube_tableaux()
    paths, admitted = path_class(emitter)
    cut_checks(emitter)
    excess_checks(emitter)
    print(f'{vertices} cut vertices; {admitted}/{paths} path maps admit strict sections.')
    print(f'{quotients} quotient checks; {tableaux} cube tableaux agree in all rows.')
    print('Pole cuts, incompatible subdivisions, and rank-excess bounds passed.')
    if args.agda:
        args.agda.write_text(emitter.module(args.agda.stem, 'Gray terms, round 10.'))
