"""Check cut words in free surface contexts and the several-seam bar contraction."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import re
from tempfile import TemporaryDirectory

from catt import STAR, arr, comp2, disc_tree, glue_tree, infer, maximal_vars, sub_from, subst_tm, tdim_tm, tree_ctx, v
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import ident, susp_ctx, susp_tm
from partial_cylinder_steiner import trees
from relative_coherence_exchange_faces import head
from semistrict_surface_elementary_insertions import slots, subtree
from semistrict_surface_moore_insertion import height
from semistrict_surface_scalar_pairs import splice
from semistrict_surface_seam_descent import drop, erase, then
from semistrict_surface_window_intersections import Equations, assertions, collapse, parents, suspend
from semistrict_surface_exact_boundary import run
from semistrict_surface_insertion_cut import Assertions, variables


def raise_to(ctx, term, rank):
    for _ in range(tdim_tm(ctx, term), rank):
        term = ident(ctx, term)
    return term


def examples():
    x, f, a, b, z = map(v, range(5))
    graph = (STAR, arr(STAR, x, x))
    ff = comp2(graph, 0, f, f)
    a_type = arr(infer(graph, ff), ff, ff)
    ctx = (*graph, a_type, a_type, arr(a_type, a, a))
    pair = tree_ctx(glue_tree(2, 0, 2))
    symbols = maximal_vars(pair)
    swap = head(pair, *temporal_words(pair, *map(v, symbols), 0, 1))
    swap = subst_tm(swap, sub_from(pair, ctx, dict(zip(symbols, (a, b), strict=True))))
    atoms = [f, a, b, comp2(ctx, 1, a, b), z, swap]
    yield ctx, 0, x, atoms
    yield susp_ctx(ctx), 1, susp_tm(x), list(map(susp_tm, atoms))
    # An opaque standard with trunk strictly below the cut. Its outer binary
    # spatial head must survive when concatenated at the higher cut.
    wide = comp2(ctx, 0, ff, ff)
    spatial = comp2(ctx, 0, a, b)
    twice = comp2(ctx, 0, a, a)
    yield ctx, 1, wide, [spatial, twice, comp2(ctx, 0, z, b)]


def rice_words(binary, ctx, cut, pole, atoms, width):
    rank = cut + width
    atoms = [t for t in atoms if tdim_tm(ctx, t) <= rank]
    if not atoms:
        return 0, 0
    code = Assertions()
    annotated = [f'(x{i} : ' + ('*' if ty == STAR else ' -> '.join(code.term(t) for t in ty[2:])) + ')'
                 for i, ty in enumerate(ctx)]
    context = ' '.join(annotated)
    spellings = {}

    def add(term, word):
        # Every spelling here has the same output rank.
        term = raise_to(ctx, term, rank)
        spellings.setdefault(term, word)
        assert spellings[term] == word

    add(pole, ())
    for size in range(1, 4):
        for word in product(range(len(atoms)), repeat=size):
            entries = [atoms[i] for i in word]
            high = [raise_to(ctx, t, rank) for t in entries]
            readings = []
            for values in (entries, high):
                left = values[0]
                for t in values[1:]:
                    left = comp2(ctx, cut, left, t)
                readings.append(left)
                right = values[-1]
                for t in reversed(values[:-1]):
                    right = comp2(ctx, cut, t, right)
                readings.append(right)
            readings.append(comp2(ctx, cut, raise_to(ctx, pole, rank), readings[0]))
            readings.append(comp2(ctx, cut, readings[0], raise_to(ctx, pole, rank)))
            for term in readings:
                add(term, word)
    cases = [f'normalise {code.term(t)} in {context}' for t in spellings]
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'Words.catt').write_text('\n'.join(code.commands + cases) + '\n')
        for flags in (['--insertion-width', str(width)], ['--sua']):
            out = run(binary, folder, 'Words.catt', flags)
            assert 'Error:' not in out, out[-2000:]
            forms = [re.sub(r'\s+', '', s) for s in re.findall(
                r'Normal form:\s*(.*?)\s+has type:', out, flags=re.S)]
            assert len(forms) == len(cases), out[-2000:]
            names, words = {}, {}
            for word, shape in zip(spellings.values(), forms, strict=True):
                assert names.setdefault(word, shape) == shape, word
                assert words.setdefault(shape, word) == word, (shape, word)
    return len(cases), len(words)


def cuts_for(signature, size):
    return set(combinations_with_replacement(range(size + 1), len(signature)))


def neighbors(cut, grades, signature):
    ends = (0, *cut, len(grades))
    for i, threshold in enumerate(signature):
        for dest in range(ends[i], ends[i + 2] + 1):
            lo, hi = sorted((cut[i], dest))
            if dest != cut[i] and all(g <= threshold for g in grades[lo:hi]):
                yield cut[:i] + (dest,) + cut[i + 1:]


def components(grades, signature):
    unseen = cuts_for(signature, len(grades))
    while unseen:
        start = min(unseen)
        seen, todo = {start}, [start]
        while todo:
            for nxt in neighbors(todo.pop(), grades, signature):
                if nxt not in seen:
                    todo.append(nxt)
                    seen.add(nxt)
        unseen.difference_update(seen)
        yield seen


def signature_key(cut, grades, signature):
    # Position in the ordered subword of atoms too tall to cross the seam.
    return tuple(sum(g > m for g in grades[:pos]) for pos, m in zip(cut, signature, strict=True))


@cache
def choose_positions(lo, hi):
    return tuple(tuple(p for p in range(lo, hi + 1) if mask & (1 << (p-lo)))
                 for mask in range(1, 1 << (hi-lo+1)))


def check_bars(grades, signature, count):
    universe = cuts_for(signature, len(grades))
    groups = {}
    for cut in universe:
        groups.setdefault(signature_key(cut, grades, signature), set()).add(cut)
    direct = list(components(grades, signature))
    assert {frozenset(s) for s in groups.values()} == {frozenset(s) for s in direct}
    count['placement components'] += len(direct)

    # Generate every nondegenerate multibar simplex independently: each cut
    # spans a chosen subsequence of positions, with mobile blocks in its gaps.
    for group in direct:
        floor = tuple(map(min, zip(*group, strict=True)))
        assert floor in group
        seen = set()
        for start in group:
            for end in group:
                if any(start[i] > end[i] or i + 1 < len(start) and end[i] > start[i+1]
                       for i in range(len(start))):
                    continue
                for supports in product(*(choose_positions(l, r) for l, r in zip(start, end, strict=True))):
                    if all(s[0] == l and s[-1] == r for s, l, r in zip(supports, start, end, strict=True)):
                        seen.add(supports)
        for supports in seen:
            assert all(c in group for c in product(*supports))
            current = list(supports)
            for i, low in enumerate(floor):
                cone = current.copy()
                cone[i] = tuple(sorted(set(current[i]) | {low}))
                assert tuple(cone) in seen
                current[i] = (low,)
                assert tuple(current) in seen
                count['stage cones'] += 1
        count['bar cells'] += len(seen)


def window_after_prune(checks, tree, parent, start, end, small, include):
    for tip in slots(tree):
        target, prune = erase(tree, tip)
        row_tip = len(tip) == len(parent) + 1 and tip[:-1] == parent
        inside = (len(tip) > len(parent) and tip[:len(parent)] == parent
                  and start <= tip[len(parent)] < end)
        left = start - int(row_tip and tip[-1] < start)
        right = end - int(row_tip and tip[-1] < end)
        base = drop(parent, tip)
        residual, inc = collapse(target, base, left, right)
        if inside:
            if residual == small:
                q = variables(tree_ctx(small))
            else:
                rank = len(base) + height(subtree(tree, parent)[start:end])
                qtree, q = erase(small, parent + (start,) + (0,) * (rank - len(parent) - 1))
                assert qtree == residual
        else:
            image = tip
            if len(tip) > len(parent) and tip[:len(parent)] == parent and tip[len(parent)] >= end:
                image = parent + (tip[len(parent)] - end + start + 1,) + tip[len(parent)+1:]
            qtree, q = erase(small, image)
            assert qtree == residual
        checks.maps(target, then(include, prune), then(q, inc), 'pruning a window')


def slide_maps(tree, parent, seam, middle):
    row = subtree(tree, parent)
    expanded_row = row[:seam] + (disc_tree(middle-1),) + row[seam:]
    if parent:
        large = splice(tree, parent, suspend((expanded_row,), len(parent)-1))
    else:
        large = expanded_row
    left, l = collapse(large, parent, seam-1, seam+1)
    right, r = collapse(large, parent, seam, seam+2)
    assert left == right == tree
    return large, l, r


def local_interactions(binary, edges):
    checks = Equations()
    for n in range(edges + 1):
        for tree in trees(n):
            for parent in parents(tree):
                row = subtree(tree, parent)
                for a, e in combinations(range(len(row)+1), 2):
                    small, inc = collapse(tree, parent, a, e)
                    if tree == small:
                        continue
                    window_after_prune(checks, tree, parent, a, e, small, inc)
                    for i in range(1, len(row)):
                        heights = [height(t) for t in row[i-1:i+1]]
                        if any(t != disc_tree(h) for t, h in zip(row[i-1:i+1], heights, strict=True)):
                            continue
                        for m in range(1, min(heights) + 1):
                            target, l, r = slide_maps(tree, parent, i, m)
                            if a < i < e:
                                checks.maps(target, then(inc, l), then(inc, r), 'absorbed slides')
                            else:
                                shift = int(i <= a)
                                after, post = collapse(target, parent, a+shift, e+shift)
                                new_i = i - (e-a-1 if e <= i else 0)
                                reduced, ll, rr = slide_maps(small, parent, new_i, m)
                                assert after == reduced
                                for old, new in ((l, ll), (r, rr)):
                                    checks.maps(target, then(inc, old), then(new, post), 'transported slides')
    assertions(binary, checks.rice, ['--sua'])
    return checks.counts, len(checks.seen)


def pullback_obstruction(binary):
    tree = (disc_tree(1),) * 3
    _, l = collapse(tree, (), 0, 2)
    pair, r = collapse(tree, (), 1, 3)
    base, q = erase(tree, (1, 0))
    assert base == (disc_tree(1), (), disc_tree(1))
    three, ll, rr = slide_maps(pair, (), 1, 1)
    assert three == base
    eq = Equations()
    for leg, wanted in ((l, ll), (r, rr)):
        eq.maps(base, then(leg, q), wanted, 'after pruning')
    c = tree_ctx(pair)
    swap = head(c, *temporal_words(c, *map(v, maximal_vars(c)), 0, 1))
    eq.rice.equal(tree_ctx(base), subst_tm(swap, then(l, q)), subst_tm(swap, then(r, q)),
                  'balanced head after pruning')
    assertions(binary, eq.rice, ['--insertion-width', '2'])
    unequal = Assertions()
    unequal.equal(tree_ctx(tree), subst_tm(swap, l), subst_tm(swap, r), 'separate lifted heads')
    assertions(binary, unequal, ['--sua'], False, allow_different_types=True)


def pullback_cuts(totals):
    # Both arms specialize three atoms to the same four-letter word, allowing
    # contractions to an empty word and substitutions which expand an atom.
    grades = (1, 2, 1, 1)
    signature = (1, 1)
    def arms():
        for i,j in combinations_with_replacement(range(5), 2):
            boundaries = (0, i, j, 4)
            ranks = [max(grades[a:b], default=1) for a,b in zip(boundaries, boundaries[1:])]
            for promoted in product(*(range(r, 3) for r in ranks)):
                yield boundaries, promoted

    def index(arm):
        pos, heights = arm
        values = {}
        for cut in cuts_for(signature, 3):
            at = tuple(pos[c] for c in cut)
            key = signature_key(cut, heights, signature)
            values.setdefault(key, {}).setdefault(at, set()).add(cut)
        return values

    indexed = [(arm, index(arm)) for arm in arms()]
    for (_, left_geom), left in indexed:
        for (_, right_geom), right in indexed:
            for l in left.values():
                for r in right.values():
                    a, b = next(iter(l)), next(iter(r))
                    if signature_key(a, grades, signature) != signature_key(b, grades, signature):
                        continue
                    lifts = {(u, v) for c in l.keys() & r.keys() for u in l[c] for v in r[c]}
                    if not lifts:
                        totals['unrealized compatible classes'] += 1
                        continue
                    minima = tuple(tuple(map(min, zip(*ss, strict=True))) for ss in zip(*lifts, strict=True))
                    assert minima in lifts
                    # Individual monotone cut contractions must be actual
                    # simultaneous substring transfers in the two arms.
                    for u,vv in lifts:
                        for i in range(len(signature)):
                            next_u = u[:i]+minima[0][i:i+1]+u[i+1:]
                            next_v = vv[:i]+minima[1][i:i+1]+vv[i+1:]
                            assert (next_u, next_v) in lifts
                            assert all(h <= signature[i] for h in left_geom[next_u[i]:u[i]])
                            assert all(h <= signature[i] for h in right_geom[next_v[i]:vv[i]])
                            u, vv = next_u, next_v
                    totals['realized compatible classes'] += 1


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rice-binary', required=True, type=Path)
    parser.add_argument('--letters', default=4, type=int)
    parser.add_argument('--edges', default=6, type=int)
    args = parser.parse_args()
    totals = Counter()
    for ctx, cut, pole, atoms in examples():
        for width in (1, 2, 3):
            cases, classes = rice_words(args.rice_binary.resolve(), ctx, cut, pole, atoms, width)
            totals['normalized spellings per mode'] += cases
            totals['word classes across cases'] += classes
    for length in range(args.letters + 1):
        for grades in product((1, 2, 3), repeat=length):
            for size in range(1, 4):
                for signature in product((1, 2), repeat=size):
                    check_bars(grades, signature, totals)
    pullback_cuts(totals)
    pullback_obstruction(args.rice_binary.resolve())
    print(dict(totals), flush=True)
    squares, equations = local_interactions(args.rice_binary.resolve(), args.edges)
    print(dict(squares), equations, 'nonliteral coordinate comparisons')
