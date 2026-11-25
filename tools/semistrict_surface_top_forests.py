"""Check separation of top expansions and contractions at compound written faces."""
from argparse import ArgumentParser
from collections import deque
from itertools import product
from pathlib import Path

from catt import arr, comp2, fv_tm, infer, maximal_vars, src, tgt, tree_ctx, v
from ct_suspension import ident, susp_tm
from relative_coherence_exchange_faces import composite, head, string_tree
from semistrict_surface_directed_power_queries import apply, square
from semistrict_surface_inverse_completion import DerivationEmitter
from semistrict_surface_positional_tags import loop_tower


def closure(start, productions):
    seen = {start}
    queue = deque([start])
    while queue:
        word = queue.popleft()
        for old, new in productions:
            for pos in range(len(word) - len(old) + 1):
                if word[pos:pos + len(old)] == old:
                    nxt = word[:pos] + new + word[pos + len(old):]
                    if nxt not in seen:
                        seen.add(nxt)
                        queue.append(nxt)
    return seen


def check_word_factorizations():
    # Expansion and contraction have bounded depth on these inputs.
    # This finite acyclic example has overlapping and disjoint uses, a peak
    # with a genuine expansion-only witness, and permutations of the letters at the middle boundary.
    expansion = [('a', 'bc'), ('b', 'dd'), ('x', 'de'), ('c', 'e'), ('d', 'f')]
    contraction = [('bc', 'x'), ('fd', 'y'), ('ee', 'z')]
    # The peak bc -> x -> de needs an expansion-only test. Use b -> d as
    # an additional choice alongside b -> dd.
    expansion.append(('b', 'd'))
    alphabet = 'abcdexfyz'
    seam = [(a + b, b + a) for a in alphabet for b in alphabet if a != b]
    assert 'de' in closure('bc', expansion)
    words = [''.join(p) for k in (1, 2) for p in product('abcxdfe', repeat=k)]
    arrivals = {}
    count = 0
    for start in words:
        interleaved = closure(start, expansion + contraction + seam)
        factored = set()
        for opened in closure(start, expansion):
            for mid in closure(opened, seam):
                if mid not in arrivals:
                    arrivals[mid] = closure(mid, contraction)
                factored.update(arrivals[mid])
        assert interleaved == factored
        count += len(interleaved)
    # Omitting the peak condition can change reachability already on words.
    assert 'de' in closure('bc', [('bc', 'x'), ('x', 'de')])
    assert all('de' not in closure(middle, [('bc', 'x')])
               for middle in closure('bc', [('x', 'de')]))
    return count


def change_at_face(ctx, template, face, place, variation, labels):
    arity = tree_ctx(string_tree(1, (4, 3) if place == 0 else (3, 4)))
    tips = list(map(v, maximal_vars(arity)))
    moving = tips[place]
    ends = []
    for boundary in (src, tgt):
        tips[place] = boundary(arity, moving)
        ends.append(face(arity, apply(arity, template, tips)))
    args = list(labels)
    args[place] = variation
    return apply(ctx, (arity, head(arity, *ends)), args)


def check_typed_peak(emitter):
    base = loop_tower(2)
    p = comp2(base, 1, v(2), v(2))
    ty = arr(infer(base, p), p, p)
    b, c, b1, b2, c1, c2, d = [v(len(base) + i) for i in range(7)]
    base += (ty,) * 7
    native = susp_tm(square(2)[1])
    template = native[1], native
    inner = apply(base, template, (b, c))
    old_start, peak_end = src(base, inner), tgt(base, inner)
    w = v(len(base))
    base += (infer(base, old_start),)
    pair = comp2(base, 2, b1, b2)
    idle = ident(base, p)
    c_pair = comp2(base, 2, c1, c2)
    c_final = comp2(base, 2, c1, idle)
    endpoints = [(old_start, w), (w, peak_end), (b, pair), (c, c_pair), (c2, idle), (pair, d)]
    into, out, split, branch, erase, join = (v(len(base) + i) for i in range(len(endpoints)))
    ctx = base + tuple(arr(infer(base, a), a, b_) for a, b_ in endpoints)
    c_forest = comp2(ctx, 3, branch, comp2(ctx, 2, c1, erase))
    assert tgt(ctx, c_forest) == c_final
    old_end = tgt(ctx, apply(ctx, template, (d, c_final)))

    def move(face, pos, step, labels):
        return change_at_face(ctx, template, face, pos, step, labels)

    original = composite(ctx, 3, [
        into, out, move(tgt, 0, split, (b, c)), move(tgt, 1, c_forest, (pair, c)),
        move(tgt, 0, join, (pair, c_final))])
    middle = apply(base, template, (pair, c_final))
    sorted_term = composite(ctx, 3, [
        move(src, 0, split, (b, c)), move(src, 1, c_forest, (pair, c)),
        middle, move(tgt, 0, join, (pair, c_final))])
    expected = arr(infer(ctx, old_start), old_start, old_end)
    assert infer(ctx, original) == infer(ctx, sorted_term) == expected
    assert (fv_tm(original) - fv_tm(sorted_term)) >= {into[1], out[1]}
    assert src(base, middle) != tgt(base, middle)
    if emitter is not None:
        emitter.check_type('unfoldedPeak', ctx, original, expected)
        emitter.check_type('factoredAtOriginalEnds', ctx, sorted_term, expected)
        emitter.check_type('comparisonOnSkeleton', base, middle, infer(base, middle))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    count = check_word_factorizations()
    emitter = DerivationEmitter() if args.agda_dir else None
    check_typed_peak(emitter)
    if emitter is not None:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('TopForests', __doc__).replace(
            'open import CaTTExp.Pure\n', 'open import CaTTExp.Gray.Pure\n'
            'open import CaTTExp.Pure using (∅)\n'
            'open import CaTTExp.PastingCheck ∅ using () renaming (checkPs to pastable)\n')
        (args.agda_dir / 'TopForests.agda').write_text(module)
    print(f'Checked {count} reachable word pairs and both typed routes through the compound-pole peak.')


if __name__ == '__main__':
    main()
