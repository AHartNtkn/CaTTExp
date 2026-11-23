"""Check cubical attachments for changing paths and thinness of the two-letter exchanges."""

from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path

from catt import STAR, arr, comp2, glue_tree, infer, maximal_vars, sub_from, subst_tm, tree_ctx, v
from catt_unit_ordered_exchange import temporal_words
from emit_agda import Emitter
from relative_coherence_exchange_faces import head


# A cube is a spatial string of old edges and marked rewrite intervals.
# Include insertions, erasures and a scalar at an empty path.
BOUNDARIES = {"b": ("", "ff"), "c": ("ff", ""), "d": ("", ""), "e": ("f", "g")}


def marked(word):
    return [i for i, token in enumerate(word) if token in BOUNDARIES]


def face(word, coordinate, end):
    i = marked(word)[coordinate]
    return word[:i] + BOUNDARIES[word[i]][end] + word[i + 1:]


def edge(step):
    i, = marked(step)
    return (step[:i], step[i], step[i + 1:])


def check_cubes(counts):
    for size in range(1, 6):
        for tokens in product("fgbcde", repeat=size):
            word = "".join(tokens)
            active = marked(word)
            if not active:
                continue
            # Attach d last. Intervals labelled d cut the word uniquely
            # into older word factors, including empty intervening factors.
            old = word.split("d")
            assert "d".join(old) == word
            for j in range(len(old) - 1):
                coordinate = sum(len(marked(part)) for part in old[:j + 1]) + j
                assert face(word, coordinate, 0) == face(word, coordinate, 1)
                assert face(word, coordinate, 0) == "d".join(old[:j] + [
                    old[j] + old[j + 1]] + old[j + 2:])
                counts["folded attaching faces"] += 1
            for i, j in combinations(range(len(active)), 2):
                for s, t in product((0, 1), repeat=2):
                    assert face(face(word, j, t), i, s) == face(face(word, i, s), j - 1, t)
                    counts["cubical face identities"] += 1
            if len(active) != 2:
                continue
            i, j = active
            b, c = word[i], word[j]
            l, m, r = word[:i], word[i + 1:j], word[j + 1:]
            sb, tb = BOUNDARIES[b]
            sc, tc = BOUNDARIES[c]
            # Read the two oriented facet walks independently as old
            # contextual rewriting steps on explicitly flattened paths.
            assert (edge(face(word, 0, 0)), edge(face(word, 1, 1))) == (
                (l + sb + m, c, r), (l, b, m + tc + r))
            assert (edge(face(word, 1, 0)), edge(face(word, 0, 1))) == (
                (l, b, m + sc + r), (l + tb + m, c, r))
            counts["directed square boundaries"] += 1


def check_shuffles(counts):
    for size in range(8):
        for word in product("LRm", repeat=size):
            # Each occurrence keeps its initial wire number. A diagram
            # records the ordered crossing partners on every wire.
            @lru_cache(None)
            def sortings(order):
                reference = None
                total = 0
                for i in range(len(order) - 1):
                    a, b = order[i:i + 2]
                    if (word[a], word[b]) != ("R", "L"):
                        continue
                    next_order = order[:i] + (b, a) + order[i + 2:]
                    rest, paths = sortings(next_order)
                    record = list(rest)
                    record[a] = (b,) + record[a]
                    record[b] = (a,) + record[b]
                    record = tuple(record)
                    if reference is not None:
                        assert reference == record
                    reference = record
                    total += paths
                if reference is None:
                    return ((),) * len(order), 1
                return reference, total

            record, paths = sortings(tuple(range(size)))
            inversions = sum(block[:i].count("R") for block in "".join(word).split("m")
                             for i, char in enumerate(block) if char == "L")
            assert sum(map(len, record)) == 2 * inversions
            counts["shuffle words with barriers"] += 1
            counts["complete directed sortings"] += paths


def check_polygon_terms(emitter):
    # A long hom across two occupied columns. Give its extra 3-generators
    # positive two- and three-step boundaries, as in the marker reduction.
    k = (STAR, STAR, arr(STAR, v(0), v(1)), STAR, arr(STAR, v(1), v(3)))
    arrow = comp2(k, 0, v(2), v(4))
    k += (arr(k[2], v(2), v(2)), arr(k[4], v(4), v(4)))
    k += (arr(infer(k, arrow), arrow, arrow),)
    left = comp2(k, 0, v(5), v(4))
    right = comp2(k, 0, v(2), v(6))
    lr = comp2(k, 1, left, right)
    rl = comp2(k, 1, right, left)
    markers = comp2(k, 1, v(7), comp2(k, 1, v(7), v(7)))
    k += (arr(infer(k, lr), lr, markers), arr(infer(k, rl), markers, rl))
    arity = tree_ctx(glue_tree(3, 1, 3))
    slots = maximal_vars(arity)
    first, second = temporal_words(arity, *map(v, slots), 1, 2)
    label = sub_from(arity, k, dict(zip(slots, (v(8), v(9)))))
    for name, s, t in [('forward', first, second), ('backward', second, first)]:
        term = subst_tm(head(arity, s, t), label)
        source, target = subst_tm(s, label), subst_tm(t, label)
        expected = arr(infer(k, source), source, target)
        assert source != target and infer(k, term) == expected
        emitter.check_type('polygon-' + name, k, term, expected)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path, help='emit the directed raw boundary checks')
    args = parser.parse_args()
    counts = Counter()
    check_cubes(counts)
    check_shuffles(counts)
    emitter = Emitter()
    check_polygon_terms(emitter)
    if args.agda:
        module = emitter.module(args.agda.stem, 'Interchange inside a hom with polygon attachments.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n',
                                            'open import CaTTExp.Gray.Pure\n'))
    for label, count in sorted(counts.items()):
        print(f"{count:,} {label}")
    print("Both raw 4-boundaries checked for the two long-hom polygon generators.")
