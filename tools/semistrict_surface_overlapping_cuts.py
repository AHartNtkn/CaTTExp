"""Check joint cancellation, corners of shared-rule cubes and a nested old 6-type."""
from argparse import ArgumentParser
from collections import defaultdict
from functools import cache
from itertools import combinations
from pathlib import Path

from catt import STAR, arr, comp2, glue_tree, infer, maximal_vars, sub_from, subst_tm, tree_ctx, v
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from semistrict_surface_product_histories import readings, replay, switch


class Diagrams:
    """Strict planar diagrams, identified only by literal disjoint interchanges."""

    def __init__(self, rules):
        self.rules = rules
        self.classes = {}

    @cache
    def lists(self, word, length):
        if not length:
            return ((),)
        return tuple(((r, i),) + tail for r, (p, q) in enumerate(self.rules)
                     for i in range(len(word) + 1) if word.startswith(p, i)
                     for tail in self.lists(word[:i] + q + word[i + len(p):], length - 1))

    def play(self, word, history):
        for r, i in history:
            p, q = self.rules[r]
            assert word.startswith(p, i)
            word = word[:i] + q + word[i + len(p):]
        return word

    def neighbors(self, hist):
        for k, ((a, x), (b, y)) in enumerate(zip(hist, hist[1:])):
            p, q = self.rules[a]
            s, t = self.rules[b]
            if y + len(s) <= x:
                yield hist[:k] + ((b, y), (a, x + len(t) - len(s))) + hist[k + 2:]
            if x + len(q) <= y:
                yield hist[:k] + ((b, y + len(p) - len(q)), (a, x)) + hist[k + 2:]

    def equivalents(self, hist):
        if hist not in self.classes:
            seen = {hist}
            pending = [hist]
            while pending:
                for nxt in self.neighbors(pending.pop()):
                    if nxt not in seen:
                        seen.add(nxt)
                        pending.append(nxt)
            cls = min(seen), tuple(sorted(seen))
            self.classes.update(dict.fromkeys(seen, cls))
        return self.classes[hist]

    def cell(self, word, hist):
        return word, self.equivalents(hist)[0]

    def factor(self, word, hist, cuts):
        last, parts = 0, []
        for end in (*cuts, len(hist)):
            part = hist[last:end]
            parts.append(self.cell(word, part))
            word, last = self.play(word, part), end
        return tuple(parts)

    def germs(self, word, hist, marks):
        return tuple(self.factor(word, hist, (i, i + 1)) for i in marks)


def overlaps():
    # Births can never be destroyed: a built wire is 'a', a destroyed wire is 'b'.
    diagrams = Diagrams((('', 'a'), ('b', ''), ('', ''), ('ab', 'ba')))
    left, right, both = defaultdict(set), defaultdict(set), {}
    classes, processed = set(), 0
    for word in ('', 'b', 'ab', 'bb'):
        for h in diagrams.lists(word, 4):
            classes.add(diagrams.cell(word, h))
            for i, j in combinations(range(5), 2):
                g, m, k = diagrams.factor(word, h, (i, j))
                gm, _ = diagrams.factor(word, h, (j,))
                _, mk = diagrams.factor(word, h, (i,))
                left[g, gm].add(m)
                right[k, mk].add(m)
                assert both.setdefault((g, gm, mk, k), m) == m
                processed += 1
    assert any(len(v) > 1 for v in left.values()) and any(len(v) > 1 for v in right.values())
    corners = 0
    for word, normal in classes:
        # Use one positive 3-loop on each possible literal one-box 2-cell.
        # Independently compare 3-cubes with triangles in the link.
        squares, triples = {}, {}
        for hist in diagrams.equivalents(normal)[1]:
            for size, cubes in ((2, squares), (3, triples)):
                for marks in combinations(range(len(hist)), size):
                    germs = frozenset(diagrams.germs(word, hist, marks))
                    cuts = tuple(c for i in marks for c in (i, i + 1))
                    data = diagrams.factor(word, hist, cuts)
                    assert len(germs) == size and cubes.setdefault(germs, data) == data
        adjacency = defaultdict(set)
        for pair in squares:
            a, b = pair
            adjacency[a].add(b)
            adjacency[b].add(a)
        cliques = {frozenset((a, b, c)) for a in adjacency for b in adjacency[a]
                   for c in adjacency[a] & adjacency[b]}
        assert cliques == set(triples)
        corners += len(triples)
    # A wire-bearing bubble. The transfer past a common birth and the
    # transfer before two common deaths have different middle diagrams.
    bubble = Diagrams((('', 'a'), ('a', '')))
    birth = ((0, 0),)
    l, r = ((0, 1),), ((0, 0),)
    deaths = ((1, 0), (1, 0))
    assert bubble.cell('a', l) != bubble.cell('a', r)
    assert bubble.cell('', birth + l) == bubble.cell('', birth + r)
    assert bubble.cell('a', l + deaths) == bubble.cell('a', r + deaths)
    print(f'{processed} overlap tests, {len(classes)} planar classes, {corners} triple corners')


@cache
def normal_reading(path):
    for k in range(len(path) - 1):
        nxt = switch(path, k)
        if nxt is not None:
            return normal_reading(nxt)
    return path


def iterated_cancellation():
    # The first three rules have positive total input and output on the two tapes.
    left, right, cuts = {}, {}, 0
    for start in (('ab', 'cd'), ('aa', 'cc'), ('b', 'c')):
        for length in range(2, 5):
            for path in readings(start, length, range(3)):
                whole = start, normal_reading(path)
                for i in range(1, length):
                    prefix = start, normal_reading(path[:i])
                    mid = replay(start, path[:i])
                    suffix = mid, normal_reading(path[i:])
                    assert left.setdefault((whole, prefix), suffix) == suffix
                    assert right.setdefault((whole, suffix), prefix) == prefix
                    cuts += 1
    print(f'{cuts} cuts in length-changing two-tape 3-readings checked in both directions')


def nested_witness(directory):
    ctx = (STAR, STAR, STAR)
    for i in range(2):
        ctx += (arr(STAR, v(i), v(i + 1)),) * 3
    # Two temporal stages in each of two spatial columns.
    for i in (3, 6):
        ctx += (arr(ctx[i], v(i), v(i + 1)), arr(ctx[i], v(i + 1), v(i + 2)))
    u, w = comp2(ctx, 0, v(9), v(11)), comp2(ctx, 0, v(10), v(12))
    ctx += (arr(infer(ctx, u), u, u),) * 2 + (arr(infer(ctx, w), w, w),) * 2
    first, last = comp2(ctx, 1, v(13), v(15)), comp2(ctx, 1, v(14), v(16))
    ctx += (arr(infer(ctx, first), first, last),)
    pair = tree_ctx(glue_tree(4, 2, 4))
    peaks = maximal_vars(pair)
    early, late = temporal_words(pair, *map(v, peaks), 2, 3)
    loop = comp2(pair, 4, head(pair, early, late), head(pair, late, early))
    unit = ident(pair, early)
    labels = sub_from(pair, ctx, dict.fromkeys(peaks, v(17)))
    raw = subst_tm(head(pair, loop, unit), labels)
    x, y = (subst_tm(t, labels) for t in (loop, unit))
    expected = arr(infer(ctx, x), x, y)
    assert x != y and infer(ctx, raw) == expected
    if directory:
        directory.mkdir(parents=True, exist_ok=True)
        emitter = Emitter()
        emitter.check_typed('nested', ctx, raw)
        emitter.check_type('nested-faces', ctx, raw, expected)
        name = 'NestedSharedInterchange'
        (directory / (name + '.agda')).write_text(emitter.module(name, __doc__))
    print('Raw 6-cell over a shared 4-generator comparing two pairs of spanning 3-rules')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    overlaps()
    iterated_cancellation()
    nested_witness(args.agda_dir)
