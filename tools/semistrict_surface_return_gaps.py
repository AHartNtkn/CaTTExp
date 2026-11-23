"""Check finite gap tests and the middle-edge obstruction on contextual rewrites."""

from argparse import ArgumentParser
from collections import Counter, deque
from dataclasses import dataclass
from itertools import product
from pathlib import Path

from catt import arr, chain_tree, check_ctx, comp2, infer, src, tgt, tree_ctx, v
from emit_agda import Emitter
from semistrict_surface_scalar_cube import exchange


@dataclass(frozen=True)
class Rule:
    path: str
    source: tuple
    target: tuple


class Presentation:
    def __init__(self, edges, marks, rules):
        self.edges = edges
        self.marks = marks
        self.rules = rules
        for source, target in marks.values():
            assert self.poles(source) == self.poles(target)
        for rule in rules:
            assert rule.source and rule.target
            assert self.walk(rule.path, rule.source)[-1] == self.walk(rule.path, rule.target)[-1]

    def poles(self, path):
        assert path and all(self.edges[a][1] == self.edges[b][0] for a, b in zip(path, path[1:]))
        return self.edges[path[0]][0], self.edges[path[-1]][1]

    def walk(self, start, steps):
        paths = [start]
        for pos, mark in steps:
            source, target = self.marks[mark]
            path = paths[-1]
            assert 0 <= pos and path[pos:pos + len(source)] == source
            paths.append(path[:pos] + target + path[pos + len(source):])
        return paths

    def square(self, a, gap, b):
        sa, ta = self.marks[a]
        sb, _ = self.marks[b]
        start = sa + gap + sb
        self.poles(start)
        left = (0, a)
        sorted_steps = (left, (len(ta + gap), b))
        unsorted_steps = ((len(sa + gap), b), left)
        assert self.walk(start, sorted_steps)[-1] == self.walk(start, unsorted_steps)[-1]
        return start, sorted_steps, unsorted_steps

    def moves(self, start, steps):
        paths = self.walk(start, steps)
        for i, (pos, a) in enumerate(steps):
            # A forward square executes the spatially left event first.
            if i + 1 < len(steps):
                other_pos, b = steps[i + 1]
                sb, tb = self.marks[b]
                if other_pos + len(sb) <= pos:
                    replacement = ((other_pos, b), (pos + len(tb) - len(sb), a))
                    yield steps[:i] + replacement + steps[i + 2:], None
            for rule in self.rules:
                k = len(rule.source)
                offset = pos - rule.source[0][0]
                if offset < 0 or not paths[i].startswith(rule.path, offset):
                    continue
                lhs = tuple((offset + j, name) for j, name in rule.source)
                if steps[i:i + k] == lhs:
                    rhs = tuple((offset + j, name) for j, name in rule.target)
                    yield steps[:i] + rhs + steps[i + k:], (rule, i, offset)

    def reachable(self, start, steps, bound):
        end = self.walk(start, steps)[-1]
        seen = {steps}
        queue = deque(seen)
        while queue:
            for after, _ in self.moves(start, queue.popleft()):
                assert self.walk(start, after)[-1] == end
                if len(after) <= bound and after not in seen:
                    seen.add(after)
                    queue.append(after)
        return seen


def gap_outside_dictionary(edges, start, end, words):
    """Return a missing path, or None when every graph path is in the trie."""
    prefixes = {w[:i] for w in words for i in range(len(w) + 1)} | {''}
    queue = deque([(start, '', '')])
    seen = {(start, '')}
    while queue:
        vertex, prefix, path = queue.popleft()
        if vertex == end and prefix not in words:
            return path
        for edge, (s, t) in edges.items():
            if s != vertex:
                continue
            extension = prefix + edge if prefix is not None else None
            state = (t, extension if extension in prefixes else None)
            if state not in seen:
                seen.add(state)
                queue.append((*state, path + edge))
    return None


def separated_presentation(gaps, cyclic):
    edges = {'f': (0, 1), 'u': (0, 4), 'v': (4, 1),
             'g': (2, 3), 'i': (2, 5), 'j': (5, 3),
             'h': (1, 1 if cyclic else 2), 'k': (1, 2)}
    marks = {'a': ('f', 'uv'), 'b': ('g', 'ij')}
    rules = []
    bare = Presentation(edges, marks, [])
    for m, mode in gaps:
        start, lr, rl = bare.square('a', m, 'b')
        middle = 'Q' + m
        if mode == 'first':
            marks[middle] = start, 'uv' + m + 'g'
            rules.extend((Rule(start, lr[:1], ((0, middle),)),
                          Rule(start, ((0, middle), lr[1]), rl)))
        elif mode == 'second':
            path = 'uv' + m + 'g'
            marks[middle] = path, 'uv' + m + 'ij'
            rules.extend((Rule(path, lr[1:], ((0, middle),)),
                          Rule(start, (lr[0], (0, middle)), rl)))
        else:
            rules.append(Rule(start, lr, rl))
    return Presentation(edges, marks, rules)


def check_dictionary(counts):
    for cyclic in (False, True):
        gaps = [n * 'h' + 'k' for n in range(4)] if cyclic else ['h', 'k']
        for choices in product((None, 'direct', 'first', 'second'), repeat=len(gaps)):
            chosen = [(m, mode) for m, mode in zip(gaps, choices) if mode]
            pres = separated_presentation(chosen, cyclic)
            dictionary = {''} | {rule.path[i:j] for rule in pres.rules
                                   for i in range(len(rule.path)) for j in range(i + 1, len(rule.path) + 1)}
            missing = gap_outside_dictionary(pres.edges, 1, 2, dictionary)
            assert (missing is None) == (not cyclic and len(chosen) == len(gaps))
            probes = set(gaps)
            if missing is not None:
                probes.add(missing)
            for m in probes:
                start, lr, rl = pres.square('a', m, 'b')
                moves = list(pres.moves(start, lr))
                assert (rl in pres.reachable(start, lr, 2)) == any(g == m for g, _ in chosen)
                for _, (rule, i, offset) in moves:
                    current = pres.walk(start, lr[:i])[-1]
                    gap_pos = current.index(m)
                    assert offset <= gap_pos and gap_pos + len(m) <= offset + len(rule.path)
                    counts['literal gaps covered by first rule windows'] += 1
                counts['basic squares searched'] += 1
            counts['dictionary inclusion decisions'] += 1


def check_middle_edge(counts):
    # A polygon can act entirely on the left alongside b. Its two output steps
    # shorten the intermediate spatial path and restore it at the next step.
    edges = {'f': (0, 1), 'u': (0, 3), 'v': (3, 1), 'h': (1, 1),
             'g': (1, 2), 'i': (1, 4), 'j': (4, 2)}
    marks = {'a': ('f', 'uv'), 'b': ('g', 'ij'), 'p': ('fh', 'f'),
             'q': ('f', 'uvh'), 'd': ('uv', 'f'), 'e': ('f', 'f')}
    split = Rule('fh', ((0, 'a'),), ((0, 'p'), (0, 'q')))
    # At an empty gap a declared binary return crosses the separating cut.
    bare = Presentation(edges, marks, [])
    start, lr, rl = bare.square('a', '', 'b')
    rules = [split, Rule(split.path, split.target, split.source), Rule(start, lr, rl),
             Rule('uv', ((0, 'd'),), ((0, 'd'), (0, 'e')))]
    pres = Presentation(edges, marks, rules)
    assert rl in pres.reachable(start, lr, 2)
    k = max(len(s) for s, _ in marks.values())
    width = max(len(rule.path) for rule in rules)
    for height in range(2, 6):
        for extra in range(3):
            n = 2 * (height * k + width) + 1 + extra
            for a in ('a', 'p', 'q', 'd', 'e'):
                sa, _ = marks[a]
                start, lr, rl = pres.square(a, 'h' * n, 'b')
                normal = pres.reachable(start, lr, height)
                reversed_start = pres.reachable(start, rl, height)
                assert rl not in normal and lr in reversed_start
                for steps in normal | reversed_start:
                    # Follow the actual surviving edge through this history.
                    position = len(sa) + n // 2
                    sides = []
                    for offset, name in steps:
                        source, target = marks[name]
                        if offset + len(source) <= position:
                            position += len(target) - len(source)
                            sides.append('L')
                        else:
                            assert offset > position
                            sides.append('R')
                    if steps in normal:
                        assert sides == sorted(sides)
                    counts['histories traced at a protected edge'] += 1
                counts['bounded searches with a polygon beside a mark'] += 1


def check_graph_reduction(counts):
    edges = {'f': (0, 1), 'g': (1, 2)}
    states = 'xyz'
    marks = {q: ('fg', 'fg') for q in states + '#'}
    marks.update(a=('f', 'f'), b=('g', 'g'))
    bare = Presentation(edges, marks, [])
    start, lr, rl = bare.square('a', '', 'b')
    pairs = [(i, j) for i in states for j in states if i != j]

    def marked(q):
        return ((0, q), (0, '#'))

    for flags in product((False, True), repeat=len(pairs)):
        arcs = [p for p, yes in zip(pairs, flags) if yes]
        graph = set(arcs) | {(q, q) for q in states}
        for pivot in states:
            graph.update((s, t) for s in states for t in states
                         if (s, pivot) in graph and (pivot, t) in graph)
        for s, t in product(states, repeat=2):
            rules = [Rule(start, marked(i), marked(j)) for i, j in arcs]
            rules += [Rule(start, lr, marked(s)), Rule(start, marked(t), rl)]
            pres = Presentation(edges, marks, rules)
            assert (rl in pres.reachable(start, lr, 2)) == ((s, t) in graph)
            counts['graph reachability reductions'] += 1


def raw_graph_return():
    ctx = tree_ctx(chain_tree(2))
    f, g = v(2), v(4)
    a, b = v(len(ctx)), v(len(ctx) + 1)
    ctx += (arr(infer(ctx, f), f, f), arr(infer(ctx, g), g, g))
    square = exchange(ctx, a, b)
    rl, lr = src(ctx, square), tgt(ctx, square)
    letter_type = infer(ctx, lr)
    q, r, d = (v(i) for i in range(len(ctx), len(ctx) + 3))
    ctx += (letter_type,) * 3
    qd, rd = comp2(ctx, 1, q, d), comp2(ctx, 1, r, d)
    begin, edge, end = (v(i) for i in range(len(ctx), len(ctx) + 3))
    ctx += (arr(letter_type, lr, qd), arr(letter_type, qd, rd), arr(letter_type, rd, rl))
    check_ctx(ctx)
    witness = comp2(ctx, 2, comp2(ctx, 2, begin, edge), end)
    expected = arr(letter_type, lr, rl)
    assert infer(ctx, witness) == expected
    emitter = Emitter()
    emitter.check_type('return', ctx, witness, expected)
    return emitter


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    totals = Counter()
    check_dictionary(totals)
    check_middle_edge(totals)
    check_graph_reduction(totals)
    emitter = raw_graph_return()
    if args.agda:
        module = emitter.module(args.agda.stem, 'Return along one directed graph edge.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n',
                                            'open import CaTTExp.Gray.Pure\n'))
    for label, count in sorted(totals.items()):
        print(f'{count:,} {label}')
