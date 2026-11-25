"""Replay positioned string rewrites as ordinary CaTT witnesses at heterogeneous compound poles."""

import argparse
from collections import deque
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, chain_tree, check_ctx, coh_between, comp2, fv_tm, glue_tree,
                  infer, maximal_vars, tdim, tdim_tm, tree_ctx, ucomp, v)
from relative_coherence_hidden_seam import identity
from semistrict_surface_compound_words import base_bridge, fold
from semistrict_surface_equal_rank import suspend
from semistrict_surface_flat_heads import check_weak
from semistrict_surface_grid_tracks import temporal
from semistrict_surface_rank_cut import RankCut
from semistrict_surface_strict_factors import height, proper_factors, strict


def rewrites(word, lhs, rhs):
    for pos in range(len(word) - len(lhs) + 1):
        if word[pos:pos + len(lhs)] == lhs:
            yield pos, word[:pos] + rhs + word[pos + len(lhs):]


def search(rules, source, target, counts=None, weights=None):
    """BFS with exact budgets or checked positive weight bounds; otherwise semidecide."""
    if counts is not None:
        counts = tuple(counts)
        if len(counts) != len(rules) or any(type(n) is not int or n < 0 for n in counts):
            raise ValueError('Expected a nonnegative count per rule')
    limit = None
    if weights is not None:
        letters = set(source + target).union(*(set(a + b) for a, b in rules))
        if any(type(weights[x]) is not int or weights[x] <= 0 for x in letters):
            raise ValueError('Expected positive integer letter weights')
        def weight(w):
            return sum(weights[x] for x in w)
        differences = [weight(b) - weight(a) for a, b in rules]
        if all(d <= 0 for d in differences):
            limit = weight(source)
        elif all(d >= 0 for d in differences):
            limit = weight(target)
        else:
            raise ValueError('Supplied weights do not bound the search')
    initial = (source, counts)
    queue, parents = deque([initial]), {initial: None}
    while queue:
        state = queue.popleft()
        word, budget = state
        if word == target and (budget is None or not any(budget)):
            moves = []
            while parents[state] is not None:
                state, move = parents[state]
                moves.append(move)
            return list(reversed(moves))
        for i, (a, b) in enumerate(rules):
            if budget is not None and not budget[i]:
                continue
            rest = None if budget is None else budget[:i] + (budget[i] - 1,) + budget[i + 1:]
            for pos, result in rewrites(word, a, b):
                if limit is not None and weight(result) > limit:
                    continue
                new = result, rest
                if new not in parents:
                    parents[new] = state, (i, pos)
                    queue.append(new)
    return None


class Serial:
    def __init__(self, base, names, rank, pole=None):
        check_ctx(base)
        if rank < 2 or any(tdim(t) + 1 >= rank or
                           (t != STAR and any(x[0] != 'v' for x in t[2:])) for t in base):
            raise ValueError('Expected a lower globular base')
        if not names and pole is None:
            raise ValueError('Supply a reference pole when there are no letters')
        self.pole = names[0][0] if pole is None else pole
        if (tdim_tm(base, self.pole) != rank - 1 or
                not any(tdim(base[i]) + 1 == rank - 1 for i in fv_tm(self.pole))):
            raise ValueError('The reference pole needs a positive top-dimensional occurrence')
        self.base = base
        self.rank = rank
        self.names = tuple(v(len(base) + i) for i in range(len(names)))
        self.ctx = base + tuple(arr(infer(base, a), a, b) for a, b in names)
        self.bridges = {}
        self.poles = {strict(base, self.pole)}
        for a, b in names:
            self.check_poles(a, b)
        self.rules = []
        self.types = []
        self.arrows = []
        self.arity = tree_ctx(glue_tree(rank, rank - 1, rank))
        self.binary = ucomp(self.arity)
        self.binary_tips = maximal_vars(self.arity)

    def check_poles(self, a, b):
        poles = self.poles.copy()
        for x in (a, b):
            if infer(self.base, x) != infer(self.base, self.pole):
                raise ValueError('The lower poles must be literally parallel')
            d = strict(self.base, x)
            if d in poles:
                continue
            if height(d) != self.rank - 1:
                raise ValueError('Each pole needs a top-dimensional occurrence')
            if any(y in proper_factors(d) or d in proper_factors(y) for y in poles):
                raise ValueError('One strict pole is a proper factor of another')
            poles.add(d)
        self.poles = poles

    def bridge(self, a, b):
        if (a, b) not in self.bridges:
            self.bridges[a, b] = identity(self.base, a) if a == b else base_bridge(self.base, a, b)
        return self.bridges[a, b]

    def parse(self, term):
        leaves = []
        def visit(x):
            if x in self.names or not fv_tm(x).intersection(z[1] for z in self.names):
                leaves.append(x)
                return len(leaves) - 1
            if x[0] == 'coh' and x[1:3] == self.binary[1:3]:
                return tuple(visit(x[3][i]) for i in self.binary_tips)
            raise ValueError('Input is outside the serial word class')
        pattern = visit(term)
        return pattern, leaves

    def word(self, term):
        return tuple(self.names.index(x) for x in self.parse(term)[1] if x in self.names)

    def normal(self, word, source, target):
        parts = []
        at = source
        for index in word:
            z = self.names[index]
            start, end = infer(self.ctx, z)[2:]
            parts.extend([self.bridge(at, start), z])
            at = end
        parts.append(self.bridge(at, target))
        return fold(self.ctx, parts, self.rank - 1)

    def normalize(self, term, reverse=False):
        ctx, rank = self.ctx, self.rank
        pattern, leaves = self.parse(term)
        tree = suspend(chain_tree(len(leaves)), rank - 1)
        shape = tree_ctx(tree)
        pos = [v(i) for i in maximal_vars(shape)]
        def read(p):
            return pos[p] if isinstance(p, int) else temporal(shape, read(p[0]), read(p[1]))
        original = read(pattern)
        gaps, events = [[]], []
        for i, x in enumerate(leaves):
            if x in self.names:
                events.append(i)
                gaps.append([])
            else:
                gaps[-1].append(i)
        def pieces(G, labels):
            result = []
            for j, gap in enumerate(gaps):
                if gap:
                    result.append(fold(G, [labels[i] for i in gap], rank - 1))
                else:
                    if j < len(events):
                        seam = infer(G, labels[events[j]])[2]
                    else:
                        seam = infer(G, labels[events[-1]])[3]
                    result.append(identity(G, seam))
                if j < len(events):
                    result.append(labels[events[j]])
            return result
        grouped = fold(shape, pieces(shape, pos), rank - 1)
        faces = (grouped, original) if reverse else (original, grouped)
        reg = coh_between(ctx, tree, leaves, *faces)
        moves = []
        for j, x in enumerate(pieces(ctx, leaves)):
            if j % 2:
                moves.append(identity(ctx, x))
                continue
            canonical = self.bridge(*infer(ctx, x)[2:])
            ends = (canonical, x) if reverse else (x, canonical)
            moves.append(identity(ctx, x) if x == canonical else base_bridge(self.base, *ends))
        changed = fold(ctx, moves, rank - 1)
        return temporal(ctx, changed, reg) if reverse else temporal(ctx, reg, changed)

    def same(self, a, b):
        if a == b:
            return identity(self.ctx, a)
        if self.word(a) != self.word(b) or infer(self.ctx, a) != infer(self.ctx, b):
            raise ValueError('Expected two spellings of the same word at identical poles')
        result = temporal(self.ctx, self.normalize(a), self.normalize(b, True))
        assert infer(self.ctx, result)[2:] == (a, b)
        return result

    def declare(self, a, b):
        ty = infer(self.ctx, a)
        if infer(self.ctx, b) != ty:
            raise ValueError('Rule faces must be parallel')
        self.check_poles(*ty[2:])
        self.rules.append((self.word(a), self.word(b)))
        self.types.append(ty)
        self.arrows.append(v(len(self.ctx)))
        self.ctx += (arr(ty, a, b),)

    def typed_search(self, source, target, counts=None, weights=None):
        ty = infer(self.ctx, source)
        if infer(self.ctx, target) != ty:
            raise ValueError('Query faces must be parallel')
        self.check_poles(*ty[2:])
        def encode(term):
            word = self.word(term)
            indices = [infer(self.ctx, term)[2]] + [infer(self.ctx, self.names[j])[3] for j in word]
            poles = [strict(self.base, x) for x in indices]
            encoded = [('pole', poles[0])]
            for j, d in zip(word, poles[1:]):
                encoded.extend([('letter', j), ('pole', d)])
            return tuple(encoded)
        rules = [(encode(self.ctx[g[1]][2]), encode(self.ctx[g[1]][3])) for g in self.arrows]
        weighted = None
        if weights is not None:
            weighted = {('pole', d): 1 for d in self.poles}
            weighted.update({('letter', j): 2 * w - 1 for j, w in weights.items()})
        history = search(rules, encode(source), encode(target), counts, weighted)
        if history is None:
            return None
        assert all(pos % 2 == 0 for _, pos in history)
        return [(rule, pos // 2) for rule, pos in history]

    def replay(self, source, target, moves):
        ctx, rank = self.ctx, self.rank
        poles = infer(ctx, source)
        if infer(ctx, target) != poles:
            raise ValueError('Query faces must be parallel')
        self.check_poles(*poles[2:])
        word, current, cells = self.word(source), source, []
        for i, pos in moves:
            a, b = self.rules[i]
            if not 0 <= pos <= len(word) - len(a) or word[pos:pos + len(a)] != a:
                raise ValueError('Mismatch at the specified rewrite position')
            start, end = self.types[i][2:]
            prefix = self.normal(word[:pos], poles[2], start)
            suffix = self.normal(word[pos + len(a):], end, poles[3])
            change = comp2(ctx, rank - 1, comp2(ctx, rank - 1, prefix, self.arrows[i]), suffix)
            left, right = infer(ctx, change)[2:]
            cells.extend([self.same(current, left), change])
            word = word[:pos] + b + word[pos + len(a):]
            current = right
        cells.append(self.same(current, target))
        # Balance long chronological proofs; all intermediate faces are literal.
        while len(cells) > 1:
            cells = [temporal(ctx, cells[j], cells[j + 1]) if j + 1 < len(cells) else cells[j]
                     for j in range(0, len(cells), 2)]
        witness, = cells
        assert infer(ctx, witness) == arr(poles, source, target)
        return witness


DOUBLE = tuple((tuple(a), tuple(b)) for a, b in
               [('Lq', 'LF'), ('Fa', 'aaF'), ('FR', 'BR'), ('aB', 'Ba'),
                ('LB', 'Lq'), ('Lq', 'LD'), ('Da', 'D')])


def doubling_budgets(n):
    copied = 2 ** n - 1
    return (n, copied, n, 2 * copied, n, 1, copied + 1)


def examples(rank, checker):
    tree = suspend(chain_tree(3), rank - 2)
    base = tree_ctx(tree)
    p = ucomp(base)
    q = fold(base, [v(i) for i in maximal_vars(base)], rank - 2)
    assert p != q
    serial = Serial(base, [(p, q), (q, p), (q, q), (p, p)], rank)
    a, b, c, d = serial.names
    # An expanding rule, a contraction at different lower endpoints, and a birth.
    def norm(w, s, t):
        return serial.normal(w, s, t)
    serial.declare(a, norm((1, 2), p, q))
    serial.declare(norm((2, 3), q, p), b)
    serial.declare(identity(base, q), norm((3,), q, q))
    source, target = norm((0,), q, p), norm((1, 1), q, p)
    hist = search(serial.rules, serial.word(source), serial.word(target), (1, 1, 1))
    assert hist is not None
    witness = serial.replay(source, target, hist)
    if checker:
        check_weak(checker, serial.ctx, witness, arr(infer(serial.ctx, source), source, target))
    assert search(serial.rules, (0,), (1, 1), (1, 1, 0)) is None
    assert search(serial.rules[:2], (0, 3), (1, 1), weights={0: 3, 1: 2, 2: 1, 3: 1}) is not None


def doubling_raw(checker):
    rank = 5
    base = tree_ctx(suspend(chain_tree(2), rank - 2))
    p = ucomp(base)
    letters = sorted(set('LqFaRBD'))
    ids = {x: i for i, x in enumerate(letters)}
    serial = Serial(base, [(p, p)] * len(letters), rank)
    def spell(w):
        return fold(serial.ctx, [serial.names[ids[x]] for x in w], rank - 1)
    for a, b in DOUBLE:
        serial.declare(spell(a), spell(b))
    for n in (0, 1):
        history = search(DOUBLE, tuple('LqaR'), tuple('LDR'), doubling_budgets(n))
        s, t = spell('LqaR'), spell('LDR')
        witness = serial.replay(s, t, history)
        if checker:
            check_weak(checker, serial.ctx, witness, arr(infer(serial.ctx, s), s, t))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path)
    opts = parser.parse_args()
    for n, adjustment in product(range(6), (-1, 0, 1)):
        counts = list(doubling_budgets(n))
        counts[-1] += adjustment
        result = search(DOUBLE, tuple('LqaR'), tuple('LDR'), counts)
        assert (result is not None) == (adjustment == 0)
    print('18 exact-budget tests distinguish the doubling counts from adjacent counts', flush=True)
    with TemporaryDirectory() as tmp:
        checker = RankCut(6, opts.checker.resolve(), Path(tmp)) if opts.checker else None
        for rank in (2, 3, 5):
            examples(rank, checker)
            print(f'Degree {rank+1}: expansion, empty-position insertion and contraction at distinct poles', flush=True)
        doubling_raw(checker)
        print('Two complete degree-six doubling histories replayed at their literal boundaries', flush=True)
