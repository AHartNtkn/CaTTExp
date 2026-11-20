"""Compressed observations of divisors of a common two-row grid path.

Each rank-three or rank-four input letter names its two active sites.
Axes supplied to an observer are subsequences in processing order.
Rank-one and rank-two observers just measure chronological length.
"""

from itertools import combinations

from interchange_rigid_readers import ReaderCodes
from interchange_shared_whiskers import Words


def pair_axes(names):
    for size in (1, 2):
        yield from combinations(names, size)


class CornerReader:
    """Erase other tiles and normalize the one possible four-letter relation."""

    redex = (0, 2, 1, 3)
    replacement = (0, 1, 2, 3)

    def __init__(self, raw, rows, cols, reverse=False):
        self.raw = raw
        self.reverse = reverse
        self.labels = None if rows is None else {
            (r, c): 2*i+j for i, r in enumerate(rows) for j, c in enumerate(cols)
        }
        self.output = Words()
        self.cache = {}

    def emit(self, symbols):
        word = 0
        for symbol in symbols:
            word = self.output.join(word, self.output.letter(symbol))
        return word

    def finish(self, state):
        return self.emit(state)

    def step(self, state, tile):
        if self.labels is None:
            return (), self.output.letter(0)
        if tile not in self.labels:
            return state, 0
        value = self.labels[tile]
        pending = state + (3-value if self.reverse else value,)
        if pending == self.redex:
            return (), self.emit(self.replacement)
        # Keep the longest suffix that can still begin the redex.
        start = 0
        while pending[start:] != self.redex[:len(pending)-start]:
            start += 1
        return pending[start:], self.emit(pending[:start])

    def run(self, state, root):
        pending = [(state, root)]
        while pending:
            key = pending[-1]
            if key in self.cache:
                pending.pop()
                continue
            entering, node = key
            rule = self.raw.rules[node]
            if not rule:
                result = entering, 0
            elif len(rule) == 1:
                result = self.step(entering, rule[0])
            else:
                first, second = (~ref for ref in (rule[::-1] if self.reverse else rule))
                left = entering, first
                if left not in self.cache:
                    pending.append(left)
                    continue
                middle, prefix = self.cache[left]
                right = middle, second
                if right not in self.cache:
                    pending.append(right)
                    continue
                final, suffix = self.cache[right]
                result = final, self.output.join(prefix, suffix)
            self.cache[key] = result
            pending.pop()
        return self.cache[state, root]


def rigid_coordinates(rules, raw, row_names, col_names):
    """Compare upper grammar nodes at a common source, retaining every rigid head.

    A ('pad', rank, left, child, right) rule uses raw SLP references for
    the two low pads. Other rules are the upper instructions of ReaderCodes.
    The names at ranks 3 and 4 are ordered in their respective sweep orders.
    """
    for rank in range(1, 5):
        observed = []
        for rule in rules:
            if rule[0] == 'pad':
                _, acting_rank, left, child, right = rule
                low = ('base', left, child, right) if rank == acting_rank else ('base', 0, child, 0)
                observed.append(low)
            else:
                observed.append(rule)
        axes = ((rows, cols) for rows in pair_axes(row_names[rank])
                for cols in pair_axes(col_names[rank])) if rank >= 3 else [(None, None)]
        for rows, cols in axes:
            for reverse in (False, True):
                reader = CornerReader(raw, rows, cols, reverse)
                yield ReaderCodes(observed, reader, rank, reverse)
