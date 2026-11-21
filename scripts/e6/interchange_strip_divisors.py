"""Divisor coordinates for prepared rigid paths over a shared two-chain strip.

A lower slice lists stationary edges in chronological order and binary moving
run lengths before, between and after them. A base pad starts at this slice.
Rules are typed; 'strip' pads carry Pad objects and 'flank' pads carry Slices.
All upper instructions use the ReaderCodes convention.
"""

from dataclasses import dataclass
from itertools import combinations

from interchange_rigid_readers import ReaderCodes
from interchange_shared_whiskers import Words


@dataclass(frozen=True)
class Slice:
    marks: tuple = ()
    runs: tuple = (0,)

    def __post_init__(self):
        if len(self.runs) != len(self.marks) + 1 or min(self.runs) < 0:
            raise ValueError("invalid moving runs in strip slice")

    def reverse(self):
        return Slice(self.marks[::-1], self.runs[::-1])

    def join(self, other):
        return Slice(self.marks + other.marks,
                     self.runs[:-1] + (self.runs[-1] + other.runs[0],) + other.runs[1:])

    def project(self, pair, modulus):
        marks, runs = [], [self.runs[0]]
        for mark, n in zip(self.marks, self.runs[1:]):
            if mark in pair:
                marks.append(mark)
                runs.append(0)
            runs[-1] += n
        # Preserve exact zero separately from a positive multiple.
        return Slice(tuple(marks), tuple(1 + (n-1) % modulus if n else 0 for n in runs))

    def symbols(self):
        return len(self.marks) + sum(self.runs)


@dataclass(frozen=True)
class Pad:
    start: Slice
    word: int


@dataclass(frozen=True)
class Walk:
    up: int = 0
    down: int = 0
    minimum: int = 0
    down_at_last_min: int = 0

    def then(self, other):
        right_min = self.up - self.down + other.minimum
        return Walk(self.up + other.up, self.down + other.down,
                    min(self.minimum, right_min),
                    self.down + other.down_at_last_min if right_min <= self.minimum
                    else self.down_at_last_min)


def walks(raw, pair, reverse):
    """Directional two-row projected walks, including their empty prefix."""
    result = [Walk()]
    for rule in raw.rules[1:]:
        if len(rule) == 1:
            r = rule[0]
            result.append(Walk(up=1) if r == pair[0] else
                          Walk(0, 1, -1, 1) if r == pair[1] else Walk())
        else:
            a, b = (~i for i in rule)
            first, second = (b, a) if reverse else (a, b)
            result.append(result[first].then(result[second]))
    return result


class Contacts:
    """No output until a head. A positive contact resets the stored column."""
    def __init__(self, raw, pair, modulus, reverse):
        self.pair = pair[::-1] if reverse else pair
        self.reverse = reverse
        self.modulus = modulus
        self.walks = walks(raw, self.pair, reverse)
        self.output = Words()

    def finish(self, state):
        _, _, column = state
        return 0 if column is None else self.output.letter(column)

    def run(self, state, instruction):
        left, right, column = state
        kind, *args = instruction
        if kind == 'flank':
            pre, post = args
            if self.reverse:
                pre, post = post.reverse(), pre.reverse()
            return (left.join(pre).project(self.pair, self.modulus),
                    post.join(right).project(self.pair, self.modulus), column), 0

        pad, = args
        walk = self.walks[pad.word]
        if not (walk.up or walk.down):
            return state, 0
        width = sum(pad.start.runs)
        local = {}
        pos = pad.start.runs[0]
        for r, n in zip(pad.start.marks, pad.start.runs[1:]):
            if r in self.pair:
                advances = walk.up if r == self.pair[0] else walk.down
                local[r] = width - pos - advances if self.reverse else pos
            pos += n
        u, d = self.pair
        origin = sum(left.runs)
        if u in local and d in local:
            if local[u] - local[d] + walk.minimum == 0:
                column = (origin + local[d] + walk.down_at_last_min) % self.modulus
        elif u in local and d in left.marks:
            # Internal U can only move away from exterior D.
            if local[u] == 0 and not any(left.runs[left.marks.index(d)+1:]):
                column = origin % self.modulus
        elif d in local and u in right.marks:
            # Internal D can only approach exterior U.
            if local[d] + walk.down == width and not any(right.runs[:right.marks.index(u)+1]):
                column = (origin + width) % self.modulus
        return (left, right, column), 0


class Lengths:
    def __init__(self, raw, row):
        self.row = row
        self.output = Words()
        self.counts = [0]
        for rule in raw.rules[1:]:
            self.counts.append(int(rule[0] == row) if len(rule) == 1
                               else sum(self.counts[~child] for child in rule))

    def finish(self, state):
        return 0

    def run(self, state, item):
        if isinstance(item, Slice):
            n = item.symbols() if self.row is None else 0
        else:
            n = self.counts[item.word] if self.row is not None else 0
        out, power = 0, self.output.letter(0)
        while n:
            if n & 1:
                out = self.output.join(out, power)
            n //= 2
            if n:
                power = self.output.join(power, power)
        return state, out


def coordinates(rules, raw, rows, width, base_rank):
    """Yield separate (code, initial state); never construct their product."""
    for reverse in (False, True):
        lengths, contacts = [], []
        for rule in rules:
            if rule[0] in ('flank', 'strip'):
                kind, left, child, right = rule
                lengths.append(('base', left, child, right))
                instruction = (('flank', left, right) if kind == 'flank'
                               else ('strip', right if reverse else left))
                contacts.append(('base', instruction, child, instruction))
            else:
                lengths.append(rule)
                contacts.append(rule)
        for row in (*rows, None):
            reader = Lengths(raw, row)
            yield ReaderCodes(lengths, reader, base_rank if row is not None else base_rank-1,
                              reverse), ()
        for pair in combinations(rows, 2):
            for modulus in range(2, 2*(width.bit_length()+2)+1):
                reader = Contacts(raw, pair, modulus, reverse)
                yield ReaderCodes(contacts, reader, base_rank, reverse), (Slice(), Slice(), None)
