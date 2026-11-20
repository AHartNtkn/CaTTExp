"""Compare rigid chronological paths under shared immediate whiskerings.

Lower pads are SLP words in a faithful free alphabet. Right pads are stored
in reverse order, so both context coordinates change by prepending a word.
Top inputs are parallel and use previously classified intrinsic rigid labels.
"""

from dataclasses import dataclass

from interchange_shared_paths import compressed_equal


class Words:
    def __init__(self):
        self.rules = [()]
        self.length = [0]
        self.indices = {(): 0}

    def intern(self, rule, size):
        if rule not in self.indices:
            self.indices[rule] = len(self.rules)
            self.rules.append(rule)
            self.length.append(size)
        return self.indices[rule]

    def letter(self, name):
        return self.intern((name,), 1)

    def join(self, x, y):
        if not x or not y:
            return x or y
        return self.intern((~x, ~y), self.length[x] + self.length[y])

    def slice(self, root, lo, hi):
        pieces = []
        pending = [(root, lo, hi)]
        while pending:
            node, i, j = pending.pop()
            if i == j:
                continue
            if i == 0 and j == self.length[node]:
                pieces.append(node)
                continue
            left, right = (~v for v in self.rules[node])
            cut = self.length[left]
            if j > cut:
                pending.append((right, max(0, i-cut), j-cut))
            if i < cut:
                pending.append((left, i, min(j, cut)))
        result = 0
        for piece in pieces:
            result = self.join(result, piece)
        return result

    def equal(self, x, y):
        return (x == y or (self.length[x] == self.length[y]
                           and compressed_equal(self.rules, x, y)))

    def difference(self, x, y):
        """Remove the longest common prefix, giving a canonical pair of tails."""
        if x == y:
            return 0, 0
        low = 0
        high = min(self.length[x], self.length[y]) + 1
        while high - low > 1:
            k = (low + high) // 2
            if self.equal(self.slice(x, 0, k), self.slice(y, 0, k)):
                low = k
            else:
                high = k
        return self.slice(x, low, self.length[x]), self.slice(y, low, self.length[y])


@dataclass(frozen=True)
class Path:
    first: tuple
    body: int
    last: tuple


class RigidPaths:
    """Bottom-up summaries; None represents an empty chronological path."""

    def __init__(self, pads):
        self.pads = pads
        self.bodies = Words()
        self.seams = []

    def atom(self, name, left=0, reverse_right=0):
        pads = left, reverse_right
        return Path(pads, self.bodies.letter(2*name), pads)

    def same_pads(self, xs, ys):
        return all(self.pads.equal(x, y) for x, y in zip(xs, ys))

    def pad(self, left, path, reverse_right):
        if path is None:
            return None

        def act(pair):
            return self.pads.join(left, pair[0]), self.pads.join(reverse_right, pair[1])

        return Path(act(path.first), path.body, act(path.last))

    def join(self, a, b):
        if a is None or b is None:
            return b if a is None else a
        key = tuple(v for x, y in zip(a.last, b.first) for v in self.pads.difference(x, y))
        for i, seen in enumerate(self.seams):
            if self.same_pads(key, seen):
                break
        else:
            i = len(self.seams)
            self.seams.append(key)
        middle = self.bodies.letter(2*i + 1)
        body = self.bodies.join(self.bodies.join(a.body, middle), b.body)
        return Path(a.first, body, b.last)

    def equal(self, a, b):
        if a is None or b is None:
            return a is b
        return self.same_pads(a.first, b.first) and self.bodies.equal(a.body, b.body)
