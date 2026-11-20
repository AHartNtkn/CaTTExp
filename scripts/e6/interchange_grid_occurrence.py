"""Verify an indexed disagreement of parallel two-row degree-five constructor paths.

After the polynomial lower spatial preparation, a head has classified intrinsic
data. Immediate pads are degree-four Expressions. A 'context' adds left and
reversed right degree-three histories to the whole child, including its pads.
"""

from interchange_grid_windows import equal, residual, start


class IndexedPaths:
    def __init__(self, pads, width, heights):
        self.pads = pads
        self.width = width
        self.heights = heights
        self.rules = []
        self.lengths = []

    def add(self, rule):
        kind = rule[0]
        if kind == 'atom':
            length = 1
        elif kind == 'empty':
            length = 0
        elif kind == 'cat':
            length = self.lengths[rule[1]] + self.lengths[rule[2]]
        elif kind in ('pad', 'context'):
            length = self.lengths[rule[2]]
        else:
            raise ValueError(kind)
        self.rules.append(rule)
        self.lengths.append(length)
        return len(self.rules) - 1

    def at(self, node, index):
        if index < 0 or index >= self.lengths[node]:
            raise IndexError(index)
        left = right = 0
        prefix = suffix = ''
        while True:
            rule = self.rules[node]
            kind = rule[0]
            if kind == 'cat':
                _, a, b = rule
                if index < self.lengths[a]:
                    node = a
                else:
                    index -= self.lengths[a]
                    node = b
            elif kind == 'context':
                _, p, node, q = rule
                prefix += p
                suffix += q
            else:
                if kind == 'atom':
                    _, name, p, q = rule
                else:
                    _, p, node, q = rule
                left = self.pads.cat(left, self.pads.pad(prefix, p, suffix))
                right = self.pads.cat(self.pads.pad(prefix, q, suffix), right)
                if kind == 'atom':
                    h, k = self.heights
                    return ((name, residual(start(h), prefix), residual(start(k), suffix)),
                            left, right)

    def disagrees(self, a, b, index):
        """The shorter end is the canonical witness for a length mismatch."""
        size = min(self.lengths[a], self.lengths[b])
        if index == size:
            return self.lengths[a] != self.lengths[b]
        if index < 0 or index > size:
            return False
        x, l, r = self.at(a, index)
        y, other_l, other_r = self.at(b, index)
        if x != y:
            return True
        return any(i != j and not equal(self.pads, i, j, self.width, *self.heights)
                   for i, j in ((l, other_l), (r, other_r)))
