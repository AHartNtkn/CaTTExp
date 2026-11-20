"""Shared rigid 5-path equality with immediate pads given by two-row grid 4-words."""

from interchange_grid_windows import covering, residual, start
from interchange_shared_whiskers import RigidPaths, Words


class GridReader:
    """Subsequential code for a 4-pad, read forwards or from its terminal end."""

    def __init__(self, width, heights, tiles, raw, output, reverse=False):
        self.radius = max(1, width*width//4)-1
        self.contexts = tuple(map(start, heights))
        self.tiles = tiles
        self.raw = raw
        self.output = output
        self.reverse = reverse
        self.names = {}
        self.transforms = {}
        self.finals = {}

    def record(self, window, i):
        if self.reverse:
            window, i = window[::-1], len(window)-1-i
        tile, offset = covering(tuple(self.tiles[x] for x in window), i, *self.contexts)
        p, q = self.contexts
        code = offset, tile.f, tile.g, residual(p, tile.pre), residual(q, tile.revpost)
        return self.output.letter(self.names.setdefault(code, len(self.names)))

    def run(self, state, node):
        """Evaluate a compressed input and produce a compressed output."""
        stack = [(state, node)]
        while stack:
            key = stack[-1]
            if key in self.transforms:
                stack.pop()
                continue
            buf, i = key
            rule = self.raw.rules[i]
            if not rule:
                result = buf, 0
            elif len(rule) == 1:
                extended = buf + rule
                k = len(extended)-1-self.radius
                emitted = self.record(extended, k) if k >= 0 else 0
                result = extended[max(0, len(extended)-2*self.radius):], emitted
            else:
                a, b = (~x for x in rule)
                if self.reverse:
                    a, b = b, a
                first = buf, a
                if first not in self.transforms:
                    stack.append(first)
                    continue
                mid, emitted = self.transforms[first]
                second = mid, b
                if second not in self.transforms:
                    stack.append(second)
                    continue
                final, more = self.transforms[second]
                result = final, self.output.join(emitted, more)
            self.transforms[key] = result
            stack.pop()
        return self.transforms[state, node]

    def finish(self, state):
        if state not in self.finals:
            out = 0
            for k in range(max(0, len(state)-self.radius), len(state)):
                lo = max(0, k-self.radius)
                out = self.output.join(out, self.record(state[lo:], k-lo))
            self.finals[state] = out
        return self.finals[state]


def equal_five(rules, roots, width, heights, tiles, raw):
    """Compare parallel paths in the structurally prepared 5-grammar.

    Heads ('atom', name, p, q) have already classified intrinsic data and two
    4-pad SLPs. ('pad', left, child, right) wraps a path and ('cat', a, b)
    concatenates; ('empty',) is the empty path. Pads on both sides are supplied
    in ordinary chronological order. All raw terminals are singleton 4-tiles.
    """
    pads = Words()
    prefix = GridReader(width, heights, tiles, raw, pads)
    suffix = GridReader(width, heights, tiles, raw, pads, reverse=True)
    paths = RigidPaths(pads)
    memo = {}

    def visit(root):
        root_key = root, (), ()
        stack = [root_key]
        while stack:
            key = stack[-1]
            if key in memo:
                stack.pop()
                continue
            node, p, q = key
            rule = rules[node]
            if rule[0] == 'empty':
                result = None
            elif rule[0] == 'atom':
                _, name, left, right = rule
                lp, lword = prefix.run(p, left)
                rq, rword = suffix.run(q, right)
                result = paths.atom(name, pads.join(lword, prefix.finish(lp)),
                                    pads.join(rword, suffix.finish(rq)))
            elif rule[0] == 'cat':
                left, right = (rule[1], p, q), (rule[2], p, q)
                if left not in memo or right not in memo:
                    stack.append(left if left not in memo else right)
                    continue
                result = paths.join(memo[left], memo[right])
            else:
                _, left, child, right = rule
                lp, lword = prefix.run(p, left)
                rq, rword = suffix.run(q, right)
                sub = child, lp, rq
                if sub not in memo:
                    stack.append(sub)
                    continue
                result = paths.pad(lword, memo[sub], rword)
            memo[key] = result
            stack.pop()
        return memo[root_key]

    return paths.equal(visit(roots[0]), visit(roots[1]))
