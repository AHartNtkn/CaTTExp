"""Compare two-row 4-paths with shared chronological products and lazy 3-pads.

Named columns decrease on each row. A pad is spelled by 'u' (first row) or 'd'
(second row). Right pads are read backwards with the two symbols interchanged.
The checker supplies parallel typed paths in the same spatial interval.
"""

from dataclasses import dataclass
from functools import cache

from interchange_shared_whiskers import Words


@dataclass(frozen=True)
class Reader:
    height: int
    mountain: tuple | None
    emitted: int = 0
    symbol: str = ""


def start(height):
    return Reader(height, None if height else (0, 0))


def scan(state, word, emit):
    """Emit settled letters. Keep only an unfinished single mountain at the end."""
    height, mountain = state.height, state.mountain
    for c in word:
        height += 1 if c == "u" else -1
        if height < 0:
            raise ValueError("invalid two-row history")
        if mountain is None:
            emit(c)
            if height == 0:
                mountain = (0, 0)
            continue
        up, down = mountain
        if c == "u" and down:
            emit("u"*up + "d"*down + c)
            mountain = None
        elif c == "u":
            mountain = up+1, 0
        elif height == 0:
            emit("ud"*up)
            mountain = (0, 0)
        else:
            mountain = up, down+1
    return height, mountain


def tail(mountain):
    if mountain is None:
        return ""
    up, down = mountain
    return "u"*up + "d"*down


def residual(state, word):
    parts = []
    _, mountain = scan(state, word, parts.append)
    return "".join(parts) + tail(mountain)


def feed(state, word, coordinate):
    pos, symbol = state.emitted, state.symbol

    def emit(chunk):
        nonlocal pos, symbol
        if pos <= coordinate < pos + len(chunk):
            symbol = chunk[coordinate-pos]
        pos += len(chunk)

    h, m = scan(state, word, emit)
    return Reader(h, m, pos, symbol)


def read_coordinate(state, word, k):
    final = feed(state, word, k)
    if final.symbol:
        return final.symbol
    return tail(final.mountain)[k-final.emitted:k-final.emitted+1] if k >= final.emitted else ""


@dataclass(frozen=True)
class Tile:
    pre: str
    f: tuple
    g: tuple
    revpost: str

    def pad(self, p, q):
        return Tile(p+self.pre, self.f, self.g, q+self.revpost)

    @property
    def area(self):
        return len(self.f) * len(self.g)


def units(t):
    """Use moving subdivision, then split the opposite row in processing order."""
    for i, f in enumerate(t.f):
        for j in reversed(range(len(t.g))):
            yield Tile(t.pre + "u"*i + "d"*j, (f,), (t.g[j],),
                       t.revpost + "d"*(len(t.f)-1-i) + "u"*(len(t.g)-1-j))


def merge(x, y, p, q):
    if (x.g == y.g and x.f[-1] == y.f[0]+1
            and residual(p, x.pre + "u"*len(x.f)) == residual(p, y.pre)
            and residual(q, y.revpost + "d"*len(y.f)) == residual(q, x.revpost)):
        return Tile(x.pre, x.f+y.f, x.g, y.revpost)
    if (x.f == y.f and y.g[-1] == x.g[0]+1
            and residual(p, y.pre + "d"*len(y.g)) == residual(p, x.pre)
            and residual(q, x.revpost + "u"*len(x.g)) == residual(q, y.revpost)):
        return Tile(y.pre, x.f, y.g+x.g, x.revpost)
    return None


def covering(window, index, p, q):
    stack = []
    for tile in window:
        stack.append(tile)
        while len(stack) >= 2:
            parent = merge(stack[-2], stack[-1], p, q)
            if parent is None:
                break
            stack[-2:] = [parent]
    for tile in stack:
        if index < tile.area:
            return tile, index
        index -= tile.area
    raise IndexError("coordinate outside tile window")


class Expressions:
    """An arena for paths, also used for the derived sequence of marked windows."""

    def __init__(self):
        self.rules = [("empty",)]
        self.sizes = [0]

    def add(self, rule, size):
        self.rules.append(rule)
        self.sizes.append(size)
        return len(self.rules)-1

    def cat(self, a, b):
        if not a or not b:
            return a or b
        return self.add(("cat", a, b), self.sizes[a]+self.sizes[b])

    def pad(self, p, a, q):
        if not a or not (p or q):
            return a
        return self.add(("pad", p, a, q), self.sizes[a])

    def tile(self, t):
        root = 0
        for unit in units(t):
            root = self.cat(root, self.add(("tile", unit), 1))
        return root

    def at(self, node, k):
        p = q = ""
        while True:
            rule = self.rules[node]
            if rule[0] == "tile":
                return rule[1].pad(p, q)
            if rule[0] == "pad":
                _, pre, node, post = rule
                p += pre
                q += post
            else:
                _, a, b = rule
                node = a if k < self.sizes[a] else b
                if k >= self.sizes[a]:
                    k -= self.sizes[a]


def windows(raw, roots, radius):
    out = Expressions()

    names = {}

    def marked(node, lo, hi):
        result = 0
        size = raw.sizes[node]
        for k in range(lo, hi):
            first = max(0, k-radius)
            tiles = tuple(raw.at(node, j) for j in range(first, min(size, k+radius+1)))
            key = ("window", tiles, k-first)
            if key not in names:
                names[key] = out.add(key, 1)
            result = out.cat(result, names[key])
        return result

    cores = []
    for node, rule in enumerate(raw.rules):
        size = raw.sizes[node]
        if size <= 2*radius:
            core = 0
        elif rule[0] == "pad":
            _, p, a, q = rule
            core = out.pad(p, cores[a], q)
        elif rule[0] == "cat":
            _, a, b = rule
            lo = radius + out.sizes[cores[a]]
            hi = size - radius - out.sizes[cores[b]]
            core = out.cat(out.cat(cores[a], marked(node, lo, hi)), cores[b])
        else:
            core = marked(node, radius, size-radius)
        assert out.sizes[core] == max(0, size-2*radius)
        cores.append(core)

    def finish(node):
        size = raw.sizes[node]
        lo, hi = min(radius, size), max(size-radius, min(radius, size))
        return out.cat(out.cat(marked(node, 0, lo), cores[node]), marked(node, hi, size))

    return out, [finish(node) for node in roots]


def equal(raw, a, b, width, source_height, target_height):
    """Exact decision on parallel expressions; the two heights refer to 2-faces."""
    if raw.sizes[a] != raw.sizes[b]:
        return False
    if not raw.sizes[a]:
        return True
    gramm, roots = windows(raw, (a, b), width*width-1)

    @cache
    def resolved(node, hp, mp, hq, mq):
        _, tiles, index = gramm.rules[node]
        return covering(tiles, index, Reader(hp, mp), Reader(hq, mq))

    def compare_projection(side, k):
        words = Words()
        names = {}
        memo = {}

        def visit(root):
            root_key = root, start(source_height), start(target_height)
            stack = [root_key]
            while stack:
                key = stack[-1]
                node, p, q = key
                rule = gramm.rules[node]
                if key in memo:
                    stack.pop()
                    continue
                if rule[0] == "window":
                    tile, offset = resolved(node, p.height, p.mountain, q.height, q.mountain)
                    if side == "core":
                        value = offset, tile.f, tile.g
                    elif side == "pre":
                        value = read_coordinate(p, tile.pre, k)
                    else:
                        value = read_coordinate(q, tile.revpost, k)
                    memo[key] = words.letter(names.setdefault(value, len(names)))
                elif rule[0] == "empty":
                    memo[key] = 0
                else:
                    if rule[0] == "cat":
                        children = [(rule[1], p, q), (rule[2], p, q)]
                    else:
                        _, pre, child, post = rule
                        children = [(child, feed(p, pre, k), feed(q, post, k))]
                    missing = next((x for x in children if x not in memo), None)
                    if missing is not None:
                        stack.append(missing)
                        continue
                    parts = [memo[x] for x in children]
                    memo[key] = parts[0] if len(parts) == 1 else words.join(*parts)
                stack.pop()
            return memo[root_key]

        return words.equal(visit(roots[0]), visit(roots[1]))

    return (compare_projection("core", -1)
            and all(compare_projection(side, k) for side in ("pre", "post")
                    for k in range(2*width)))
