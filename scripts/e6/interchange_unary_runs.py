"""Chronological SLPs of left-variable cylinders on one stationary slot.

Inputs are typed. A tag identifies the stationary head and all its fixed
lower whiskers below the immediate pads. Faces are classified lower values.
join and equal act on shared lower cells in their respective homs.
"""

from dataclasses import dataclass

from interchange_shared_whiskers import Words


@dataclass(frozen=True)
class Cylinder:
    tag: object
    source: object
    target: object
    prefix: object
    moving: object
    suffix: object
    left_insertion: object
    right_insertion: object


@dataclass(frozen=True)
class Runs:
    first: Cylinder
    middle: int
    last: Cylinder | None  # None for a single block


class UnaryRuns:
    def __init__(self, join, equal):
        self.join_lower = join
        self.equal_lower = equal
        self.words = Words()
        self.names = []

    def same(self, a, b):
        return ((a.tag, a.source, a.target) == (b.tag, b.source, b.target)
                and self.equal_lower(a.prefix, b.prefix)
                and self.equal_lower(a.moving, b.moving)
                and self.equal_lower(a.suffix, b.suffix))

    def token(self, block):
        for i, value in enumerate(self.names):
            if self.same(block, value):
                return self.words.letter(i)
        i = len(self.names)
        self.names.append(block)
        return self.words.letter(i)

    def merge(self, a, b):
        if a.tag != b.tag or a.target != b.source:
            return None
        join = self.join_lower
        if not self.equal_lower(join(a.prefix, a.left_insertion), b.prefix):
            return None
        if not self.equal_lower(a.suffix, join(b.right_insertion, b.suffix)):
            return None
        return Cylinder(a.tag, a.source, b.target, a.prefix, join(a.moving, b.moving),
                        b.suffix, join(a.left_insertion, b.left_insertion),
                        join(a.right_insertion, b.right_insertion))

    def product(self, left, right):
        if left is None or right is None:
            return left or right
        a, b = left.last or left.first, right.first
        merged = self.merge(a, b)
        seam = [merged] if merged is not None else [a, b]
        first = left.first if left.last is not None else seam.pop(0)
        last = right.last if right.last is not None else (seam.pop() if seam else None)
        middle = left.middle
        for block in seam:
            middle = self.words.join(middle, self.token(block))
        return Runs(first, self.words.join(middle, right.middle), last)

    def code(self, path):
        if path is None:
            return 0
        result = self.words.join(self.token(path.first), path.middle)
        return result if path.last is None else self.words.join(result, self.token(path.last))

    def equal(self, left, right):
        """The caller compares exterior boundaries, including those of empty paths."""
        return self.words.equal(self.code(left), self.code(right))


class PaddedRuns:
    """Verify one alleged discrepancy between paths with shared immediate pads.

    The arena uses a fixed stationary slot and left variation. For an empty
    path the caller checks its boundary. Each terminal has positive integer
    weight furnished by the moving lower grading.
    """

    def __init__(self, solver, identity):
        self.solver = solver
        self.identity = identity
        self.rules = [('empty',)]
        self.weights = [0]
        self.products = [None]

    def add(self, rule, weight, product):
        self.rules.append(rule)
        self.weights.append(weight)
        self.products.append(product)
        return len(self.rules)-1

    def atom(self, record, weight):
        if weight <= 0:
            raise ValueError('a proper occurrence must have positive weight')
        return self.add(('atom', record), weight,
                        (record.source, record.target, record.moving))

    def combine(self, a, b):
        if a is None or b is None or a[1] != b[0]:
            return None
        return a[0], b[1], self.solver.join_lower(a[2], b[2])

    def join(self, left, right):
        if not left or not right:
            return left or right
        return self.add(('join', left, right), self.weights[left] + self.weights[right],
                        self.combine(self.products[left], self.products[right]))

    def pad(self, pre, node, post):
        if not node:
            return 0
        return self.add(('pad', pre, node, post), self.weights[node], self.products[node])

    def at(self, node, pos):
        """The actual record, and the offset of pos inside that occurrence."""
        if not 0 <= pos < self.weights[node]:
            raise IndexError(pos)
        pre = post = self.identity
        join = self.solver.join_lower
        while True:
            rule = self.rules[node]
            if rule[0] == 'atom':
                a = rule[1]
                return Cylinder(a.tag, a.source, a.target, join(pre, a.prefix),
                                a.moving, join(a.suffix, post), a.left_insertion,
                                a.right_insertion), pos
            if rule[0] == 'pad':
                pre, post = join(pre, rule[1]), join(rule[3], post)
                node = rule[2]
            else:
                left, right = rule[1:]
                if pos < self.weights[left]:
                    node = left
                else:
                    pos -= self.weights[left]
                    node = right

    def boundary(self, root, coord):
        if coord in (0, self.weights[root]):
            return True
        b, offset = self.at(root, coord)
        if offset:
            return False
        a, _ = self.at(root, coord-1)
        return self.solver.merge(a, b) is None

    def moving_product(self, root, lo, hi):
        """Aggregate a nonempty raw-boundary interval, ignoring exterior pads."""
        pending = [(root, lo, hi)]
        pieces = []
        while pending:
            node, a, b = pending.pop()
            if (a, b) == (0, self.weights[node]):
                pieces.append(self.products[node])
                continue
            rule = self.rules[node]
            if rule[0] == 'pad':
                pending.append((rule[2], a, b))
                continue
            if rule[0] != 'join':
                raise ValueError('weight coordinate splits a raw occurrence')
            left, right = rule[1:]
            cut = self.weights[left]
            if b > cut:
                pending.append((right, max(0, a-cut), b-cut))
            if a < cut:
                pending.append((left, a, min(b, cut)))
        value = pieces[0]
        for other in pieces[1:]:
            value = self.combine(value, other)
        return value

    def product_differs(self, a, b):
        if a is None or b is None:
            return a != b
        return a[:2] != b[:2] or not self.solver.equal_lower(a[2], b[2])

    def distinguishes(self, x, y, lo=0, hi=None):
        if self.weights[x] != self.weights[y]:
            return True
        if not 0 <= lo <= self.weights[x]:
            return False
        bx, by = self.boundary(x, lo), self.boundary(y, lo)
        if bx != by:
            return True
        if hi is None or not bx or not lo < hi <= self.weights[x]:
            return False
        if not self.boundary(x, hi) or not self.boundary(y, hi):
            return False
        left_x, _ = self.at(x, lo)
        left_y, _ = self.at(y, lo)
        right_x, _ = self.at(x, hi-1)
        right_y, _ = self.at(y, hi-1)
        eq = self.solver.equal_lower
        return (left_x.tag != left_y.tag or right_x.tag != right_y.tag
                or not eq(left_x.prefix, left_y.prefix) or not eq(right_x.suffix, right_y.suffix)
                or self.product_differs(self.moving_product(x, lo, hi),
                                        self.moving_product(y, lo, hi)))
