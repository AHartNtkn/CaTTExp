"""Compressed free-group codes for typed rigid paths with common source.

Each proper intrinsic head has its own generator, disjoint across degrees.
At any lower cut a fixed left action conjugates the code and a fixed right
action preserves it. The caller supplies the globular typing.
"""

from dataclasses import dataclass

from interchange_shared_whiskers import Words


@dataclass(frozen=True)
class Reduced:
    forward: int
    inverse: int


class RigidGroup:
    unit = Reduced(0, 0)

    def __init__(self):
        self.words = Words()
        self.names = {}

    def head(self, degree, name):
        index = self.names.setdefault((degree, name), len(self.names))
        return Reduced(self.words.letter(2 * index), self.words.letter(2 * index + 1))

    def _prefix(self, root, length):
        """A one-boundary descent preserving the original tree's height."""
        saved = []
        while 0 < length < self.words.length[root]:
            left, right = (~ref for ref in self.words.rules[root])
            if length <= self.words.length[left]:
                root = left
            else:
                saved.append(left)
                length -= self.words.length[left]
                root = right
        result = root if length else 0
        for left in reversed(saved):
            result = self.words.join(left, result)
        return result

    def _suffix(self, root, length):
        saved = []
        while 0 < length < self.words.length[root]:
            left, right = (~ref for ref in self.words.rules[root])
            if length <= self.words.length[right]:
                root = right
            else:
                saved.append(right)
                length -= self.words.length[right]
                root = left
        result = root if length else 0
        for right in reversed(saved):
            result = self.words.join(result, right)
        return result

    def join(self, left, right):
        a, b = left.forward, right.forward
        if not a or not b:
            return right if not a else left
        m, n = self.words.length[a], self.words.length[b]
        low, high = 0, min(m, n) + 1
        while high - low > 1:
            k = (low + high) // 2
            if self.words.equal(self._prefix(left.inverse, k), self._prefix(b, k)):
                low = k
            else:
                high = k
        return Reduced(
            self.words.join(self._prefix(a, m-low), self._suffix(b, n-low)),
            self.words.join(self._prefix(right.inverse, n-low), self._suffix(left.inverse, m-low)),
        )

    def left_action(self, pad, path):
        return self.join(self.join(pad, path), Reduced(pad.inverse, pad.forward))

    def equal_at_source(self, left, right):
        return self.words.equal(left.forward, right.forward)


@dataclass(frozen=True)
class StructuralCell:
    degree: int
    rows: tuple  # source/target code pairs; rank zero uses object names

    def row(self, degree):
        if degree > self.degree or degree < 0:
            raise ValueError("row outside the declared dimension")
        if degree >= len(self.rows):
            return RigidGroup.unit, RigidGroup.unit
        return self.rows[degree]

    def elevate(self, degree):
        if degree < self.degree:
            raise ValueError("identity elevation cannot lower dimension")
        return StructuralCell(degree, self.rows)

    def face(self, degree, side):
        if degree >= self.degree or side not in (0, 1):
            raise ValueError("a face needs a smaller degree and a side")
        value = self.row(degree)[side]
        if degree >= len(self.rows):
            return StructuralCell(degree, self.rows)
        return StructuralCell(degree, self.rows[:degree] + ((value, value),))


class StructuralPaths:
    """Row preparation for well-typed structural DAGs over explicit named globes."""

    def __init__(self):
        self.group = RigidGroup()

    @staticmethod
    def object(name):
        return StructuralCell(0, ((name, name),))

    def globe(self, name, source, target):
        degree = source.degree + 1
        top = self.group.head(degree, name)
        lower = tuple(source.row(j) for j in range(degree-1))
        faces = source.row(degree-1)[0], target.row(degree-1)[1]
        return StructuralCell(degree, lower + (faces, (top, top)))

    def chrono(self, left, right):
        n = left.degree
        if not n or n != right.degree:
            raise ValueError("chronological operands need the same positive degree")
        if n >= max(len(left.rows), len(right.rows)):
            return left  # Both are identities with a common matching face.
        result = [left.row(j) for j in range(n-1)]
        result.append((left.row(n-1)[0], right.row(n-1)[1]))
        top = self.group.join(left.row(n)[0], right.row(n)[0])
        return StructuralCell(n, tuple(result) + ((top, top),))

    def act(self, pad, path, on_left):
        m, n = pad.degree, path.degree
        if not 0 < m < n:
            raise ValueError("a fixed pad needs positive degree below the path")
        if m >= len(pad.rows):
            return path  # The top pad is an identity.
        a = pad.row(m)[0]
        height = max(len(path.rows)-1, m)
        result = [path.row(j) for j in range(m-1)]
        first, last = (pad, path) if on_left else (path, pad)
        result.append((first.row(m-1)[0], last.row(m-1)[1]))
        result.append(tuple(self.group.join(a, x) if on_left else self.group.join(x, a)
                            for x in path.row(m)))
        for j in range(m+1, height+1):
            row = path.row(j)
            result.append(tuple(self.group.left_action(a, x) for x in row) if on_left else row)
        return StructuralCell(n, tuple(result))

    def product(self, cut, left, right):
        declared = left.degree
        if declared != right.degree or not 0 <= cut < declared:
            raise ValueError("invalid Godement cut or operand degree")
        height = max(len(left.rows), len(right.rows))-1
        if cut >= height:
            return left
        if height < declared:
            left, right = left.face(height, 0), right.face(height, 0)
        for i in range(cut, height-1):
            left, right = (self.act(left.face(i+1, 0), right, True),
                           self.act(right.face(i+1, 1), left, False))
        return self.chrono(left, right).elevate(declared)

    def equal(self, left, right):
        if left.degree != right.degree or left.rows[0][0] != right.rows[0][0]:
            return False
        return all(self.group.equal_at_source(left.row(j)[0], right.row(j)[0])
                   for j in range(1, max(len(left.rows), len(right.rows))))
