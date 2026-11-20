"""Binary-index rank operations and equality of typed principal/chronological DAGs."""

from dataclasses import dataclass

from interchange_shared_whiskers import Words


def principal_rank(cut, left, right):
    vertex = cut + 1
    return max(left, right) + max(0, min(left, right) - vertex)


def bridge_rank(cut, old_moving, layer, moving_rank, fixed_rank):
    """The signed raising bridge on the old layer, including the pure bottom insertion."""
    row = cut + 1 + layer
    proper_variation = moving_rank == cut + 2 + old_moving
    return min(row + int(proper_variation), principal_rank(cut, moving_rank, fixed_rank))


def column_ranks(left, right, first_cut, steps):
    """Jump over successive Godement columns. Inputs and outputs are effective ranks."""
    if not steps:
        return left, right
    high = max(left, right)
    low = max(min(left, right), min(high, first_cut + steps))
    high_on_left = (left >= right) != bool(steps % 2)
    return (high, low) if high_on_left else (low, high)


@dataclass(frozen=True)
class Value:
    degree: int
    rank: int
    word: int


class PrincipalWords:
    """Typed inputs at cut three; supplied seed names classify single rigid 5-cells."""
    def __init__(self):
        self.words = Words()
        self.terminals = {}
        self.classes = {}
        self.names = {}

    def atom(self, key):
        name = self.terminals.setdefault(key, len(self.terminals))
        return self.words.letter(name)

    def seed(self, name):
        return Value(5, 5, self.atom(('seed', name)))

    def elevate(self, x, degree):
        if degree < x.degree:
            raise ValueError('identity elevation cannot lower the degree')
        return Value(degree, x.rank, x.word)

    def join(self, x, y):
        if x.degree != y.degree:
            raise ValueError('chronological join requires a common degree')
        if x.rank < x.degree:
            return y
        if y.rank < y.degree:
            return x
        return Value(x.degree, x.degree, self.words.join(x.word, y.word))

    def name(self, x):
        key = x.rank, x.word
        if key not in self.names:
            reps = self.classes.setdefault(x.rank, [])
            for i, rep in enumerate(reps):
                if self.words.equal(x.word, rep):
                    break
            else:
                i = len(reps)
                reps.append(x.word)
            self.names[key] = x.rank, i
        return self.names[key]

    def tensor(self, x, y):
        degree = principal_rank(3, x.degree, y.degree)
        rank = principal_rank(3, x.rank, y.rank)
        head = self.atom(('tensor', self.name(x), self.name(y)))
        return Value(degree, rank, head)

    def equal(self, x, y):
        return x.degree == y.degree and self.name(x) == self.name(y)
