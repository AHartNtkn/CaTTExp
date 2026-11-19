"""Execute the mixed two-slot moves and check their cut markers."""

from collections import Counter
from dataclasses import dataclass
from itertools import combinations, groupby, permutations, product


@dataclass(frozen=True)
class Move:
    family: str
    lo: int
    hi: int
    parts: tuple
    replacement: tuple

    def apply(self, word):
        return word[:self.lo] + self.replacement + word[self.hi:]

    def markers(self, pure):
        names = [set(x.rstrip('+') for x in part) for part in self.parts]
        if self.family == 'globe':
            return 'P' if names[0] & pure else ''
        if self.family == 'i':
            return 'P' * (len(names[0] & pure) * len(names[1] & pure))
        varying = names[-1] if self.family == 'h' else names[0]
        if varying & pure:
            return None  # A mixed Gray atom outside the chosen fiber.
        return 'M' * len(varying)


def runs(word):
    return [(kind, tuple(group)) for kind, group in groupby(word, key=lambda x: x[0])]


def moves(word):
    c = word.index('C')
    for i, x in enumerate(word):
        if x != 'C' and not x.endswith('+'):
            yield Move('globe', i, i + 1, ((x,),), (x + '+',))
    for i, j in combinations(range(len(word) + 1), 2):
        spans = runs(word[i:j])
        pattern = ''.join(x for x, _ in spans)
        parts = tuple(part for _, part in spans)
        if pattern in ('CA', 'BC'):
            operand = parts[pattern.index('A' if pattern == 'CA' else 'B')]
            yield Move('r' if pattern == 'CA' else 't', i, j, (operand,), parts[1] + parts[0])
        elif pattern == 'BCA':
            b, cross, a = parts
            yield Move('h', i, j, (b, a), a + b + cross)
        elif (pattern == 'AB' and j <= c) or (pattern == 'BA' and i > c):
            yield Move('i', i, j, parts, parts[1] + parts[0])


def inversions(word, early, late):
    return sum(word[:i].count(late) for i, color in enumerate(word) if color == early)


def check():
    counts = Counter()
    for order in permutations(('A1', 'A2', 'B1', 'B2', 'C')):
        if order.index('A1') > order.index('A2') or order.index('B1') > order.index('B2'):
            continue
        c = order.index('C')
        for flags in product(('', '+'), repeat=4):
            versions = dict(zip(sorted(set(order) - {'C'}), flags))
            word = tuple(e + versions.get(e, '') for e in order)
            edges = list(moves(word))
            for early_pure, candidates in ((True, order[:c]), (False, order[c + 1:])):
                early, late = ('P', 'M') if early_pure else ('M', 'P')
                for size in range(1, len(candidates) + 1):
                    for selected in combinations(candidates, size):
                        pure = frozenset(selected)
                        active = []
                        for edge in edges:
                            label = edge.markers(pure)
                            if label is None:
                                continue
                            after = edge.apply(word)
                            k = after.index('C')
                            side = after[:k] if early_pure else after[k + 1:]
                            assert pure <= {e.rstrip('+') for e in side}
                            if 'P' in label:
                                on_pure_side = edge.hi <= c if early_pure else edge.lo > c
                                assert on_pure_side
                            if 'M' in label:
                                assert edge.lo <= c < edge.hi
                            if edge.family == 'h':
                                # h followed by the positional inner square equals
                                # r after the stationary B prefix (K32).
                                b, a = edge.parts
                                direct = next(e for e in edges if e.family == 'r'
                                              and e.lo == edge.lo + len(b) and e.hi == edge.hi)
                                correction = next(e for e in moves(after) if e.family == 'i'
                                                  and e.lo == edge.lo and e.hi == edge.lo + len(a) + len(b))
                                assert correction.apply(after) == direct.apply(word)
                                assert label + correction.markers(pure) == direct.markers(pure)
                                counts['joins'] += 1
                            active.append((edge, label))
                        for (x, xs), (y, ys) in permutations(active, 2):
                            if x.hi > y.lo:
                                continue
                            assert x.apply(y.apply(word)) == y.apply(x.apply(word))
                            assert x in moves(y.apply(word)) and y in moves(x.apply(word))
                            change = inversions(ys + xs, early, late) - inversions(xs + ys, early, late)
                            assert change >= 0
                            if early in xs and late in ys:
                                assert change > 0
                                counts['strict'] += 1
                            counts['rectangles'] += 1
    assert counts['strict'] and counts['joins']
    print(f"Checked {counts['rectangles']} contextual rectangles, {counts['strict']} strict marked drops, "
          f"and {counts['joins']} binary join equations.")


if __name__ == '__main__':
    check()
