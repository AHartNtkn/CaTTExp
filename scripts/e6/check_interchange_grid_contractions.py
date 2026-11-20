"""Check binary block contraction against the grid presentations in rounds 6 and 9."""

from collections import defaultdict
from functools import cache

from grid_loop_words import classes, schedules, states
from interchange_shared_paths import compressed_equal
from t_endomorphisms import all_extensions, expansions


def merge_blocks(first, second):
    left, right = first
    other_left, other_right = second
    if right == other_right and left[-1] + 1 == other_left[0]:
        return left + other_left, right
    if left == other_left and other_right[-1] + 1 == right[0]:
        return left, other_right + right
    return None


def normal_path(events):
    stack = []
    for row, col in events:
        stack.append(((row,), (col,)))
        while len(stack) >= 2:
            merged = merge_blocks(stack[-2], stack[-1])
            if merged is None:
                break
            stack[-2:] = [merged]
    return tuple(stack)


def check_histories(rows, cols):
    histories = all_extensions(tuple(range(rows)), tuple(range(cols)))
    normals = {word: normal_path(word) for word in histories}
    replacements = 0
    for word, blocks in normals.items():
        # Every resulting block has a legal expansion spelling the original word.
        offset = 0
        for left, right in blocks:
            end = offset + len(left) * len(right)
            assert word[offset:end] in expansions(left, right)
            offset = end
        assert offset == len(word)
        # Conversely every contextual equation in the independent atomic
        # presentation preserves the normal form, in both directions.
        for lo in range(len(word)):
            for hi in range(lo + 2, len(word) + 1):
                factor = word[lo:hi]
                left = tuple(sorted({a for a, b in factor}))
                right = tuple(sorted({b for a, b in factor}))
                if len(left) * len(right) != len(factor):
                    continue
                variants = expansions(left, right)
                if factor in variants:
                    for variant in variants:
                        assert normals[word[:lo] + variant + word[hi:]] == blocks
                        replacements += 1
    print(f"{rows}x{cols}: {len(histories)} histories, "
          f"{len(set(normals.values()))} classes, {replacements} contextual equations")


def four_cells(n):
    """Enumerate the two-row extreme interval via independent 3-history classes."""
    start, end = (n, n), (0, 0)

    @cache
    def letter(pre, left, right, post):
        corner = states(start, pre)[-1]
        after = states(corner, right + left)[-1]
        return classes(start, corner)[pre], left, right, classes(after, end)[post]

    parents = {}
    letters = set()

    def split(pair, parent):
        assert parents.setdefault(pair, parent) == parent

    for history in schedules(start, end):
        for pos, (x, y) in enumerate(states(start, history)):
            for width in range(1, x + 1):
                for height in range(1, y - x + 1):
                    left = tuple((0, x-i) for i in range(width))
                    right = tuple((1, y-i) for i in range(height))
                    if history[pos:pos+width+height] != right + left:
                        continue
                    pre, post = history[:pos], history[pos+width+height:]
                    wide = letter(pre, left, right, post)
                    letters.add(wide)
                    for i in range(1, width):
                        split((letter(pre, left[:i], right, left[i:] + post),
                               letter(pre + left[:i], left[i:], right, post)), wide)
                    for j in range(1, height):
                        split((letter(pre + right[:j], left, right[j:], post),
                               letter(pre, left, right[:j], right[j:] + post)), wide)
    return letters, parents


def check_peaks(n, letters, parents):
    following = defaultdict(list)
    for first, second in parents:
        following[first].append(second)
    peaks = 0
    for (first, second), merged in parents.items():
        for third in following[second]:
            assert parents[merged, third] == parents[first, parents[second, third]]
            peaks += 1
    print(f"2x{n}: {len(letters)} four-letters, {len(parents)} contractions, {peaks} peaks")


class Grammar:
    """Binary SLP. Taking a prefix or suffix preserves the height bound."""

    def __init__(self, terminals, parents):
        self.rules = [()]
        self.lengths = [0]
        self.parents = parents
        self.names = {term: i for i, term in enumerate(terminals)}
        self.terminals = list(terminals)
        self.atoms = [self.add((i,), 1) for i in range(len(terminals))]

    def add(self, rule, length):
        self.rules.append(rule)
        self.lengths.append(length)
        return len(self.rules) - 1

    def join(self, left, right):
        if left and right:
            return self.add((~left, ~right), self.lengths[left] + self.lengths[right])
        return left or right

    def part(self, root, lo, hi):
        if lo == hi:
            return 0
        if (lo, hi) == (0, self.lengths[root]):
            return root
        left, right = (~x for x in self.rules[root])
        cut = self.lengths[left]
        a = self.part(left, lo, min(cut, hi)) if lo < cut else 0
        b = self.part(right, max(0, lo-cut), hi-cut) if hi > cut else 0
        return self.join(a, b)

    def at(self, root, index):
        while self.lengths[root] > 1:
            left, right = (~x for x in self.rules[root])
            if index < self.lengths[left]:
                root = left
            else:
                index -= self.lengths[left]
                root = right
        return self.terminals[self.rules[root][0]]

    def product(self, left, right):
        m, n = self.lengths[left], self.lengths[right]
        if not m or not n:
            return self.join(left, right)
        center = self.parents.get((self.at(left, m-1), self.at(right, 0)))
        if center is None:
            return self.join(left, right)
        i, j = m-1, 1
        while True:
            next_left = self.parents.get((self.at(left, i-1), center)) if i else None
            next_right = self.parents.get((center, self.at(right, j))) if j < n else None
            if next_left is not None:
                i, center = i-1, next_left
            elif next_right is not None:
                j, center = j+1, next_right
            else:
                break
        return self.join(self.part(left, 0, i),
                         self.join(self.atoms[self.names[center]], self.part(right, j, n)))


def check_shared(n, letters, parents):
    grammar = Grammar(sorted(letters), parents)

    def atom(letter):
        return grammar.atoms[grammar.names[letter]]

    top = classes((n, n), (0, 0))

    def is_loop(letter):
        pre, left, right, post = letter
        return top[pre + right + left + post] == top[pre + left + right + post]

    # Select a genuine loop which can be subdivided on both axes.
    sides = defaultdict(list)
    for pair, wide in parents.items():
        sides[wide].append(pair)
    wide = next(w for w in sorted(sides) if len(w[1]) == len(w[2]) == 2 and is_loop(w))
    splits = sorted(sides[wide])
    first = grammar.product(*map(atom, splits[0]))
    second = grammar.product(*map(atom, splits[-1]))
    assert first == second == atom(wide)
    # Split the last copy across a grammar junction after an increasingly long
    # power. Equality and the single-terminal disturbance both have parallel faces.
    lpart, rpart = map(atom, splits[0])
    power = atom(wide)
    for _ in range(100):
        power = grammar.product(power, power)
    across = grammar.product(grammar.product(power, lpart), rpart)
    expected = grammar.product(power, atom(wide))
    assert grammar.lengths[power] == 1 << 100
    assert compressed_equal(grammar.rules, across, expected)
    other = next(w for w in sorted(letters) if w != wide and is_loop(w)
                 and top[w[0] + w[2] + w[1] + w[3]]
                 == top[wide[0] + wide[2] + wide[1] + wide[3]])
    assert not compressed_equal(grammar.rules, across, grammar.product(power, atom(other)))
    print("Shared two-axis loop, crossing a grammar junction after 2^100 copies: "
          "equal split and distinct parallel loop both checked")


if __name__ == "__main__":
    for dims in ((3, 2), (3, 3), (3, 4)):
        check_histories(*dims)
    for n in range(4, 8):
        letters, parents = four_cells(n)
        check_peaks(n, letters, parents)
        if n == 4:
            check_shared(n, letters, parents)
