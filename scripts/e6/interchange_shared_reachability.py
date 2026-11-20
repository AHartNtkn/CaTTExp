"""Compressed doubled-loop reachability. A bad prefix certifies a missing 5-cell."""

from itertools import combinations_with_replacement, product

from grid_loop_words import check_grid, reach


class LoopWords:
    """Shared concatenations of the early E and late L loops, with prefix counts."""

    def __init__(self):
        self.children = [None, None, None]  # identity, E, L
        self.length = [0, 1, 1]
        self.early = [0, 1, 0]
        self.joins = {}

    def cat(self, a, b):
        if not a or not b:
            return a or b
        if (a, b) not in self.joins:
            self.joins[a, b] = len(self.children)
            self.children.append((a, b))
            self.length.append(self.length[a] + self.length[b])
            self.early.append(self.early[a] + self.early[b])
        return self.joins[a, b]

    def power(self, word, exponent):
        result = 0
        while exponent:
            if exponent % 2:
                result = self.cat(result, word)
            exponent //= 2
            if exponent:
                word = self.cat(word, word)
        return result

    def prefix_early(self, word, k):
        if not 0 <= k <= self.length[word]:
            raise ValueError("prefix length outside word")
        total = 0
        while 0 < k < self.length[word]:
            a, b = self.children[word]
            if k <= self.length[a]:
                word = a
            else:
                total += self.early[a]
                k -= self.length[a]
                word = b
        return total + (self.early[word] if k else 0)

    def permits(self, source, target, k):
        return (self.length[source] == self.length[target]
                and self.early[source] == self.early[target]
                and self.prefix_early(source, k) <= self.prefix_early(target, k))

    def subset_sum_pair(self, weights, t):
        """Construct paths admitting a filler exactly when no subset sums to t."""
        if any(w < 0 for w in weights) or t < 0:
            raise ValueError("expected nonnegative integers")
        m = 1 + max(t, sum(weights))
        front, back = self.cat(1, 2), self.cat(2, 1)
        # Encode the subset indicator by 1 -> EL and 0 -> LE.
        source = front
        count = 1
        for w in weights:
            gap = count * m + w - self.length[source] // 2
            source = self.cat(self.cat(source, self.power(back, gap)), source)
            count *= 2
        source = self.cat(source, self.power(back, count * m - self.length[source] // 2))
        # Encode the target indicator by 1 -> LE and 0 -> EL.
        period = self.cat(self.cat(self.power(front, t), back), self.power(front, m-1-t))
        return source, self.power(period, count)


def check_prefix_order():
    grammar = LoopWords()
    for size in range(7):
        words = list(product("EL", repeat=size))
        ids = {}
        for word in words:
            node = 0
            for x in word:
                node = grammar.cat(node, 1 if x == "E" else 2)
            ids[word] = node
        for word in words:
            expected = reach(word, {(("L", "E"), ("E", "L"))})
            observed = {v for v in words if all(grammar.permits(ids[word], ids[v], k)
                                                for k in range(size + 1))}
            assert observed == expected


def check_subsets():
    cases = 0
    for size in range(5):
        for weights in combinations_with_replacement(range(4), size):
            sums = {0}
            for w in weights:
                sums |= {s + w for s in sums}
            for t in range(sum(weights) + 2):
                grammar = LoopWords()
                a, b = grammar.subset_sum_pair(weights, t)
                assert all(grammar.permits(a, b, k) for k in range(grammar.length[a]+1)) == (t not in sums)
                cases += 1
    print(f"Prefix certificate criterion agrees with directed search through length six; "
          f"all {cases} small subset instances agree with exhaustive subset sums.")
    weights = [1 << i for i in range(90)]
    t = (1 << 88) + 7
    grammar = LoopWords()
    a, b = grammar.subset_sum_pair(weights, t)
    # With binary powers the subset's identifier and its sum coincide.
    k = 2 * (t * (sum(weights) + 1) + t) + 1
    assert not grammar.permits(a, b, k)
    assert grammar.permits(a, b, k-1) and grammar.permits(a, b, k+1)
    print(f"{len(grammar.children)} nodes; {grammar.length[a].bit_length()}-bit expanded length; "
          "checked an interior bad prefix and its two neighbours.")


if __name__ == '__main__':
    check_grid()
    check_prefix_order()
    check_subsets()
