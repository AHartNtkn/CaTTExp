"""Check degree-five temporal exchanges on the three slots supporting a triangle.

The Gray 4-chain permits the braid and, in a flagged run, a single input
update. The other positive 4-edges are spatial exchanges or the binary join
with this same braid atom. Histories can start and end at any intermediate
state of the word graph, and every chronological 4-path context is tested.
"""
from collections import Counter
from dataclasses import dataclass
from functools import cache
from itertools import combinations, permutations


NEGATIVE = ('bc', 'ac', 'ab')
POSITIVE = NEGATIVE[::-1]


def slots(event):
    return event.rstrip('+')


def order_after(prefix):
    order = list('cba')
    for event in prefix:
        if len(slots(event)) == 2:
            x, y = event
            i = order.index(y)
            assert order[i+1] == x
            order[i:i+2] = [x, y]
    return order


@dataclass(frozen=True)
class Edge:
    family: str
    lo: int
    hi: int
    output: tuple
    left: str = ''

    def apply(self, word):
        return word[:self.lo] + self.output + word[self.hi:]


@cache
def moves(word, flag):
    result = []
    for lo, mid, hi in combinations(range(len(word)+1), 3):
        order = order_after(word[:lo])
        right, left = word[lo:mid], word[mid:hi]
        left_slots = set(''.join(map(slots, left)))
        right_slots = set(''.join(map(slots, right)))
        if max(map(order.index, left_slots)) < min(map(order.index, right_slots)):
            result.append(Edge('inner', lo, hi, left+right, ''.join(sorted(left_slots))))
    for i in range(len(word)):
        if word[i:i+3] == NEGATIVE:
            result.append(Edge('triangle', i, i+3, POSITIVE))
        if slots(word[i]) == 'c' and word[i+1:i+4] == NEGATIVE:
            result.append(Edge('join', i, i+4, (POSITIVE[0], word[i], *POSITIVE[1:])))
        if word[i] == flag:
            result.append(Edge('update', i, i+1, (flag+'+',)))
    return tuple(result)


def states(unaries, flag):
    for word in permutations((*NEGATIVE, *unaries)):
        crossings = tuple(e for e in word if len(e) == 2)
        if crossings in (NEGATIVE, POSITIVE):
            yield word
            if flag:
                yield tuple(e+'+' if e == flag else e for e in word)


def check(unaries, flag=''):
    @cache
    def rules(word):
        found = set()

        def add(name, lhs, rhs, symmetric=False):
            def evaluate(path):
                v = word
                for edge in path:
                    assert edge in moves(v, flag)
                    v = edge.apply(v)
                return v
            assert evaluate(lhs) == evaluate(rhs)
            found.add((name, lhs, rhs))
            if symmetric:
                found.add((name, rhs, lhs))

        for first in moves(word, flag):
            mid = first.apply(word)
            for second in moves(mid, flag):
                end = second.apply(mid)
                if second.hi <= first.lo:
                    add('exchange', (first, second), (second, first))
                if first.family == second.family == 'inner' or (
                        first.family == 'join' and second.family == 'inner'):
                    kind = 'inner' if first.family == 'inner' else 'triangle'
                    for edge in moves(word, flag):
                        if edge.family == kind and edge.apply(word) == end:
                            add('split' if kind == 'inner' else 'factor',
                                (edge,), (first, second), True)
                if first.family not in ('inner', 'join') or second.family != 'update':
                    continue
                at = word.index(flag)
                if first.lo <= at < first.hi:
                    update = next(e for e in moves(word, flag) if e.family == 'update')
                    new = update.apply(word)
                    for other in moves(new, flag):
                        if (other.family, other.lo, other.hi) != (first.family, first.lo, first.hi):
                            continue
                        if other.apply(new) != end:
                            continue
                        later, earlier = (first, second), (update, other)
                        if first.family == 'join':
                            assert flag == 'c'
                            add('right join variation', earlier, later)
                        elif flag in first.left:
                            add('left naturality', later, earlier)
                        else:
                            add('right naturality', earlier, later)
        return found

    @cache
    def paths(word):
        return ((),) + tuple((edge, *tail) for edge in moves(word, flag)
                             for tail in paths(edge.apply(word)))

    counts = Counter()
    for word in states(unaries, flag):
        graph = {}
        exchanges = set()
        for path in paths(word):
            v = word
            graph[path] = set()
            for i, edge in enumerate(path):
                for name, lhs, rhs in rules(v):
                    if path[i:i+len(lhs)] != lhs:
                        continue
                    dst = path[:i] + rhs + path[i+len(lhs):]
                    graph[path].add(dst)
                    counts[name] += 1
                    if name == 'exchange':
                        exchanges.add((path, dst))
                v = edge.apply(v)
        for source, target in exchanges:
            seen, stack = {target}, [target]
            while stack:
                new = graph[stack.pop()] - seen
                stack.extend(new)
                seen.update(new)
            assert source not in seen, (word, source, target)
        counts['paths'] += len(graph)
    return counts


if __name__ == '__main__':
    for marking in ('flag', 'pair'):
        total = Counter()
        instances = [((s,), s) for s in 'abc'] if marking == 'flag' else [
            (pair, '') for pair in combinations('abc', 2)]
        for unaries, flag in instances:
            total.update(check(unaries, flag))
        print(marking, dict(sorted(total.items())))
