"""Test the run-order invariant against all rewrites on a separated triangle and flag.

The flag's slot stays spatially outside the three braid slots. An inner move
can transport its advance across any nonempty consecutive part of the braid.
The complete graph includes those moves even when the tested schedules do not.
"""
from collections import Counter
from functools import cache
from itertools import permutations

from interchange_triangle_fiber import Edge, NEGATIVE, POSITIVE


def check(flag_on_left):
    histories = [tuple(word) for braid in (NEGATIVE, POSITIVE) for i in range(4)
                 for u in ('u', 'u+') for word in [(*braid[:i], u, *braid[i:])]]

    @cache
    def moves(word):
        i = next(i for i, item in enumerate(word) if item.startswith('u'))
        out = []
        if word[i] == 'u':
            out.append(Edge('flag', i, i+1, ('u+',)))
        for j in range(2):
            if word[j:j+3] == NEGATIVE:
                out.append(Edge('braid', j, j+3, POSITIVE))
        for j in (range(i) if flag_on_left else range(i+1, 4)):
            out.append(Edge('inner', min(i,j), max(i,j)+1,
                            (word[i], *word[j:i]) if j < i else (*word[i+1:j+1], word[i])))
        return tuple(out)

    @cache
    def paths(word):
        return ((),) + tuple((edge, *tail) for edge in moves(word) for tail in paths(edge.apply(word)))

    @cache
    def rules(word):
        result = set()
        def add(name, lhs, rhs, both=False):
            result.add((name, lhs, rhs))
            if both:
                result.add((name, rhs, lhs))
        def family(path):
            return tuple(e.family for e in path)
        grouped = {}
        for path in paths(word):
            if not 1 <= len(path) <= 3:
                continue
            end = word
            for edge in path:
                end = edge.apply(end)
            grouped.setdefault(end, []).append(path)
        for choices in grouped.values():
            for x, y in permutations(choices, 2):
                a,b = family(x),family(y)
                if a == ('inner',) and b == ('inner','inner'):
                    add('inner subdivision', x, y, True)
                if len(x) == 2 and x[1].hi <= x[0].lo and y == x[::-1]:
                    add('temporal', x, y)
                for key, on_left in [('flag',flag_on_left), ('braid',not flag_on_left)]:
                    if a != ('inner',key) or b != (key,'inner'):
                        continue
                    # A non-temporal square: the variation is actually
                    # contained in the history traversed by the product.
                    if x[0].lo <= y[0].lo and y[0].hi <= x[0].hi:
                        add('inner naturality', x if on_left else y, y if on_left else x)
                left,right = ('flag','braid') if flag_on_left else ('braid','flag')
                if a == (right,'inner',left) and b == (left,right,'inner'):
                    if x[1].hi - x[1].lo == y[2].hi - y[2].lo == 4:
                        add('shifted join', x, y)
        return result

    def labels(word, path):
        debt = 0
        indices = []
        for edge in path:
            if edge.family == 'inner':
                debt += edge.hi-edge.lo-1
            else:
                components = [item.startswith('u') for item in word]
                indices.append(sum(a != b for a,b in zip(
                    components[:edge.lo], components[1:edge.lo+1])))
            word = edge.apply(word)
        return debt, indices

    counts = Counter()
    for word in histories:
        paths_here = set(paths(word))
        counts['paths'] += len(paths_here)
        for path in paths_here:
            v = word
            j, runs = labels(word, path)
            for i, edge in enumerate(path):
                for name, lhs, rhs in rules(v):
                    if path[i:i+len(lhs)] != lhs:
                        continue
                    other = path[:i] + rhs + path[i+len(lhs):]
                    assert other in paths_here
                    k, after = labels(word, other)
                    assert j == k
                    counts[name] += 1
                    if j == 0:
                        if name == 'temporal':
                            assert runs[i] > runs[i+1]
                            assert after == runs[:i] + runs[i:i+2][::-1] + runs[i+2:]
                            counts['strict on clean paths'] += 1
                        else:
                            assert runs == after
                v = edge.apply(v)
    return counts


if __name__ == '__main__':
    counts = check(True) + check(False)
    for key in ('inner subdivision', 'temporal', 'inner naturality', 'shifted join',
                'strict on clean paths'):
        assert counts[key] > 0, key
    print(dict(sorted(counts.items())))
