"""Check planar occurrence transport across mixed births, deaths and repeated gates."""

from collections import Counter
from itertools import product

RULES = {'d': ('a', ''), 'b': ('', 'b'), 's': ('a', 'ab'), 'm': ('ab', 'b'),
         'n': ('bb', 'b')}


def spellings(initial, rules, length):
    def extend(word, prefix):
        if len(prefix) == length:
            yield prefix
            return
        for gate, (src, tgt) in rules.items():
            for offset in range(len(word) - len(src) + 1):
                if word.startswith(src, offset):
                    after = word[:offset] + tgt + word[offset+len(src):]
                    yield from extend(after, prefix + ((gate, offset),))
    return set(extend(initial, ()))


def switches(history, rules):
    for p, ((g, i), (h, j)) in enumerate(zip(history, history[1:])):
        a, b = map(len, rules[g])
        c, d = map(len, rules[h])
        if j + c <= i:
            yield p, history[:p] + ((h, j), (g, i+d-c)) + history[p+2:]
        if i + b <= j:
            yield p, history[:p] + ((h, j-b+a), (g, i)) + history[p+2:]


def component_transport(words, rules):
    remaining = words.copy()
    while remaining:
        root = remaining.pop()
        transport = {root: tuple(range(len(root)))}
        todo = [root]
        rigid = True
        while todo:
            w = todo.pop()
            order = transport[w]
            for pos, nxt in switches(w, rules):
                next_order = order[:pos] + (order[pos+1], order[pos]) + order[pos+2:]
                if nxt in transport:
                    rigid &= transport[nxt] == next_order
                else:
                    remaining.remove(nxt)
                    transport[nxt] = next_order
                    todo.append(nxt)
        yield root, transport, rigid


def check_colours(initial, n):
    words = spellings(initial, RULES, n)
    roots = {}
    for root, transport, rigid in component_transport(words, RULES):
        assert rigid
        roots.update(dict.fromkeys(transport, root))
    # Independently compute actual exchange classes upstairs and fold them.
    coloured = {(g, c): rule for g, rule in RULES.items() for c in (0, 1)}
    counts = Counter()
    for word, _, rigid in component_transport(spellings(initial, coloured, n), coloured):
        assert rigid
        projected = tuple((g, pos) for (g, _), pos in word)
        counts[roots[projected]] += 1
    assert set(counts) == set(roots.values())
    assert set(counts.values()) == {2 ** n}
    return len(words), len(counts), sum(counts.values())


def scalar_control():
    rules = {'z': ('', '')}
    [(root, _, rigid)] = list(component_transport(spellings('', rules, 2), rules))
    assert len(root) == 2 and not rigid
    labelled = {('z', c): ('', '') for c in range(2)}
    classes = list(component_transport(spellings('', labelled, 2), labelled))
    assert len(classes) == 3
    # A dead input and a born output at the same empty cut allow BOTH outer
    # serializations. They are genuinely two different offset spellings.
    mixed = list(switches((('d', 0), ('b', 0)), RULES))
    assert len({nxt for _, nxt in mixed}) == 2


if __name__ == '__main__':
    scalar_control()
    for initial, length in product(('a', 'aa', 'ab'), (2, 3, 4)):
        print(initial, length, 'spellings, planar classes, two-colour classes:', *check_colours(initial, length))
