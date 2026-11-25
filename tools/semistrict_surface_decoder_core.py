"""Check relation-compatible finite readers and positioned lifts of multiset cycles."""
from collections import Counter, deque
from itertools import combinations, product

from semistrict_surface_finite_decoder import Decoder


def forced_letters(relations):
    forced = set()
    while True:
        added = {letter for lhs, rhs in relations for source, target in ((lhs, rhs), (rhs, lhs))
                 if all(x in forced for x in source) for letter in target}
        if added <= forced:
            return forced
        forced.update(added)


def follow(actions, word, start):
    for letter in word:
        start = actions[letter][start]
    return start


def closure_test():
    # Solve the defining equations in the full two-state transformation monoid.
    pairs = [('','ab'), ('a','bc'), ('c','cbd'), ('b',''), ('ca','dd'), ('d','a')]
    states = range(2)
    endomaps = list(product(states, repeat=2))
    candidates = []
    for maps in product(endomaps, repeat=4):
        actions = dict(zip('abcd', maps))
        valid = {i for i, (u, v) in enumerate(pairs)
                 if all(follow(actions, u, s) == follow(actions, v, s) for s in states)}
        permutations = {x for x, action in actions.items() if len(set(action)) == 2}
        candidates.append((valid, permutations))
    for mask in product((False, True), repeat=len(pairs)):
        selected = {i for i, flag in enumerate(mask) if flag}
        forced = set('abcd')
        for valid, permutations in candidates:
            if selected <= valid:
                forced &= permutations
        assert forced == forced_letters([pairs[i] for i in selected])
    return 2 ** len(pairs)


class Reader:
    def __init__(self, letters, relations):
        forced = forced_letters(relations)
        rest = [letter for letter in letters if letter not in forced]
        self.machine = Decoder(len(rest)) if len(rest) >= 2 else None
        self.states = self.machine.states() if self.machine else [0]
        self.codes = {letter: letter for letter in letters}
        if self.machine:
            self.codes.update(zip(rest, self.machine.codes, strict=True))
        self.rest = rest
        alphabet = set(''.join(self.codes.values()))
        assert len(alphabet) == len(forced) + min(2, len(rest))

    def read(self, word, state):
        emitted = []
        for letter in word:
            if letter in ('P', 'Q'):
                state, event = self.machine.step(state, letter)
                emitted.append(None if event is None else self.rest[event - 1])
            else:
                emitted.append(letter)
        return state, emitted

    def encode(self, word):
        return ''.join(self.codes[letter] for letter in word)


def reader_test():
    cases = [('', []), ('a', [('', '')]), ('abc', [('', 'ab')]),
             ('abc', [('', 'ab'), ('b', 'c')]),
             ('abcde', [('', 'ab'), ('b', 'ca'), ('da', 'ee')]),
             ('abcde', [('ac', 'bdd'), ('', '')])]
    checks = 0
    for letters, relations in cases:
        reader = Reader(letters, relations)
        for start in reader.states:
            for length in range(4):
                for word in product(letters, repeat=length):
                    _, emitted = reader.read(reader.encode(word), start)
                    assert [v for v in emitted if v is not None] == list(word)
                    for x in word:
                        _, events = reader.read(reader.codes[x], start)
                        assert events == [None] * (len(events) - 1) + [x]
                    checks += 1
            for u, v in relations:
                assert reader.read(reader.encode(u), start)[0] == reader.read(reader.encode(v), start)[0]
    # Strict one-object 2-category with one arrow, two 2-cells (addition mod 2),
    # and only identity 3-cells. The generating birth and its parallel twin
    # receive different colours. Whisker both by d, whose code resets the state.
    reader = Reader('abcde', cases[-2][1])
    def action(word):
        return tuple(reader.states.index(reader.read(reader.encode(word), s)[0]) for s in reader.states)

    def horizontal(left, right):
        h, a = left
        k, b = right
        return tuple(k[j] for j in h), tuple((a[i] + b[j]) % 2 for i, j in enumerate(h))

    zero = (0,) * len(reader.states)
    one = (1,) * len(reader.states)
    assert action('') == action('ab')
    births = [(action('ab'), colour) for colour in (zero, one)]
    faces = [horizontal((action('d'), zero), birth) for birth in births]
    assert action('d') != action('') and {faces[0][0], faces[1][0]} == {action('dab')}
    assert faces[0][1] == zero and faces[1][1] == one
    # On a nonconstant test family, left whiskering actually changes coordinates.
    probe = (1,) + (0,) * (len(zero) - 1)
    _, reindexed = horizontal((action('d'), zero), (action(''), probe))
    assert len(set(reindexed)) == 1 and reindexed != probe
    return checks


def positioned_steps(word, rules, width):
    for lhs, rhs in rules:
        for i in range(len(word) - len(lhs) + 1):
            if word.startswith(lhs, i):
                nxt = word[:i] + rhs + word[i + len(lhs):]
                if len(nxt) <= width:
                    yield nxt


def cycle(successors):
    seen, pending = {''}, deque([''])
    while pending:
        for nxt in successors(pending.popleft()):
            if nxt == '':
                return True
            if nxt not in seen:
                seen.add(nxt)
                pending.append(nxt)
    return False


def marking_steps(word, rules, width):
    live = Counter(word)
    for lhs, rhs in rules:
        if Counter(lhs) <= live and len(word) - len(lhs) + len(rhs) <= width:
            yield ''.join(sorted((live - Counter(lhs) + Counter(rhs)).elements()))


def shuffle_test():
    swaps = [(a + b, b + a) for a, b in product('abc', repeat=2) if a != b]
    reactions = [('', 'ba'), ('', 'c'), ('ac', ''), ('ab', ''), ('c', 'a'),
                 ('bb', 'c'), ('a', 'b'), ('bc', 'ca')]
    checks = 0
    for count in range(len(reactions) + 1):
        for selected in combinations(reactions, count):
            rules = list(selected)
            for width in (2, 3, 4):
                actual = cycle(lambda w: positioned_steps(w, rules + swaps, width))
                abstract = cycle(lambda w: marking_steps(w, rules, width))
                assert actual == abstract
                checks += 1
    # The one-way swap leaves the first b in place. Its reverse gives a witness.
    rules = [('', 'ba'), ('ab', ''), ('ab', 'ba')]
    assert cycle(lambda w: marking_steps(w, rules, 2))
    assert not cycle(lambda w: positioned_steps(w, rules, 8))
    assert cycle(lambda w: positioned_steps(w, rules + [('ba', 'ab')], 2))
    return checks


if __name__ == '__main__':
    print(f'{closure_test()} presentations checked against all two-state actions.')
    print(f'{reader_test()} state/word readings checked, including mixed empty-path relations.')
    print(f'{shuffle_test()} bounded multiset cycle tests agreed with positioned word rewriting.')
