"""Separate an integral gap-sphere class by linking in a finite sheet cover."""

from argparse import ArgumentParser
from collections import Counter
import json
from pathlib import Path

from semistrict_surface_history_group import inv, reduced
from semistrict_surface_shared_edge import braid_image


def coefficients(terms, punctures):
    result = Counter()
    for value, word in terms:
        if type(value) is not int or any(type(x) is not int or not 1 <= abs(x) <= punctures for x in word):
            raise ValueError('expected an integer coefficient and signed one-based puncture indices')
        result[reduced(word)] += value
    return {w: c for w, c in result.items() if c}


def cover(words, punctures):
    # Right multiplication on the prefix tree gives a partial injection
    # for each positive letter, even when an edge is traversed backwards.
    prefixes = sorted({()} | {w[:k] for w in words for k in range(1, len(w)+1)})
    address = {w: i for i, w in enumerate(prefixes)}
    rows = []
    for letter in range(1, punctures+1):
        partial = {i: address[v] for i, w in enumerate(prefixes)
                   if (v := reduced(w + (letter,))) in address}
        free_from = sorted(set(address.values()) - partial.keys())
        free_to = sorted(set(address.values()) - set(partial.values()))
        partial.update(zip(free_from, free_to, strict=True))
        rows.append(tuple(partial[i] for i in range(len(prefixes))))
    return prefixes, rows


def lift(word, start, rows):
    for x in word:
        row = rows[abs(x)-1]
        start = row[start] if x > 0 else row.index(start)
    return start


def readout(terms, punctures):
    support = coefficients(terms, punctures)
    names, rows = cover(support, punctures)
    linking = Counter()
    for sheet in range(len(names)):
        for word, value in support.items():
            linking[sheet, lift(word, sheet, rows)] += value
    at_origin = {names[j]: n for (i, j), n in linking.items() if i == 0 and n}
    assert at_origin == support
    return names, rows, {pair: n for pair, n in linking.items() if n}


def brunnian(m):
    word = (1,)
    for letter in range(2, m+1):
        word = reduced(word + (letter,) + inv(word) + (-letter,))
    return word


def push(word, punctures):
    # The moving strand starts at the right of the ordered stationary rods.
    braid = ()
    for letter in word:
        i = abs(letter)
        approach = tuple(range(punctures, i, -1))
        turn = approach + (i, i) + inv(approach)
        braid += turn if letter > 0 else inv(turn)
    return braid


def restrict_braid(word, strands, omit):
    order = list(range(strands))
    kept = []
    for letter in word:
        i = abs(letter)-1
        if omit not in order[i:i+2]:
            slot = 1 + sum(k != omit for k in order[:i])
            kept.append(slot if letter > 0 else -slot)
        order[i:i+2] = order[i+1], order[i]
    assert order == list(range(strands))
    return kept


def audit():
    for m in range(1, 7):
        w = brunnian(m)
        terms = [(1, ()), (-1, w)]
        assert coefficients(terms, m) and all(not reduced(x for x in w if abs(x) != j)
                                               for j in range(1, m+1))
        sheets, rows, linking = readout(terms, m)
        assert linking[0, 0] == 1 and linking[0, lift(w, 0, rows)] == -1
        if m > 1:
            assert all(w.count(j) == w.count(-j) for j in range(1, m+1))
        if m <= 3:
            braid = push(w, m)
            assert braid_image(m+1, braid) != braid_image(m+1, ())
            for j in range(m):
                assert braid_image(m, restrict_braid(braid, m+1, j)) == braid_image(m, ())
        print(m, 'punctures; commutator length', len(w), 'cover sheets', len(sheets),
              'origin linking', {j: n for (i, j), n in linking.items() if not i})
    # Signed words with cancellation, multiple coefficients and a zero class.
    assert readout([(4, (-1, 2, 1)), (-2, (1, -1)), (7, ()), (1, (-1, 2, 1))], 2)[2]
    assert readout([(3, (1, -1)), (-3, ())], 1)[2] == {}


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path, help='JSON with punctures and [coefficient, word] terms')
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        punctures = data['punctures']
        if type(punctures) is not int or punctures < 0:
            parser.error('punctures must be a nonnegative integer')
        try:
            sheets, rows, linking = readout(data['terms'], punctures)
        except ValueError as err:
            parser.error(str(err))
        print('zero class:', not linking)
        print('sheet names:', sheets)
        print('positive puncture permutations:', rows)
        print('nonzero ordered-pair linking coefficients:', linking)
    else:
        audit()
