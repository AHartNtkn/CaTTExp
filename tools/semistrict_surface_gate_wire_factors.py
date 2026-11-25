"""Verify the planar transition factors on a mixed diagram, including all simplex faces."""

from collections import defaultdict
from itertools import product
from math import comb

from semistrict_surface_planar_occurrences import component_transport, spellings

SHAPE = {'d': ('a', ''), 'b': ('', 'b'), 'r': ('ab', 'b')}
INITIAL = 'aa'
EXAMPLE = (('d', 0), ('b', 1), ('r', 0))
STATES = ('s', 't', '1', '2')


def socket(gate):
    return gate[:1] if gate[:1] in SHAPE else None


def live_after(live, base, offset):
    a, b = SHAPE[base]
    assert live[offset:offset+len(a)] == a
    return live[:offset] + b + live[offset+len(a):]


def decorate(rows, count):
    def visit(k, live, left, prefix):
        if k == len(rows) and left == 0:
            yield prefix
        if k < len(rows):
            g, i = rows[k]
            for state in STATES if g == 'r' else ('',):
                yield from visit(k+1, live_after(live, g, i), left, prefix+((g+state, i),))
        if left:
            for i, name in enumerate(live):
                for tag in '12':
                    yield from visit(k, live, left-1, prefix+(('u'+name+tag, i),))
    yield from visit(0, INITIAL, count, ())


def split(history, ident):
    ordinary = tuple((socket(g), i) for g, i in history if socket(g))
    ids = iter(ident[ordinary])
    live = [(-1, j) for j in range(len(INITIAL))]
    records = defaultdict(list)
    states = {}
    for gate, i in history:
        g = socket(gate)
        if g is None:
            records[live[i]].append(gate[-1])
        else:
            slot = next(ids)
            states[slot] = gate[1:]
            n, m = map(len, SHAPE[g])
            live[i:i+n] = [(slot, j) for j in range(m)]
    return tuple(sorted(states.items())), tuple(sorted((k, ''.join(w)) for k, w in records.items()))


def face_tag(tag, d):
    if tag not in ('1', '2'):
        return tag
    if d == 0 and tag == '1':
        return 't'
    if d == 2 and tag == '2':
        return 's'
    return '1'


def restrict(rows, d):
    result = []
    for g, i in rows:
        if g.startswith('u'):
            f = face_tag(g[-1], d)
            if f == '1':
                result.append((g[:-1]+f, i))
        else:
            result.append((g[:1]+face_tag(g[1:], d), i))
    return tuple(result)


def restrict_factors(factors, d):
    states, marks = factors
    new_marks = []
    for k, word in marks:
        reduced = ''.join('1' for tag in word if face_tag(tag, d) == '1')
        if reduced:
            new_marks.append((k, reduced))
    return tuple((k, face_tag(s, d)) for k, s in states), tuple(new_marks)


def run():
    for root, ident, rigid in component_transport(spellings(INITIAL, SHAPE, len(EXAMPLE)), SHAPE):
        if EXAMPLE in ident:
            break
    else:
        raise AssertionError('example is not a typed planar history')
    assert rigid
    arities = dict(SHAPE)
    arities.update({'r'+s: SHAPE['r'] for s in STATES})
    arities.update({'u'+a+t: (a, a) for a, t in product('ab', '12')})
    wires = len(INITIAL) + sum(len(SHAPE[g][1]) for g, _ in root)
    for n in range(4):
        words = {w for rows in ident for w in decorate(rows, n)}
        factors = set()
        for representative, transports, rigid in component_transport(words, arities):
            assert rigid
            data = split(representative, ident)
            assert data not in factors
            factors.add(data)
            for w in transports:
                assert split(w, ident) == data
            for d in range(3):
                assert split(restrict(representative, d), ident) == restrict_factors(data, d)
        expected = len(STATES) * comb(n+wires-1, wires-1) * 2**n
        assert len(factors) == expected
        print(f'{n} wire marks: {len(words)} serial spellings, {len(factors)} coordinate tuples, {3*len(factors)} simplex faces')


if __name__ == '__main__':
    run()
