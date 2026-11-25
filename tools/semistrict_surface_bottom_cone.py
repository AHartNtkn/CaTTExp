"""Compute the bottom-sphere and Hurewicz tests on a wedge of cyclic Moore spaces."""
from argparse import ArgumentParser
from itertools import combinations, product
import json
from math import gcd
from pathlib import Path

from semistrict_surface_reversible_five import quotient


def diagram(m, orders, middle, top):
    if any(type(k) is not int for k in (m, middle, top, *orders)):
        raise ValueError('expected integer rank, orders and sphere counts')
    if m < 3 or min([middle, top, *orders]) < 0:
        raise ValueError('use rank at least three and nonnegative orders and sphere counts')
    torsion, bottom, hopf, hurewicz = [], [], [], []
    names = []

    def letter(name, order, *families):
        names.append(name)
        for family in families:
            family.append(name)
        if order:
            torsion.append({name: order})
        return name

    for i, d in enumerate(orders, 1):
        if d % 2:
            continue
        e = letter(f'e{i}', 2, bottom, hopf, hurewicz)
        if d:
            u = letter(f'u{i}', 0, hurewicz)
            relation = {u: 2}
            if d % 4 == 2:
                relation[e] = -1
            torsion.append(relation)
    if m == 3:
        for i, j in combinations(range(len(orders)), 2):
            order = gcd(orders[i], orders[j])
            if order != 1:
                letter(f'z{i+1}_{j+1}', order, bottom, hurewicz)
    for i in range(1, middle + 1):
        letter(f'h{i}', 2, hopf, hurewicz)
    for i in range(1, top + 1):
        letter(f'c{i}', 0)
    return names, torsion, bottom, hopf, hurewicz


def solve(data):
    names, torsion, bottom, hopf, hurewicz = diagram(
        data['rank'], data['orders'], data.get('middle', 0), data.get('top', 0))

    def vector(row):
        if row.keys() - set(names) or any(type(n) is not int for n in row.values()):
            raise ValueError(f'expected integer coordinates from {names}')
        return [row.get(s, 0) for s in names]

    face = vector(data['face'])
    rows = [vector(row) for row in torsion + data.get('relations', [])]

    def inside(family):
        return not any(quotient(rows + [vector({s: 1}) for s in family], face))

    def comparison(sufficient, necessary):
        if sufficient:
            return True
        if not necessary:
            return False
        return None

    raw = inside([])
    return {'basis': names, 'raw': raw, 'insertion': raw,
            'binary': comparison(raw, inside(bottom)),
            'join': comparison(inside(hopf), inside(hurewicz))}


def check_halving():
    # K <= F = Z^2 has these two independent (possibly nonprimitive) columns.
    # Compare halving a relation with enumerating all elements killed by two
    # in the quotient lattice, including off-diagonal changes of generators.
    cases = 0
    for a, b, c in product(range(1, 7), range(-3, 4), range(1, 7)):
        def normal(x, y):
            q, v = divmod(y, c)
            return ((x - q*b) % a, v)

        halved = [normal((a*i+b*j)//2, c*j//2)
                  for i, j in product(range(2), repeat=2) if not ((a*i+b*j) % 2 or c*j % 2)]
        killed = {(x, y) for x, y in product(range(a), range(c)) if normal(2*x, 2*y) == (0, 0)}
        assert len(halved) == len(killed) and set(halved) == killed
        cases += 1
    return cases


def audit():
    uses = 0
    for order in range(2, 17, 2):
        for e, u in product(range(-2, 3), repeat=2):
            d = {'rank': 3, 'orders': [order], 'face': {'e1': e, 'u1': u}}
            answer = solve(d)
            raw = (u + 2*e) % 4 == 0 if order % 4 == 2 else u % 2 == 0 and e % 2 == 0
            assert answer['raw'] == raw
            assert answer['binary'] == (True if raw else None if u % 2 == 0 else False)
            assert answer['join'] == (True if u % 2 == 0 else None)
            uses += 1

    # A row tying the coextension to a free 5-cell keeps its residual class.
    # A second independent row on that free cell turns it into a bottom value.
    data = {'rank': 3, 'orders': [2], 'top': 1, 'face': {'c1': 1},
            'relations': [{'u1': 1, 'c1': -1}]}
    assert solve(data)['binary'] is False and solve(data)['join'] is None
    data['relations'].append({'c1': 1, 'e1': -1})
    assert solve(data)['raw']  # u=e=2u forces u=0

    # In C = <c,h | c=h, 2h=0>, a one-way step of difference c
    # fills a query of difference k*c with n uses exactly when k-n is even.
    # The join kills h, so every count has a fit at the final boundary.
    data = {'rank': 3, 'orders': [9], 'middle': 1, 'top': 1,
            'relations': [{'c1': 1, 'h1': -1}]}
    for k, n in product(range(-3, 4), range(5)):
        answer = solve(dict(data, face={'c1': k - n}))
        assert answer['raw'] == answer['binary'] == ((k - n) % 2 == 0)
        assert answer['join'] is True

    for m in (3, 4):
        example = {'rank': m, 'orders': [3, 9], 'face': {}}
        if m == 3:
            for k in range(-5, 6):
                example['face'] = {'z1_2': k}
                answer = solve(example)
                assert answer['raw'] == (k % 3 == 0)
                assert answer['join'] == (True if k % 3 == 0 else None)
        else:
            assert not solve(example)['basis']
    print(f'{uses} Moore coextension tests matched cyclic or split groups.')
    print(f'{check_halving()} relation lattices gave exactly the independently enumerated two-torsion.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path)
    args = parser.parse_args()
    if args.input:
        print(json.dumps(solve(json.loads(args.input.read_text()))))
    else:
        audit()
