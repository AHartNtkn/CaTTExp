"""Compute bottom degree-five obstructions on diagonal mapping tori of Moore wedges."""

import json
from argparse import ArgumentParser
from itertools import combinations, product
from math import gcd, prod
from pathlib import Path

from semistrict_surface_bottom_four import hall_triples


def limit_order(order, multiplier):
    """Order of the initial cyclic generator in the direct limit."""
    if multiplier == 0:
        return 1
    if order == 0:
        return 0
    while (common := gcd(order, multiplier)) > 1:
        order //= common
    return order


def read(orders, degrees):
    if len(orders) != len(degrees) or any(type(d) is not int for d in degrees):
        raise ValueError('give an integer degree for every summand')
    if any(type(n) is not int or n < 0 or n == 1 for n in orders):
        raise ValueError('use zero for a sphere or a Moore order at least two')
    columns = []
    def add(operation, letters, order):
        multiplier = prod(degrees[i] for i in letters)
        survives = limit_order(order, multiplier)
        if survives != 1:
            columns.append(dict(operation=operation, letters=[i+1 for i in letters],
                                stage_order=order, multiplier=multiplier, order_in_limit=survives))

    for i,n in enumerate(orders):
        add('double Hopf', (i,i), gcd(2,n))
    for i,j in combinations(range(len(orders)),2):
        add('pair Hopf', (i,j), gcd(2, orders[i], orders[j]))
    for i,j,k in hall_triples(len(orders)):
        add('triple', (i,j,k), gcd(orders[i], orders[j], orders[k]))
    return dict(bottom_image_zero=not columns, surviving_columns=columns)


def audit():
    comparisons = 0
    for order, m in product(range(1,65), range(-8,9)):
        # Iterate the actual map on every residue. Repetition detects an
        # orbit that never hits zero, also for zero or negative degree.
        expected = limit_order(order,m)
        for residue in range(order):
            v, seen = residue,set()
            while v and v not in seen:
                seen.add(v)
                v = m*v % order
            assert (v == 0) == (residue % expected == 0)
            comparisons += 1
    wedge_cases = 0
    for m,n,a,b in product((0,2,3,4,6,9), (0,2,3,4,6,9), (0,1,2,3,6), (0,1,2,3,6)):
        # Stage homology is Z[1/a] for a surviving free summand, and a
        # reduced finite cyclic group for a finite one. Independently apply
        # the local criterion to the resulting abstract bottom group.
        free = [d for size,d in ((m,a),(n,b)) if size == 0 and d]
        finite = [limit_order(size,d) for size,d in ((m,a),(n,b)) if size]
        zero = (len(free) <= 1 and all(d % 2 == 0 for d in free)
                and all(size % 2 for size in finite))
        zero &= all(gcd(x,y) == 1 for x,y in combinations(finite,2))
        for d in free:
            zero &= all(limit_order(size,d) == 1 for size in finite)
        assert read([m,n],[a,b])['bottom_image_zero'] == zero
        wedge_cases += 1
    # At the finite Prüfer stages only one torsion letter is present in
    # [[z,t],z]. Its transition is p times a p-unit on a class of order p^k.
    for p in (3,5,7):
        for k in range(1,7):
            for d in (1,p+1):
                assert p**(k+1)//gcd(p**(k+1), p*d*d) == p**k
    return comparisons, wedge_cases


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path, help='JSON with orders and degrees lists')
    args = parser.parse_args()
    if args.input:
        try:
            data = json.loads(args.input.read_text())
            print(json.dumps(read(data['orders'],data['degrees'])))
        except (KeyError, ValueError) as error:
            parser.error(str(error))
    else:
        comparisons, wedge_cases = audit()
        print(f'{comparisons} cyclic direct-limit memberships and {wedge_cases} wedge mapping tori checked.')
