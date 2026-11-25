"""Read the mobile degree-five differences of a reversible planar label from cellular coordinates."""

from argparse import ArgumentParser
from collections import Counter
from itertools import product
import json
from pathlib import Path

from catt import STAR, arr, comp2, infer, maximal_vars, sub_from, subst_tm, v
from ct_suspension import ident
from semistrict_surface_divisible_squares import diagonalize
from semistrict_surface_mixed_winding import Reading, evaluate, naturality


def quotient(rows, vector, *, signs=False):
    size = len(vector)
    relations = list(rows)
    if signs:
        relations += [[2*int(i == j) for j in range(size)] for i in range(size)]
    matrix, columns, rank = diagonalize(relations, 0, size)
    result = []
    for j in range(size):
        value = sum(vector[i]*columns[i][j] for i in range(size))
        modulus = abs(matrix[j][j]) if j < rank else 0
        result.append(value % modulus if modulus else value)
    return result


def read(data):
    # Rows in d2 and d3 are the cellular boundaries of individual disks.
    x = data['eta']
    d2, d3 = data['d2'], data['d3']
    h = data['hurewicz']
    colours, windings = data['colours'], data['windings']
    if (len(h) != len(d2) or any(len(row) != len(h) for row in d3)
            or any(len(row) != len(x) for row in [*d2, *windings]) or len(colours) != len(windings)):
        raise ValueError('inconsistent cellular or puncture dimensions')
    for row in [*d3, h]:
        if any(sum(a*b[j] for a, b in zip(row, d2, strict=True)) for j in range(len(x))):
            raise ValueError('cellular boundaries and the Hurewicz representative must be cycles')
    weight = quotient(d3, h)
    signs = None if any(weight) else quotient(d2, x, signs=True)
    named = [quotient(d2, w) for w in windings]
    sums = {}
    for name, row in zip(colours, windings, strict=True):
        value = sums.setdefault(name, [0]*len(x))
        for j, a in enumerate(row):
            value[j] += a
    folded = {name: quotient(d2, w) for name, w in sums.items()}
    return dict(weight=weight, eta=signs, named=named, by_colour=folded,
                binary_fills=not (any(weight) or any(signs or []) or any(map(any, named))),
                joined_fills=not (any(weight) or any(map(any, folded.values()))))


def check_torsion_winding():
    line = ident((STAR,), v(0))
    unit = ident((STAR,), line)
    ctx = (STAR, arr(infer((STAR,), line), line, line), arr(infer((STAR,), unit), unit, unit))
    squares = []
    for left in (True, False):
        arity, square = naturality(left)
        terms = (v(2), v(1)) if left else (v(1), v(2))
        term = subst_tm(square, sub_from(arity, ctx, dict(zip(maximal_vars(arity), terms, strict=True))))
        infer(ctx, term)
        squares.append(term)
    checks = 0
    for m in range(2, 9):
        # Both sides of the local relator q^m -> 1 have the same charge mod m.
        power = v(2)
        for _ in range(1, m):
            power = comp2(ctx, 2, power, v(2))
        blank = ident(ctx, unit)
        assert infer(ctx, power) == infer(ctx, blank)
        for charge in range(m):
            labels = [Reading(), Reading(mass=1), Reading(charge=charge)]
            assert (evaluate(power, labels).charge - evaluate(blank, labels).charge) % m == 0
            circuit = Counter()
            for term in squares:
                circuit.update(evaluate(term, labels).edges)
            edge = ((0, 0), (1, 1))
            assert circuit[edge] % m == charge
            assert all(circuit[((0, i), (1, j))] % m == ((1 if i != j else -1)*charge) % m
                       for i, j in product(range(2), repeat=2))
            checks += 1
    return checks


def audit():
    count = 0
    # An invertible change of coordinates in both cellular ranks hides the cyclic factors.
    # The two rows of d2 are proportional. The primitive cycle in C2 is (-2,1).
    for m in range(2, 9):
        for k in range(2, 7):
            for s, t, u in product(range(-2, 3), repeat=3):
                data = dict(d2=[[m, m], [2*m, 2*m]], d3=[[-2*k, k]],
                            eta=[t, t], hurewicz=[-2*s, s],
                            colours=['b', 'b'], windings=[[u, u], [-u, -u]])
                result = read(data)
                assert result['joined_fills'] == (s % k == 0)
                assert result['binary_fills'] == (s % k == 0 and (m % 2 or t % 2 == 0) and u % m == 0)
                data['colours'] = ['b', 'c']
                assert read(data)['joined_fills'] == (s % k == 0 and u % m == 0)
                count += 2
    print(f'Checked {count:,} named and repeated-colour comparisons with cyclic torsion and free summands.')
    print(f'Checked {check_torsion_winding()} torsion charge assignments on the two typed naturality squares.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, help='cellular d2/d3 rows, Hurewicz cycle, residual eta vector, colours and winding rows')
    args = parser.parse_args()
    if args.input:
        print(json.dumps(read(json.loads(args.input.read_text()))))
    else:
        audit()
