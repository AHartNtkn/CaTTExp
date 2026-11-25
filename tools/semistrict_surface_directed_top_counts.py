"""Decide positive fifth-cell counts over a finitely presented abelian difference group."""

from argparse import ArgumentParser
from collections import Counter
from itertools import product
import json
from pathlib import Path
import re

from catt import infer, maximal_vars, src, tdim, tgt, v
from emit_agda import Emitter
from semistrict_surface_higher_winding import disk
from semistrict_surface_mixed_winding import Reading, evaluate, slots
from semistrict_surface_penultimate_intervals import check, total
from semistrict_surface_reversible_five import quotient


def linear_system(relations, rules, face, counts=None):
    if any(len(row) != len(face) for row in [*relations, *rules]):
        raise ValueError('all rows must have the same width as the face')
    if counts is not None and (len(counts) != len(rules) or any(x < 0 for x in counts)):
        raise ValueError('provide one nonnegative count per directed rule')
    if any(type(x) is not int for row in [*relations, *rules, face, counts or []] for x in row):
        raise ValueError('all coordinates and counts must be integers')
    names = [f'u{i}' for i in range(len(rules))]
    signed = [f'r{i}' for i in range(len(relations))]
    lines = ['(set-logic QF_LIA)']
    for name in names + signed:
        lines.append(f'(declare-const {name} Int)')
    for i, name in enumerate(names):
        lines.append(f'(assert (>= {name} 0))')
        if counts is not None:
            lines.append(f'(assert (= {name} {counts[i]}))')
    for i, value in enumerate(face):
        terms = [f'(* {row[i]} {name})' for name, row in zip(names + signed, rules + relations, strict=True)
                 if row[i]]
        lines.append(f'(assert (= {total(terms)} {value}))')
    return '\n'.join(lines)


def uses(relations, rules, face, counts=None):
    system = linear_system(relations, rules, face, counts) + '\n(check-sat)'
    answer = check(system)
    if answer == 'unsat':
        return None
    if answer != 'sat':
        raise RuntimeError(answer)
    values = []
    if rules:
        names = ' '.join(f'u{i}' for i in range(len(rules)))
        model = check(f'{system}\n(get-value ({names}))')
        given = dict(re.findall(r'\((u\d+)\s+(\d+)\)', model))
        values = [int(given[f'u{i}']) for i in range(len(rules))]
    difference = [x - sum(n*row[i] for n, row in zip(values, rules, strict=True))
                  for i, x in enumerate(face)]
    assert not any(quotient(relations, difference))
    assert counts is None or counts == values
    return values


def top_count(term, marked):
    if term[0] == 'v':
        return int(term[1] == marked)
    _, arity, ty, sub = term
    if tdim(ty)+1 != 5:
        return 0
    first, _ = slots(arity)
    return sum(top_count(sub[i], marked) for p, i in first.items() if len(p) == 5)


def scaled(chain, coefficient):
    return Counter({edge: value*coefficient for edge, value in chain.items()})


def transport(directory):
    omega = {((0,i),(1,j)): (1 if i != j else -1) for i,j in product(range(2), repeat=2)}
    emitter = Emitter() if directory else None
    checks = 0
    for left in (True, False):
        ctx, naturality = disk(5, left)
        planes = infer(ctx, naturality)[2:]
        first, second = maximal_vars(ctx)
        change, spectator = (first, second) if left else (second, first)
        source, target = src(ctx, v(change))[1], tgt(ctx, v(change))[1]
        _, at = slots(ctx)
        if emitter:
            for j, plane in enumerate(planes):
                emitter.check_type(f'route{int(left)}x{j}', ctx, plane, infer(ctx, planes[0]))
        for mass, charge, old, shift in product((-2, 3), (-1, 2), (-1, 0, 2), (-3, 0, 4)):
            labels = [Reading(mass=mass if p == at[spectator] else 0,
                              charge=charge if len(p) == 3 else 0) for p in at]
            labels[source].edges = scaled(omega, old)
            labels[target].edges = scaled(omega, old+shift)
            for plane in planes:
                before, after = (evaluate(f, labels).edges for f in infer(ctx, plane)[2:])
                difference = after.copy()
                difference.subtract(before)
                assert top_count(plane, change) == 1
                assert difference == scaled(omega, shift)
                # The fixed mixed arc is nonzero even at zero intrinsic reading.
                assert before != scaled(omega, old)
                checks += 1
    if emitter:
        (directory / 'DirectedTopCounts.agda').write_text(emitter.module('DirectedTopCounts', __doc__))
    return checks


def cone_audit():
    # A positive free coordinate bounds the number of uses here, independently of SMT.
    rules = [[1, 2], [0, 3]]
    queries, expected = [], []
    for joined, e, x in product((False, True), range(2), range(-2, 14)):
        period = 1 if joined else 2
        possible = any(2*a+3*b == x and (a-e) % period == 0 for a,b in product(range(8), repeat=2))
        system = linear_system([[period, 0]], rules, [e, x])
        queries.append('(push)\n' + system.partition('\n')[2] + '\n(check-sat)\n(pop)')
        expected.append('sat' if possible else 'unsat')
    assert check('(set-logic QF_LIA)\n' + '\n'.join(queries)).splitlines() == expected
    assert uses([[2, 0]], rules, [1, 8]) == [1, 2]
    assert uses([[2, 0]], rules, [0, 8], [1, 2]) is None
    assert uses([[1, 0]], rules, [0, 8], [1, 2]) == [1, 2]
    return len(expected)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path,
                        help='JSON with relations, rules, face and optional prescribed counts')
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        try:
            result = uses(data['relations'], data['rules'], data['face'], data.get('counts'))
        except ValueError as exc:
            parser.error(str(exc))
        print('No directed filler.' if result is None else f'Directed filler counts {result}.')
    else:
        print(f'{transport(args.agda_dir)} raw transport readings and {cone_audit()} integral monoid decisions checked.')
