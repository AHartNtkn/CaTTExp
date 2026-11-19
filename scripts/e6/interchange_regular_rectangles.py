"""Synthesize context-stable quadratic orders on a finite path presentation.

Each edge carries an additive vector q and a scalar l. A path has charge
sum(q) and score sum(l) + sum_{i<j} omega(q_i, q_j) for a skew form omega.
When parallel paths have equal charge, their score difference is unchanged
by arbitrary matching prefixes and suffixes. A certificate checks charge
preservation on every rule and the required score inequalities exactly.
Consequently the certificate applies to words of unrestricted length.

find_rank uses glpsol to search for coefficients. verify_rank needs only
Python. A failed search is inconclusive about directed reachability.
"""
import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from math import gcd, lcm
from pathlib import Path as FilePath
import subprocess
from tempfile import TemporaryDirectory


def add(row, vector, factor=1):
    for key, value in vector.items():
        total = row.get(key, 0) + factor * value
        if total:
            row[key] = total
        else:
            row.pop(key, None)


def chords(presentation):
    """Index nonforest edges. Tree coboundaries cancel on parallel paths."""
    parent = {}

    def component(u):
        while u in parent:
            if parent[u] in parent:
                parent[u] = parent[parent[u]]
            u = parent[u]
        return u

    result = {}
    for name, edge in sorted(presentation.edges.items()):
        a, b = component(edge.source), component(edge.target)
        if a == b:
            result[name] = len(result)
        else:
            parent[b] = a
    return result


def conserved_charges(presentation, index):
    """Quotient chord counts by the count differences of all parallel rules."""
    basis = {}
    for rule in presentation.rules.values():
        row = dict(Counter(index[e] for e in rule.source.edges if e in index))
        add(row, Counter(index[e] for e in rule.target.edges if e in index), -1)
        while row:
            pivot = max(row)
            if pivot not in basis:
                basis[pivot] = {k: Fraction(v, row[pivot]) for k, v in row.items()}
                break
            add(row, basis[pivot], -row[pivot])

    image = {}
    for i in range(len(index)):
        if i in basis:
            vector = {}
            for j, value in basis[i].items():
                if i != j:
                    add(vector, image[j], -value)
            image[i] = vector
        else:
            image[i] = {i: 1}
    return {e: image[i] for e, i in index.items() if image[i]}


def wedge_into(row, before, current):
    for i, a in before.items():
        for j, b in current.items():
            if i != j:
                key = (i, j) if i < j else (j, i)
                value = a * b if i < j else -a * b
                total = row.get(key, 0) + value
                if total:
                    row[key] = total
                else:
                    row.pop(key, None)


def coordinates(path, charges, index):
    """Sparse linear and signed-area features, and the path's total charge."""
    before, area = {}, {}
    for edge in path.edges:
        current = charges.get(edge, {})
        wedge_into(area, before, current)
        add(before, current)
    row = dict(Counter(index[e] for e in path.edges if e in index))
    row.update(area)
    return row, before


@dataclass
class Rank:
    charges: dict
    index: dict
    coefficients: dict

    def evaluate(self, path):
        row, total = coordinates(path, self.charges, self.index)
        return total, sum(v * self.coefficients.get(k, 0) for k, v in row.items())


def verify_rank(presentation, strict_pairs, rank):
    """Exact verification uses only the stated model and grounded presentation."""
    if not all(type(value) in (int, Fraction) for value in rank.coefficients.values()):
        return False
    if not all(type(value) in (int, Fraction) for vector in rank.charges.values()
               for value in vector.values()):
        return False

    def compare(a, b):
        qa, va = rank.evaluate(a)
        qb, vb = rank.evaluate(b)
        return qa == qb, va - vb

    for rule in presentation.rules.values():
        equal, drop = compare(rule.source, rule.target)
        if not equal or drop < 0 or rule.equation and drop != 0:
            return False
    for a, b in strict_pairs:
        presentation.parallel(a, b)
        equal, drop = compare(a, b)
        if not equal or drop <= 0:
            return False
    return True


def integral_row(row):
    denom = lcm(*(Fraction(v).denominator for v in row.values()))
    scaled = {k: int(v * denom) for k, v in row.items()}
    common = reduce(gcd, scaled.values(), 0)
    return {k: v // common for k, v in scaled.items()}


def feasible(rows):
    """Solve the homogeneous inequalities with a unit margin on strict rows."""
    columns = {}
    constraints = []
    for row, relation in rows:
        if not row:
            if relation == '>':
                return None
            continue
        parts = []
        for key, value in integral_row(row).items():
            i = columns.setdefault(key, len(columns) + 1)
            parts.append(f'{"+" if value > 0 else "-"} {abs(value)} x{i}')
        op = {'>': '>= 1', '=': '= 0', '>=': '>= 0'}[relation]
        constraints.append(' '.join(parts) + ' ' + op)
    if not columns:
        return {}
    with TemporaryDirectory() as temp:
        directory = FilePath(temp)
        lp, answer, model = (directory / x for x in ('rank.lp', 'rank.sol', 'rank.glp'))
        lp.write_text('Minimize\n 0 x1\nSubject To\n' + '\n'.join(constraints) +
                      '\nBounds\n' + '\n'.join(f'x{i} free' for i in columns.values()) +
                      '\nEnd\n')
        run = subprocess.run(['glpsol', '--lp', str(lp), '--exact', '--write', str(answer),
                              '--wglp', str(model)], capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
        lines = [s.split() for s in answer.read_text().splitlines()]
        if not any(s[:3] == ['c', 'Status:', 'OPTIMAL'] for s in lines):
            return None
        names = {int(s[2]): int(s[3][1:]) for s in
                 (line.split() for line in model.read_text().splitlines()) if s[:2] == ['n','j']}
        values = {names[int(s[1])]: Fraction(s[3]).limit_denominator(10**7)
                  for s in lines if s[0] == 'j'}
    return {k: values[i] for k, i in columns.items() if values[i]}


def find_rank(presentation, strict_pairs):
    """Return a verified strict order witness, or None if the search found none.

    Each strict pair is ordered (source, target), with the source scoring higher.
    They can be elementary temporal deltas or designated parallel composites.
    """
    strict_pairs = tuple(strict_pairs)
    index = chords(presentation)
    for a, b in strict_pairs:
        presentation.parallel(a, b)

    def choose(charges):
        rows = []

        def require(a, b, relation):
            left, qa = coordinates(a, charges, index)
            right, qb = coordinates(b, charges, index)
            if qa != qb:
                return False
            add(left, right, -1)
            rows.append((left, relation))
            return True

        for rule in presentation.rules.values():
            if not require(rule.source, rule.target, '=' if rule.equation else '>='):
                raise ValueError(f'charge changed on grounded rule {rule.name}')
        if not all(require(a, b, '>') for a, b in strict_pairs):
            return None
        coefficients = feasible(rows)
        if coefficients is None:
            return None
        result = Rank(charges, index, coefficients)
        if not verify_rank(presentation, strict_pairs, result):
            raise ArithmeticError('The LP solution could not be reconstructed exactly.')
        return result

    additive = choose({})
    if additive is not None:
        return additive
    return choose(conserved_charges(presentation, index))


# Scalar scores on the strip, keyed by one-based index in the sorted edge
# names. All other edges score zero. The interpretation checks every rule,
# so the certificate can be replayed with no optimization library.
STRIP_SCORES = {
    'X': {1: -1, 2: -1, 3: -2, 4: -3, 5: -1, 6: -2, 7: -1, 12: -1, 13: -1,
          19: 1, 20: 1, 30: -1, 37: -1, 38: -2, 40: -1, 42: -1, 45: 1,
          52: 1, 53: 1, 54: 1, 55: -1, 65: -1, 68: 2, 74: -1, 75: -1,
          76: 1, 83: 1, 91: 2, 92: 1, 93: 1, 99: 1},
    'Y': {1: 1, 2: 2, 7: 2, 10: 1, 12: -1, 14: 1, 16: 1, 17: 1, 26: 1,
          29: 1, 30: 1, 32: 1, 33: -1, 34: -1, 37: -1, 38: -1, 40: -1,
          41: -1, 43: -2, 45: -2, 46: -2, 47: -1, 48: -1, 64: -1, 72: -1,
          76: 1, 80: 1, 83: 1, 86: 3, 93: 1, 94: 1, 95: 1, 96: 1},
}


def check_strips(synthesize=False):
    from interchange_strip_ground import ground_all

    for unary, scores in STRIP_SCORES.items():
        graph = ground_all(unary)
        deltas = [(r.source, r.target) for r in graph.rules.values() if r.name.startswith('delta ')]
        index = {e: i for i, e in enumerate(sorted(graph.edges), 1)}
        rank = Rank({}, index, scores)
        if len(deltas) != 43 or not verify_rank(graph, deltas, rank):
            raise ValueError(f'{unary}: invalid strip certificate')
        margins = [rank.evaluate(a)[1] - rank.evaluate(b)[1] for a, b in deltas]
        print(f'{unary}: {len(scores)} nonzero integer scores, {len(graph.rules)} rules, '
              f'{len(deltas)} strict deltas, drops {min(margins)} to {max(margins)}.')
        if synthesize:
            witness = find_rank(graph, deltas)
            if witness is None or witness.charges:
                raise ValueError(f'{unary}: additive-rank synthesis failed')
            print(f'{unary}: synthesized and verified an additive rank.')


def check_two_loops(synthesize=False):
    from interchange_reachability import Edge, Path, Presentation, Rule

    start = 'v'
    edges = {e: Edge(start, start, 1) for e in ('a', 'b')}
    late_first, early_first = Path(start, ('b', 'a')), Path(start, ('a', 'b'))
    pairs = [(late_first, early_first)]
    delta = Rule('delta', late_first, early_first)
    graph = Presentation([start], edges, [delta])
    # Both paths contain the same edges with the same multiplicities. Every
    # scalar additive order therefore ties. Signed area distinguishes them.
    rank = Rank({'a': {0: 1}, 'b': {1: 1}}, {}, {(0, 1): -1})
    if not verify_rank(graph, pairs, rank):
        raise ValueError('invalid signed-area witness on the doubled loop')
    if synthesize:
        result = find_rank(graph, pairs)
        if result is None or not result.charges:
            raise ValueError('doubled-loop signed-area synthesis failed')
    print('Two independent loops: the signed-area certificate gives a strict delta.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--synthesize', action='store_true', help='also discover fresh ranks using glpsol')
    args = parser.parse_args()
    check_strips(args.synthesize)
    check_two_loops(args.synthesize)
