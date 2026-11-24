"""Read degrees of mixed square reverses on paths of suspended computads."""
import argparse
import json
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path

from catt import STAR, arr, disc_tree, infer, maximal_vars, sub_from, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_comparison import boundary


def degree_pattern(edges):
    """Unary automaton. Return finite exceptions, periodic onset, period and residues."""
    # Phase 1 is the gap between the two elementary changes. Every edge
    # in the gap carries an object of its local presentation.
    outgoing = defaultdict(list)
    vertices = {s for s, _, _ in edges} | {t for _, t, _ in edges}
    for source, target, ranks in edges:
        for phase in range(3):
            outgoing[source, phase].append((0, (target, phase)))
        for phase in (0, 2):
            for rank in set(ranks):
                if rank <= 0:
                    raise ValueError('local generator ranks must be positive')
                # Expand this weight into single-letter transitions.
                node = source, phase
                for step in range(1, rank):
                    intermediate = ('unit-step', source, target, phase, rank, step)
                    outgoing[node].append((1, intermediate))
                    node = intermediate
                outgoing[node].append((1, (target, phase)))
        if 1 in ranks:
            outgoing[source, 0].append((0, (target, 1)))
            outgoing[source, 1].append((0, (target, 2)))

    def closure(states):
        states = set(states)
        pending = list(states)
        while pending:
            for cost, nxt in outgoing[pending.pop()]:
                if cost == 0 and nxt not in states:
                    states.add(nxt)
                    pending.append(nxt)
        return frozenset(states)

    current = closure((x, 0) for x in vertices)
    final = {(x, 2) for x in vertices}
    degree = 3
    seen, accepted = {}, set()
    while current not in seen:
        seen[current] = degree
        if current & final:
            accepted.add(degree)
        current = closure(nxt for state in current for cost, nxt in outgoing[state] if cost)
        degree += 1
    onset = seen[current]
    period = degree - onset
    return (sorted(d for d in accepted if d < onset), onset, period,
            sorted({d % period for d in accepted if d >= onset}))


def check_tableaux():
    count = 0
    for n in range(2, 6):
        for mark in range(n - 1):
            for outside in product((1, 2, 3, 4), repeat=n - 2):
                dims = outside[:mark] + (1, 1) + outside[mark:]
                sign = (-1) ** sum(dims[:mark])
                top = tuple((rank, 2) for rank in dims)
                for offset, length in ((-3, 1), (0, 2), (5, 3)):
                    # Compute the two specialized hemispheres from the tensor
                    # differential of the original globes. Only the translated
                    # interval has different images on its two proper facets.
                    ends = Counter()
                    for facet, coeff in boundary(top).items():
                        axis = next(i for i in range(n) if facet[i] != top[i])
                        rank, side = facet[axis]
                        if rank > 0:
                            continue  # a positive proper face of a scalar maps to zero
                        position = offset + (length if axis == mark and side else 0)
                        ends[axis, position] += coeff
                    ends = {key: v for key, v in ends.items() if v}
                    # Independently subdivide the lifted top into unit steps
                    # and compute its actual chain boundary by telescoping.
                    unit_boundary = Counter()
                    for j in range(offset, offset + length):
                        unit_boundary[mark, j] -= sign
                        unit_boundary[mark, j + 1] += sign
                    assert ends == {key: v for key, v in unit_boundary.items() if v}
                    assert sum(sign * j * v for (_, j), v in ends.items()) == length
                    count += 1
    return count


def accepted(pattern, d):
    finite, onset, period, residues = pattern
    return d in finite if d < onset else d % period in residues


def check_language():
    checks = 0
    for n in range(1, 6):
        for choices in product(((), (1,), (3,), (1, 2)), repeat=n):
            pattern = degree_pattern([(i, i+1, r) for i, r in enumerate(choices)])
            direct = set()
            for labels in product(*[(0, *r) for r in choices]):
                used = tuple(k for k in labels if k)
                if any(a == b == 1 for a, b in zip(used, used[1:])):
                    direct.add(1 + sum(used))
            assert {d for d in range(3, 3*n+4) if accepted(pattern, d)} == direct
            assert not pattern[3]
            checks += 1
    # No repeatable rank-one generator. The same higher-only edge can
    # occur repeatedly, with independent choices of its two local heights.
    graph = [(0, 1, (1,)), (1, 2, (1,)), (2, 2, (4, 6))]
    mixed = degree_pattern(graph)
    possible = {3 + 4*i + 6*j for i in range(40) for j in range(40)}
    assert all(accepted(mixed, d) == (d in possible) for d in range(3, 151))
    middle_only = degree_pattern([(0, 1, (1,)), (1, 1, (4, 6)), (1, 2, (1,))])
    assert middle_only[0] == [3] and not middle_only[3]
    four = degree_pattern([(i, i+1, (1, 2, 3, 4)) for i in range(4)])
    assert four[0] == list(range(3, 12)) and not four[3]
    return checks


def check_folded_substitutions(directory):
    first = arr(STAR, v(0), v(1))
    second = arr(STAR, v(1), v(5))
    loop = arr(STAR, v(5), v(5))
    ctx = (STAR, STAR, first, first, arr(first, v(2), v(3)), STAR,
           second, second, arr(second, v(6), v(7)), loop)
    face = ident(ctx, v(9))
    labels = {}
    for h in (2, 3):
        labels[h] = v(len(ctx))
        ctx += (arr(infer(ctx, face), face, face),)
        face = ident(ctx, face)

    emitter = Emitter()
    for i, exterior in enumerate([(), (2,), (3,), (2, 2), (2, 3), (3, 2)]):
        arity = tree_ctx(tuple(disc_tree(h) for h in (1, 1, *exterior)))
        generators = [v(4), v(8), *(labels[h] for h in exterior)]
        values = sub_from(arity, ctx, dict(zip(maximal_vars(arity), generators, strict=True)))
        g, p, s = emitter.ctx(ctx), emitter.ctx(arity), emitter.sub(values)
        emitter.checks.append(
            f'fold-{i} : {g} ⊢sub {s} ∶ {p}\n'
            f'fold-{i} = from-just (checkSub {g} (from-just (checkCtx {g})) {s} {p})\n')
    if directory:
        name = 'GrayWeightedSquare'
        body = emitter.module(name, __doc__).replace('open import CaTTExp.Pure',
                                                      'open import CaTTExp.Gray.Pure')
        (directory / (name + '.agda')).write_text(body)
    return len(emitter.checks)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--edges', help='JSON list of [start, end, local positive ranks] for traversable edges')
    parser.add_argument('--agda-dir', type=Path, help='write the six typed substitutions for Agda')
    args = parser.parse_args()
    if args.edges:
        with open(args.edges) as stream:
            print(degree_pattern(json.load(stream)))
    else:
        print(f'{check_tableaux()} signed top boundaries checked, including translated subdivisions.')
        print(f'{check_language()} finite lines compared with literal label enumeration; cyclic cases checked.')
        print(f'{check_folded_substitutions(args.agda_dir)} folded raw substitutions constructed.')
