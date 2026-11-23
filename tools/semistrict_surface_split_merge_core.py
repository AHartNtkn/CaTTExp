"""Check the top-rule dependency criterion and the mapping-space comparison on finite diagrams."""
from argparse import ArgumentParser
from collections import defaultdict
from dataclasses import dataclass
from itertools import product
from pathlib import Path

from catt import STAR, arr, check_ctx, coh_between, comp2, disc_tree, infer, sub_from, subst_tm, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity


@dataclass(frozen=True)
class Rule:
    before: str
    after: str


def core(rules, protected=(), higher_sources='', higher_targets=''):
    # For this word presentation a literal variable is precisely a word of length one.
    successors = [{j for j, other in enumerate(rules) if set(rule.after) & set(other.before)}
                  for rule in rules]
    predecessors = [{i for i, row in enumerate(successors) if j in row} for j in range(len(rules))]

    def reachable(seeds, edges):
        seen = set(seeds)
        pending = list(seen)
        while pending:
            for j in edges[pending.pop()] - seen:
                seen.add(j)
                pending.append(j)
        return seen

    starts = {i for i, r in enumerate(rules)
              if len(r.before) != 1 or set(r.before).intersection(higher_targets)}
    ends = {i for i, r in enumerate(rules)
            if len(r.after) != 1 or set(r.after).intersection(higher_sources)}
    forward = reachable(starts.union(protected), successors)
    backward = reachable(ends.union(protected), predecessors)
    return forward & backward


def check_core():
    samples = [Rule('', 'a'), Rule('a', ''), Rule('a', 'ab'), Rule('ba', 'c'),
               Rule('c', 'd'), Rule('d', 'a'), Rule('ab', 'bc'), Rule('x', 'y'), Rule('y', 'yx')]
    for selected in product((False, True), repeat=len(samples)):
        rules = [rule for rule, keep in zip(samples, selected) if keep]
        # Independent fixed point via simultaneous removal of maximal eligible
        # terminal and initial sets. A whole cycle can be eligible at once.
        active = set(range(len(rules)))
        while active:
            removable = set()
            for bits in product((False, True), repeat=len(active)):
                part = {i for i, use in zip(sorted(active), bits) if use}
                outside = active - part
                merge_end = all(len(rules[i].after) == 1 for i in part) and all(
                    set(rules[i].after).isdisjoint(rules[j].before) for i in part for j in outside)
                split_start = all(len(rules[i].before) == 1 for i in part) and all(
                    set(rules[j].after).isdisjoint(rules[i].before) for i in part for j in outside)
                if merge_end or split_start:
                    removable.update(part)
            if not removable:
                break
            active -= removable
        assert active == core(rules)
        paired = []
        for rule, private in zip(rules, 'IJKLMNOPQ'):
            paired.extend((Rule(rule.before, private), Rule(private, rule.after)))
        assert core(paired) == {2 * i + offset for i in active for offset in (0, 1)}
    return 2 ** len(samples)


def check_higher_attachments():
    rules = [Rule('ab', 'c'), Rule('c', 'd'), Rule('d', 'c'),
             Rule('e', 'fg'), Rule('g', 'h'), Rule('h', 'ij')]
    checks = 0
    outcomes = set()
    for used in product((False, True), repeat=len(rules)):
        protected = {i for i, present in enumerate(used) if present}
        for incoming, outgoing in product(('', 'ac', 'dh', 'eg'), repeat=2):
            # Enumerate all terminal sets eligible in the entire graph. Then
            # enumerate all initial sets eligible among the remaining rules.
            active = set(range(len(rules)))
            for terminal in (True, False):
                eligible = set()
                for mask in product((False, True), repeat=len(active)):
                    part = {i for i, marked in zip(sorted(active), mask) if marked}
                    if part & protected:
                        continue
                    for i in part:
                        head = rules[i].after if terminal else rules[i].before
                        occupied = set(incoming if terminal else outgoing)
                        for j in active - part:
                            occupied.update(rules[j].before if terminal else rules[j].after)
                        if len(head) != 1 or head in occupied:
                            break
                    else:
                        eligible.update(part)
                active -= eligible
            assert active == core(rules, protected, incoming, outgoing)
            outcomes.add(frozenset(active))
            checks += 1
    assert len(outcomes) > 8
    return checks, len(outcomes)


# A leaf is its old generator name, a node is (merge rule index, ordered input trees).
def root_name(tree, rules):
    return tree if isinstance(tree, str) else rules[tree[0]].after


def expand(tree):
    if isinstance(tree, str):
        return (tree,)
    return tuple(name for child in tree[1] for name in expand(child))


def read_traces(start, rules, first_merge):
    # A wire remembers its producing box, its port and the incoming wires
    # of that box. Independent orders give the same diagram. Nonempty output
    # at every box makes the final wires sufficient to retain the whole DAG.
    initial = (tuple(start), tuple(range(len(start))))
    pending = [initial]
    seen = {initial}
    result = defaultdict(set)
    while pending:
        trees, wires = pending.pop()
        result[trees].add(wires)
        names = ''.join(root_name(t, rules) for t in trees)
        for i, rule in enumerate(rules):
            for offset in range(len(names) - len(rule.before) + 1):
                if not names.startswith(rule.before, offset):
                    continue
                end = offset + len(rule.before)
                inputs = wires[offset:end]
                if i >= first_merge:
                    out = ((i, trees[offset:end]),)
                else:
                    assert all(isinstance(t, str) for t in trees[offset:end])
                    out = tuple(rule.after)
                produced = tuple((i, inputs, port) for port in range(len(out)))
                next_state = (trees[:offset] + out + trees[end:], wires[:offset] + produced + wires[end:])
                if next_state not in seen:
                    seen.add(next_state)
                    pending.append(next_state)
    return result


def finish(trees, wires):
    # Compose the actual incoming arrows of the fresh targets after an old diagram.
    leaves = iter(wires)

    def visit(tree):
        if isinstance(tree, str):
            return next(leaves)
        rule, children = tree
        return (rule, tuple(visit(t) for t in children), 0)

    answer = tuple(visit(tree) for tree in trees)
    assert next(leaves, None) is None
    return answer


def change_history(wires, position):
    # The two output ports of the direct split at this initial wire are
    # replaced together by the other split followed by its two unary boxes.
    def change(wire):
        if isinstance(wire, int):
            return wire
        rule, inputs, port = wire
        if rule == 0 and inputs == (position,):
            return (2 + port, ((1, inputs, port),), 0)
        return (rule, tuple(change(w) for w in inputs), port)

    return tuple(change(wire) for wire in wires)


def check_mapping_sets():
    base = [Rule('s', 'ab'), Rule('s', 'cd'), Rule('c', 'a'), Rule('d', 'b'), Rule('s', 'mb')]
    rules = base + [Rule('ab', 'm'), Rule('mb', 'n'), Rule('ma', 'n')]
    assert not core(rules)
    targets = histories = many = nested = changes = 0
    for start in ('s', 'ss', 'sb', 'sab', 'abs', 'asm', 'sss'):
        old = read_traces(start, base, len(base))
        lifted = read_traces(start, rules, len(base))
        for target, actual in lifted.items():
            expanded = tuple(name for t in target for name in expand(t))
            predicted = {finish(target, w) for w in old[expanded]}
            assert actual == predicted and len(actual) == len(old[expanded])
            for h in old[expanded]:
                lifted_h = finish(target, h)
                for position, colour in enumerate(start):
                    if colour != 's':
                        continue
                    h1 = change_history(h, position)
                    lifted_h1 = change_history(lifted_h, position)
                    assert lifted_h1 == finish(target, h1)
                    if h1 != h:
                        assert h1 in old[expanded] and lifted_h1 in actual and lifted_h1 != lifted_h
                        assert change_history(lifted_h1, position) == lifted_h1
                        changes += 1
            targets += 1
            histories += len(actual)
            many += len(actual) > 1
            nested += any(isinstance(t, tuple) and any(isinstance(c, tuple) for c in t[1]) for t in target)
    assert many and nested
    assert changes
    return targets, histories, many, nested, changes


def typed_comparison(directory):
    em = Emitter()
    x, y, f = v(0), v(1), v(2)
    edge = arr(STAR, x, y)
    cell = arr(edge, f, f)
    ctx = (STAR, STAR, edge) + (cell,) * 6
    s, a, b, c, d, m = map(v, range(3, 9))
    ab, cd = comp2(ctx, 1, a, b), comp2(ctx, 1, c, d)
    ctx += (arr(cell, s, ab), arr(cell, s, cd), arr(cell, c, a), arr(cell, d, b))
    direct, second, change_c, change_d = map(v, range(9, 13))
    q = comp2(ctx, 2, second, comp2(ctx, 1, change_c, change_d))
    assert direct != q and infer(ctx, direct) == infer(ctx, q)
    original = ctx + (arr(cell, ab, m),)
    private = ctx + (cell, arr(cell, ab, v(13)))
    check_ctx(original)
    check_ctx(private)
    p = comp2(private, 2, q, v(14))
    actual = comp2(original, 2, q, v(13))
    fixed = tuple(map(v, range(len(ctx))))
    fold = fixed + (m, v(13))
    erase = fixed + (ab, identity(ctx, ab))
    assert subst_tm(p, fold) == actual
    padded = subst_tm(p, erase)
    assert padded == comp2(ctx, 2, q, identity(ctx, ab)) and padded != q
    em.check_eq('fold', p, fold, actual)
    em.check_eq('erase', p, erase, padded)
    em.check_type('freshTarget', private, p, arr(cell, s, v(13)))
    em.check_type('foldedTarget', original, actual, arr(cell, s, m))
    em.check_type('erasedTarget', ctx, padded, arr(cell, s, ab))
    point = (STAR,)
    unit = identity(point, v(0))
    scalar_type = arr(infer(point, unit), unit, unit)
    scalars = point + (scalar_type,) * 3
    g, token_a, token_b = map(v, (1, 2, 3))
    empty = identity(scalars, unit)
    double_a = comp2(scalars, 1, token_a, token_a)
    attach = scalars + (arr(scalar_type, empty, double_a),
                        arr(scalar_type, double_a, token_b), arr(scalar_type, token_b, g))
    zero_return = comp2(attach, 2, comp2(attach, 2, v(4), v(5)), v(6))
    em.check_type('scalarReturn', attach, zero_return, arr(scalar_type, empty, g))
    # Add two directed 4-cells on the old alternatives and a directed
    # 5-cell between them. Test whiskering each by the new 3-cell.
    four_type = arr(infer(ctx, direct), direct, q)
    high = ctx + (four_type, four_type, arr(four_type, v(13), v(14)))
    lifted = high + (cell, arr(cell, ab, v(16)))
    folded = high + (arr(cell, ab, m),)
    high_vars = tuple(map(v, range(len(high))))
    for j in (13, 14, 15):
        old_cell = v(j)
        extended = comp2(lifted, 2, old_cell, v(17))
        expected = comp2(folded, 2, old_cell, v(16))
        returned = comp2(high, 2, old_cell, identity(high, ab))
        em.check_eq(f'higherFold{j}', extended, high_vars + (m, v(16)), expected)
        em.check_eq(f'higherReturn{j}', extended, high_vars + (ab, identity(high, ab)), returned)
        old_type = infer(high, old_cell)
        source, target = (comp2(lifted, 2, t, v(17)) for t in old_type[2:])
        em.check_type(f'directed{j}', lifted, extended, arr(infer(lifted, source), source, target))
    disc = tree_ctx(disc_tree(3))
    generic = v(len(disc) - 1)
    gen_padded = comp2(disc, 2, generic, identity(disc, disc[-1][3]))
    for name, lhs, rhs in (('contract', gen_padded, generic), ('extend', generic, gen_padded)):
        comparison = coh_between(disc, disc_tree(3), [generic], lhs, rhs)
        sigma = sub_from(disc, ctx, {len(disc) - 1: q})
        term = subst_tm(comparison, sigma)
        ty = arr(infer(ctx, q), subst_tm(lhs, sigma), subst_tm(rhs, sigma))
        assert infer(ctx, term) == ty
        em.check_type(name, ctx, term, ty)
    # A whisker at the identity has a different literal 1-boundary from
    # the generating disc. Transport both ends before testing the 2-cell.
    two = tree_ctx(disc_tree(2))
    alpha = v(len(two) - 1)
    source, target = two[-1][2:]
    one = tree_ctx(disc_tree(1))
    arrow = v(len(one) - 1)
    left = identity(one, one[-1][2])
    long_arrow = comp2(one, 0, left, arrow)
    enter = coh_between(two, disc_tree(1), [source], arrow, long_arrow)
    leave = coh_between(two, disc_tree(1), [target], long_arrow, arrow)
    moved = comp2(two, 0, identity(two, one[-1][2]), alpha)
    assert infer(two, moved) != two[-1]
    corrected = comp2(two, 1, comp2(two, 1, enter, moved), leave)
    assert infer(two, corrected) == two[-1] and corrected != alpha
    fits = [coh_between(two, disc_tree(2), [alpha], l, r)
            for l, r in ((corrected, alpha), (alpha, corrected))]
    for i, end in enumerate((corrected, alpha)):
        other = (alpha, corrected)[i]
        em.check_type(f'profile{i}', two, fits[i], arr(two[-1], end, other))
        back = comp2(two, 2, fits[i], fits[1 - i])
        unit = identity(two, end)
        cancel = coh_between(two, disc_tree(2), [alpha], back, unit)
        em.check_type(f'cancel{i}', two, cancel, arr(infer(two, unit), back, unit))
    module = 'SplitMergeBoundary'
    (directory / (module + '.agda')).write_text(em.module(module, __doc__))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    print('Dependency graphs:', check_core())
    print('Higher attachment markings, distinct retained sets:', *check_higher_attachments())
    print('Targets, diagrams, targets with alternatives, targets with nested merges, directed changes:',
          *check_mapping_sets())
    if args.agda_dir:
        typed_comparison(args.agda_dir)
