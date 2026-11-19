"""The full five-factor 4-path interval containing the cde triangle and H_R.

edcba sorts to abcde. At the prescribed temporal cut the early events are
de,ce,cd. A late crossing ab can move across cde as a single r. Its binary
factorization exposes the H_R square with the early triangle. Every
cut-compatible upper/lower boundary lies in the checked interval.

K15 acts on raw histories at arbitrary windows. A projected 4-edge keeps its
endpoint classes, family, sorted Gray triangle multiset, ordered spatial
operand event-pairs for i and h, and Response 4 weight. These are invariant
under K15 re-presentation inside an operand, a crossing, and both exterior
contexts. Whisker balancing for i only moves stationary padding. Structural
equations and unit specializations thus project to identities.

For the other 4-equations we use an overapproximation. Every full instance
fits the indicated one/two-edge family pattern (and 18 the one/one pattern),
preserves both exact endpoint classes, Gray chain and weight. A split i
partitions its ordered event pairs. Each correction in 14--17 exchanges the
varying events with the crossing of the added spectators and the stationary
operand. The correcting i in the factorization has precisely the h pairs.
Equation 18 uses the three pairwise crossing blocks on its three factors.
These necessary tests allow more comparisons than the equations require.
A second check uses only the parallel endpoints, total Gray chain, weight
and family shape for 14--18 and the factorization. Its independently saved
score suffices for every cut exchange with a late Gray atom.

For the directed rules, delta has two disjoint chronological windows. In
N_L/R the varying edge is inside one of two disjoint spatial operands.
In U_r/t and H_L a proper zero-Gray variation consists of inner moves. H_R
allows any variation in the right outer factor. The source and target
locations of the varied subhistory are read directly from the defining
faces. The outer occurrence and its variation can be exposed simultaneously:
choose the varying representative first, then the independent operand(s),
the explicit block expansion and exterior histories. K15 in any of those
choices is covered by the vertex and edge projection. We compare transported
edges with the same operands' slot lists and event sets, allowing equivalent
terminal representatives. A composite variation pastes from its constituent
edges, as do disjoint temporal comparisons between paths. A proper shifted
join requires two disjoint positive 4-paths, each needing at least three slots
here. Proper W, K, J have positive Gray top chain and no input globes occur.

The saved additive score is strict on every designated cut delta, equal on
the equation superset and nonincreasing on every directed rule. Whiskering
these comparisons by arbitrary paths preserves their score differences;
pasting the elementary deltas treats all composite late inputs and loops.
"""
from collections import Counter, defaultdict
from functools import cache
from itertools import product

from interchange_path_grading import History, word
from interchange_reachability import Edge, Path, Presentation, Rule, solve, verify
from interchange_sorting_fiber import moves, raw_histories, reachable


START = 'edcba'
NEG = ('de', 'ce', 'cd')
POS = NEG[::-1]
INITIAL = NEG + ('be', 'bd', 'bc', 'ae', 'ad', 'ac', 'ab')
FINAL = POS + ('ab', 'ae', 'ad', 'ac', 'be', 'bd', 'bc')


def closure(start, neighbors):
    pending, seen = [start], {start}
    while pending:
        fresh = set(neighbors(pending.pop())) - seen
        pending.extend(fresh)
        seen.update(fresh)
    return seen


@cache
def interval():
    backward = defaultdict(set)
    for p in raw_histories(START):
        for e in moves(START, p):
            backward[e.target].add(p)
    active = reachable(START, INITIAL) & closure(FINAL, backward.__getitem__)
    cut = [p for p in raw_histories(START) if p[:3] in (NEG, POS)]
    assert len(cut) == 28 and set(cut) <= active
    eq = {}
    at = {}
    for p in sorted(active):
        if p not in eq:
            component = closure(p, lambda q: (e.target for e in moves(START, q) if e.family == 'K15'))
            eq.update((q, min(component)) for q in component)
        at[p] = tuple(e for e in moves(START, p) if e.target in active and e.family != 'K15')
    return eq, at


def pairs(e):
    if e.family not in ('i', 'h'):
        return ()
    return tuple(sorted(product(e.left_events, e.right_events)))


def gray(e):
    if e.family == 'i':
        return ()
    varied, fixed = (e.left_events, e.right) if e.family == 't' else (e.right_events, e.left)
    return tuple(sorted(''.join(sorted(x + y)) for x, y in product(varied, fixed)))


def weight(e):
    if e.family == 'i':
        return len(pairs(e))
    if e.family == 't':
        varying, events, stationary, sign = e.left, e.left_events, e.right, -1
    else:
        varying, events, stationary, sign = e.right, e.right_events, e.left, 1
    history = History(word(varying), tuple(tuple(event[::-1]) for event in events))
    return len(stationary) * (40 * history.mass + sign * history.moment) - len(pairs(e))


def signature(e):
    return e.family, gray(e), pairs(e), weight(e)


def operand(e):
    return (e.family, e.left, e.right, frozenset(e.left_events), frozenset(e.right_events))


def inner_laws(outer):
    """Source/target offsets of the varied operand and order on the source route."""
    nl, nr = len(outer.left_events), len(outer.right_events)
    n = outer.hi - outer.lo
    if outer.family == 'i':
        yield 'N_L', nr, 0, nl, False
        yield 'N_R', 0, nl, nr, True
    elif outer.family == 'r':
        yield 'U_r', n - nr, 0, nr, False
    elif outer.family == 't':
        yield 'U_t', 0, n - nl, nl, True
    elif outer.family == 'h':
        yield 'H_L', n - nr, 0, nr, False
        yield 'H_R', 0, nr, nl, True


def whisker_correction(name, single, mixed, inner_pairs):
    """The correction in 14--17 exchanges the variation with the added crossings."""
    if name in ('14', '15'):
        stationary = set(single.left)
        if stationary != set(mixed.left) or set(single.right_events) != set(mixed.right_events):
            return False
        varied = single.right_events
        narrow, wide = set(mixed.right), set(single.right)
    else:
        stationary = set(single.right)
        if stationary != set(mixed.right) or set(single.left_events) != set(mixed.left_events):
            return False
        varied = single.left_events
        narrow, wide = set(mixed.left), set(single.left)
    if name in ('15', '16'):
        narrow, wide = wide, narrow
    if not narrow < wide:
        return False
    crossed = tuple(''.join(sorted((a, b))) for a, b in product(stationary, wide - narrow))
    pairs = product(varied, crossed) if name in ('14', '16') else product(crossed, varied)
    return tuple(sorted(pairs)) == inner_pairs


def three_blocks(r, t):
    a, d = set(t.right), set(r.left)
    b = set(r.right) - a
    if not b or set(r.right) != a | b or set(t.left) != d | b:
        return False

    def cart(x, y):
        return {''.join(sorted(pair)) for pair in product(x, y)}
    return set(r.right_events) == cart(b, a) and set(t.left_events) == cart(d, b)


@cache
def ground(loose=False):
    classes, at = interval()
    keys = {e: (classes[e.source], classes[e.target], signature(e))
            for group in at.values() for e in group}
    names = {k: str(i) for i, k in enumerate(sorted(set(keys.values())))}
    label = {e: names[k] for e, k in keys.items()}
    edges = {n: Edge(k[0], k[1], k[2][-1]) for k, n in names.items()}
    signatures = {n: k[2] for k, n in names.items()}
    representatives = defaultdict(set)
    for e, n in label.items():
        representatives[n].add(e)
    rules = set()

    def record(family, eq, left, right):
        p = Path(edges[left[0]].source, left)
        q = Path(edges[right[0]].source, right)
        if p != q:
            rules.add((family, eq, p, q))

    # Compare parallel short paths against a superset of the degree-four
    # equations. All genuine instances have the displayed family shape, the
    # same Gray top chain and Response 4 weight, and exact class endpoints.
    by_boundary = defaultdict(list)
    outgoing = defaultdict(list)
    for n, e in edges.items():
        outgoing[e.source].append(n)
        by_boundary[e.source, e.target, signatures[n][1], e.weight].append(n)
    for n, e in edges.items():
        for m in outgoing[e.target]:
            f = edges[m]
            g = tuple(sorted(signatures[n][1] + signatures[m][1]))
            singles = by_boundary[e.source, f.target, g, e.weight + f.weight]
            kinds = signatures[n][0] + signatures[m][0]
            for single in singles:
                k = signatures[single][0]
                relation = {('r', 'rr'): '10/12', ('t', 'tt'): '11/13', ('r', 'ir'): '14',
                            ('r', 'ri'): '15', ('t', 'it'): '16', ('t', 'ti'): '17',
                            ('i', 'ii'): '20/21', ('r', 'hi'): 'factor'}.get((k, kinds))
                if relation:
                    if k == 'i' and sorted(signatures[n][2] + signatures[m][2]) != list(signatures[single][2]):
                        continue
                    if not loose and relation in ('14', '15', '16', '17'):
                        mixed, inner = (m, n) if kinds.startswith('i') else (n, m)
                        if not any(whisker_correction(relation, a, b, signatures[inner][2])
                                   for a, b in product(representatives[single], representatives[mixed])):
                            continue
                    if not loose and relation == 'factor' and signatures[n][2] != signatures[m][2]:
                        continue
                    record(relation, True, (single,), (n, m))
        if signatures[n][0] == 'r':
            for m in by_boundary[e.source, e.target, signatures[n][1], e.weight]:
                if signatures[m][0] == 't' and (loose or any(
                        three_blocks(a, b) for a, b in product(representatives[n], representatives[m]))):
                    record('18', True, (n,), (m,))
    # Transport the actual raw varying occurrence. The two resulting endpoint
    # representatives may differ by a K15 rewrite inside the block crossing.
    for p, group in at.items():
        for outer in group:
            variations = list(inner_laws(outer))
            for inner in group:
                if inner.hi <= outer.lo:
                    # inner is earlier in time, hence it acts second on the source route.
                    patterns = [('delta', 0, False)]
                else:
                    patterns = [(name, new - old, inner_first)
                                for name, old, new, width, inner_first in variations
                                if outer.lo + old <= inner.lo and inner.hi <= outer.lo + old + width
                                if name not in ('U_r', 'U_t', 'H_L') or not gray(inner)]
                for name, shift, inner_first in patterns:
                    after_inner = [e for e in at[inner.target] if e.lo == outer.lo and
                                   e.hi == outer.hi and operand(e) == operand(outer)]
                    after_outer = [e for e in at[outer.target] if e.lo == inner.lo + shift and
                                   e.hi == inner.hi + shift and operand(e) == operand(inner)]
                    for a, b in product(after_inner, after_outer):
                        if classes[a.target] == classes[b.target]:
                            x = (label[inner], label[a])
                            y = (label[outer], label[b])
                            source, target = (x, y) if inner_first else (y, x)
                            record(name, False, source, target)
    graph = Presentation(set(classes.values()), edges,
        (Rule(f'{family} {p.edges} {q.edges}', p, q, eq) for family, eq, p, q in sorted(rules)))
    return graph, label


def cut_deltas(graph, label):
    """All exact delta squares between the early triangle and one late edge."""
    classes, at = interval()
    result = set()
    for raw, group in at.items():
        if raw[:3] != NEG:
            continue
        for early, late in product(group, repeat=2):
            if (early.lo, early.hi) != (0, 3) or late.lo < 3:
                continue
            assert gray(early) == ('cde',)
            end = POS + late.target[3:]

            def transport(edge, after):
                projected = {label[f] for f in at[after]
                             if f.target == end and (f.lo, f.hi) == (edge.lo, edge.hi)
                             and operand(f) == operand(edge)}
                only, = projected
                return only

            a = Path(classes[raw], (label[late], transport(early, late.target)))
            b = Path(classes[raw], (label[early], transport(late, early.target)))
            assert any(step.rule.startswith('delta ') and target == b
                       for step, target in graph.successors(a))
            result.add((a, b))
    return result


def native_example(graph, labels):
    """Read the actual delta and H_R schemas on five consecutive 2-globes."""
    from check_two_moving_native import Evaluator, Route, Value
    from interchange_sorting_fiber import _join_faces, _raw, native_generators
    from reachability_theory import Block, Cell, EQUATIONS, OPERATIONS, RULES, chi, r, word as join_words
    from response12_degree_five import EXTRA_RULES

    class FiveSlots(Evaluator):
        @cache
        def apply(self, name, args):
            if name != 'h':
                return super().apply(name, args)
            op = OPERATIONS[name]
            env = dict(zip(('x0', 'x1'), args))
            assert all(self.read(l, env) == self.read(r, env) for l, r in op.guards)
            s, t = (self.read(side, env) for side in (op.source, op.target))
            first, last = _join_faces(*(v.trace for v in args))
            assert (first, last) == (s.trace, t.trace)
            return Value(4, s, t, Route((first, last), ('h',)))

    evaluate = FiveSlots()
    evaluate.generators = native_generators(START[::-1])

    a, b, c, d, e = (Block.var(Cell(2, f'{i}/0/0'), i) for i in range(5))
    A = chi(a, b)
    Y = r(chi(c, d), e)
    early = join_words(Y, join_words(b, a))
    late = r(A, join_words(join_words(c, d), e))

    classes, at = interval()
    def read_route(expr, env):
        route = evaluate.read(expr, env).trace
        raw = tuple(_raw(v) for v in route.states)
        path = []
        for p, q, family in zip(raw, raw[1:], route.labels):
            kind = 'i' if family == 'iota' else family
            possible = {labels[u] for u in at[p] if u.target == q and u.family == kind}
            assert len(possible) == 1
            path.append(possible.pop())
        return Path(classes[raw[0]], tuple(path))

    examples = {}
    for name, schemas, blocks in (('delta', RULES, (early, late)), ('H_R', EXTRA_RULES, (A, Y))):
        schema = next(s for s in schemas if s.name == name)
        env = {v: evaluate.read(block.cell.term) for (v, _), block in zip(schema.variables, blocks)}
        assert all(evaluate.read(l, env) == evaluate.read(r, env) for l, r in schema.guards)
        p, q = (read_route(side, env) for side in (schema.left, schema.right))
        assert p.start == classes[INITIAL]
        assert any(step.rule.startswith(name + ' ') and target == q for step, target in graph.successors(p))
        examples[name] = p, q
    factor = next(s for s in EQUATIONS if s.name == 'binary join factorization')
    env = {v: evaluate.read(block.cell.term)
           for (v, _), block in zip(factor.variables, (A, Y.face(True)))}
    assert all(evaluate.read(l, env) == evaluate.read(r, env) for l, r in factor.guards)
    single, expanded = (read_route(side, env) for side in (factor.left, factor.right))
    start = examples['delta'][1]
    before, after = examples['H_R']
    assert start.edges[1:] == single.edges and graph.edges[start.edges[0]].target == single.start
    exposed = Path(start.start, start.edges[:1] + expanded.edges)
    assert exposed.edges[:2] == before.edges
    assert any(step.rule.startswith('factor ') and target == exposed
               for step, target in graph.successors(start))
    moved = Path(start.start, after.edges + expanded.edges[1:])
    assert any(step.rule.startswith('H_R ') and target == moved
               for step, target in graph.successors(exposed))
    examples['exposed_H_R'] = exposed, moved
    return examples


# Integer scores of primitive projected edges, in numerical name order.
SCORES = (
    -5, -10, -10, -5, -10, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, -5,
    -10, -10, -5, -5, 0, 0, 5, 0, 0, 5, 0, 5, 5, 5, 5, 5, 5, -10,
    -10, -10, -10, 0, 5, 5, 5, 5, 5, -5, 0, 5, 5, -5, 5, 5, -8, -16,
    -10, -8, -16, -10, 0, 0, 0, 0, 0, -8, -16, -10, -8, -16, -10, 0, 0, 0,
    -8, -16, -16, -8, -16, -16, 0, 0, 0, 0, 0, -8, -16, -16, -8, 0, 0, 0,
    -16, 0, 8, 0, -8, -8, 0, 0, 0, 0, 0, 0, 16, 0, 0, 16, 8, 0,
    -8, -16, -16, -8, 0, 0, 0, -16, -5, -10, -10, -5, -5, 0, 0, 5, 0, 0,
    5, 0, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, -5, 0, 5, 5, -5, 0,
    -5, -5, 5, 0, 0, 5, 5, 0, 0, -10, 0, 0, -10, 0, 0, 0, -5, 5,
    0, -5, 5, 5, -5, -10, -10, -5, 0, 0, 0, -10, 0, 0, -5, 0, 0, 0,
    -5, 0, 0, 0, 0, 0, -5, 0, 0, 0, 9, -1, -1, 9, 5, 5, 5, 5,
    0, -5, -5, -10, -10, 10, 5, 0, 5, 5, -5, 15, 20, 15, 10, 0, 0, -10,
    -10, 0, 5, 5, 5, 5, 5, 0, 10, 5, 0, -5, -10, -10, -10, -5, -5, -10,
    -10, 15, 0, 0, 0, 0, 5, 5, 15, 25, 15, 0, -5, 0, -1, -5, -10, 5,
    5, 0, -10, -10, -5, -10, 5, 5, 0, 5, 0, -5, 0, 3, -7, 3, 0, -10,
    -10, 13, 13, -5, -10, -10, -5, 0, 0, 0, 0, -10, 0, 0, -10, -10, -15, -20,
    -10, -5,
)


# A second rank for the broader equation test, strict on all mixed late edges.
LOOSE_SCORES = (
    3, 6, 6, 3, -3, -3, 0, 0, 0, 9, 0, 0, 0, 0, 3, 6, 0, 3,
    6, 6, 9, 3, 6, 3, 6, 0, 0, 3, 0, 6, 6, 6, 6, 6, 6, -3,
    0, -3, 6, 3, 6, 6, 6, 6, 6, 9, 6, 6, 3, 3, 6, 6, -2, 6,
    6, -2, -3, -3, 0, 0, 9, 0, 0, -2, -4, -4, -2, -13, -13, 0, 9, 0,
    -2, -4, -4, -2, -13, -13, 9, 0, 0, 0, 0, -2, -4, -13, -2, 0, 0, 0,
    -4, 0, 2, 0, -2, -2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 4, 2, 0,
    -2, -4, -4, -2, 0, 0, 0, -4, 0, 0, 0, -4, 0, -4, 0, -4, 0, 0,
    -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, -4, -4, -4, 0, 0,
    0, -4, -4, -4, 0, -4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, -4,
    -4, 0, -4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0,
    3, 0, 0, 0, 0, 0, -2, 0, 0, 0, 5, 3, 1, 5, 6, 6, 6, 6,
    4, -2, -4, -4, -2, 10, 8, 0, 6, 6, 2, 10, 12, 10, 8, 0, 0, -2,
    -4, 0, 6, 6, 6, 6, 6, 0, 4, 2, 0, -2, -4, -4, -6, -2, -4, -4,
    -2, 12, 0, 0, 0, -2, 6, 6, 10, 14, 10, 0, -2, 0, 1, -4, -4, 6,
    6, 4, -4, -6, -4, -4, 6, 6, 0, 2, 0, -2, -2, 0, -2, 0, 0, -4,
    -2, 9, 9, -2, -4, -4, -2, -4, -4, 0, 0, 0, 0, 0, -4, -4, -6, -8,
    -8, -2,
)


def check_loose(synthesize):
    from interchange_regular_rectangles import Rank, find_rank, verify_rank

    graph, label = ground(loose=True)
    gray_edges = {n for e, n in label.items() if gray(e)}
    pairs = [(p, q) for p, q in cut_deltas(graph, label) if p.edges[0] in gray_edges]
    assert len(pairs) == 44 and len(LOOSE_SCORES) == len(graph.edges)
    rank = Rank({}, {e: int(e) for e in graph.edges}, dict(enumerate(LOOSE_SCORES)))
    assert verify_rank(graph, pairs, rank)
    drops = [rank.evaluate(p)[1] - rank.evaluate(q)[1] for p, q in pairs]
    eqs = sum(rule.equation for rule in graph.rules.values())
    print(f'Broader check with {eqs} equation comparisons: all {len(pairs)} mixed-late '
          f'exchanges strict, drops {min(drops)} to {max(drops)}.')
    if synthesize:
        fresh = find_rank(graph, sorted(pairs))
        assert fresh is not None and verify_rank(graph, pairs, fresh)


def check(synthesize=False):
    from interchange_regular_rectangles import Rank, find_rank, verify_rank

    graph, label = ground()
    pairs = cut_deltas(graph, label)
    assert len(pairs) == 76
    assert sorted(map(int, graph.edges)) == list(range(len(SCORES)))
    rank = Rank({}, {e: int(e) for e in graph.edges}, dict(enumerate(SCORES)))
    assert verify_rank(graph, pairs, rank)
    drops = [rank.evaluate(p)[1] - rank.evaluate(q)[1] for p, q in pairs]
    examples = native_example(graph, label)
    p, q = examples['delta']
    assert (p, q) in pairs
    forward, reverse = solve(graph, p, q), solve(graph, q, p)
    assert forward.reachable and len(forward.steps) == 1 and verify(graph, p, q, forward)
    assert not reverse.reachable and verify(graph, q, p, reverse)
    assert set(examples['exposed_H_R']) <= set(reverse.visited)
    gray_labels = {n for e, n in label.items() if gray(e)}
    gray_pairs = sum(p.edges[0] in gray_labels for p, q in pairs)
    assert gray_pairs == 44
    counts = Counter(rule.name.split()[0] for rule in graph.rules.values())
    print(f'{len(interval()[0])} raw histories, {len(graph.vertices)} classes, '
          f'{len(graph.edges)} projected 4-edges. Comparison counts: {dict(sorted(counts.items()))}')
    print(f'{len(pairs)} strict cut exchanges ({gray_pairs} with a late triangle), '
          f'integer drops {min(drops)} to {max(drops)}.')
    print(f'Native delta, factorization and H_R replayed inside the cut. The reverse cut for the delta has '
          f'{len(reverse.visited)} paths.')
    if synthesize:
        fresh = find_rank(graph, sorted(pairs))
        assert fresh is not None and verify_rank(graph, pairs, fresh)
    check_loose(synthesize)


if __name__ == '__main__':
    from argparse import ArgumentParser

    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--synthesize', action='store_true')
    check(parser.parse_args().synthesize)
