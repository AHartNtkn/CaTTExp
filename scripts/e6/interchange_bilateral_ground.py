"""Response 12 on zwxy -> xyzw with two marked input advances.

Rows x,y and columns z,w stay in their respective branch orders. The two
linear extensions of the four crossings are pqrs and prqs. A contiguous full
rectangle has both K15 presentations, and every proper rectangle has just one.
Consequently hist gives the entire contextual degree-three quotient here.

A primitive mixed operation has a rectangular crossing between contiguous
row and column words, with its unary histories on those words. The rectangle
remembers stationary slots of the input as well as active slots. The spatial
gap in an inner crossing can be assigned to either operand by balancing.
We identify occurrences by endpoints, kind, weight and atomic event labels,
all invariant under changing a K15 representative. Thus every typed path
projects to a path. Negative closed cuts in this presentation lift to
nonreachability. Positive witnesses need a typed construction.

The grounded equations include both stationary and varying splits of these
words, the two allowed inner splits and the binary join factorization. The
directed boundaries include W, delta, inner naturality and the whole paths
of the proper shifted join. Composite delta and naturality inputs paste
from their single-edge instances. A K15 change in either temporal window
of delta is independent of the other. The spatially disjoint positive
operands of inner naturality and shifted join cannot contain a full K15
rectangle. With one advance on each branch there are no nonidentity branch
4-variations, so the remaining Response 12 rules specialize to identities
or the included W. With two advances on one branch, a branch variation can
also specialize to U_r or U_t. There is no third branch or input 4-globe.
"""
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, product

from interchange_four_slot_ground import BLOCKS, CROSSES, hist
from interchange_path_grading import History, word
from interchange_reachability import Edge, Path, Presentation, Rule
from interchange_response12_rectangles import shifted_joins
from interchange_two_moving import Move
from reachability_theory import OPERATIONS


EVENTS = {**{k: tuple(v) for k, v in CROSSES.items()},
          **{s.upper(): (s,) for s in 'xyzw'}}
LETTER = {v: k for k, v in EVENTS.items()}


@cache
def slots(events):
    return frozenset(s for e in events for s in EVENTS[e])


# The rows are read in spatial order x,y and the columns in spatial order z,w.
SHAPE = {block: tuple(''.join(s for s in branch if s in slots(block))
                      for branch in ('xy', 'zw')) for block in BLOCKS}


@cache
def raw_histories(left, right):
    if left not in ('X', 'Y', 'Z', 'W') or right not in ('X', 'Y', 'Z', 'W'):
        raise ValueError('supply two unary letters from X,Y,Z,W')
    return tuple(sorted({order[:i] + a + order[i:j] + b + order[j:]
                         for order in ('pqrs', 'prqs')
                         for i in range(5) for j in range(i, 5)
                         for a, b in ((left, right), (right, left))}))


@cache
def state_at(prefix):
    return History(word('zwxy'), tuple(EVENTS[e] for e in prefix)).end


def advances(events, branch):
    return bool(events) and all(e in branch.upper() for e in events)


@cache
def primitive_moves(raw):
    result = []
    for lo, mid, hi in combinations(range(len(raw) + 1), 3):
        first, second = raw[lo:mid], raw[mid:hi]
        order = [s for s, _ in state_at(raw[:lo])]
        if max(map(order.index, slots(second))) < min(map(order.index, slots(first))):
            result.append(Move('i', lo, mid, hi))
        if first in SHAPE and advances(second, SHAPE[first][0]):
            result.append(Move('r', lo, mid, hi))
        if second in SHAPE and advances(first, SHAPE[second][1]):
            result.append(Move('t', lo, mid, hi))
        # h(B chi A) = A B chi, with exactly two advances available.
        block = first[1:]
        if (block in SHAPE and advances(first[0], SHAPE[block][1])
                and advances(second, SHAPE[block][0])):
            result.append(Move('h', lo, mid, hi))
    return tuple(result)


def weight(raw, move):
    first, second = raw[move.lo:move.mid], raw[move.mid:move.hi]
    if move.kind == 'i':
        return len(first) * len(second)
    if move.kind == 't':
        rows, cols = SHAPE[second]
        moment = sum(len(cols) - 1 - 2 * cols.index(e.lower()) for e in first)
        return len(rows) * (11 * len(first) - moment)
    block = first if move.kind == 'r' else first[1:]
    rows, cols = SHAPE[block]
    moment = sum(len(rows) - 1 - 2 * rows.index(e.lower()) for e in second)
    return len(cols) * (11 * len(second) + moment) - int(move.kind == 'h')


@cache
def edge_key(raw, move):
    first, second = raw[move.lo:move.mid], raw[move.mid:move.hi]
    if move.kind == 'i':
        atoms = sorted(a + b for a, b in product(first, second))
    elif move.kind == 't':
        atoms = sorted(b + row for b, row in product(first, SHAPE[second][0]))
    else:
        block = first if move.kind == 'r' else first[1:]
        atoms = sorted(a + col for a, col in product(second, SHAPE[block][1]))
        if move.kind == 'h':
            atoms.append(first[0] + second)
    return f'{hist(raw)}/{hist(move.target(raw))}/{weight(raw, move)}/{move.kind}:{".".join(atoms)}'


def walk(raw, sequence):
    names, state = [], raw
    for move in sequence:
        assert move in primitive_moves(state), (state, move)
        names.append(edge_key(state, move))
        state = move.target(state)
    return Path(hist(raw), tuple(names))


def split_laws(raw, move):
    lo, mid, hi = move.lo, move.mid, move.hi
    first, second = raw[lo:mid], raw[mid:hi]

    def split_second(cut, first_kind, second_kind):
        return (Move(first_kind, lo, mid, cut), Move(second_kind, lo + cut - mid, cut, hi))

    def split_first(cut, first_kind, second_kind):
        return (Move(first_kind, cut, mid, hi), Move(second_kind, lo, cut, cut + hi - mid))

    if move.kind == 'h':
        # r_1 = h ; iota(B,A). W : t_0 ; iota(A,B) ; r_0 -> h ; t_1.
        r1 = Move('r', lo + 1, mid, hi)
        minus = Move('i', lo, lo + 1, lo + 2)
        yield 'binary_join_factorization', (r1,), (move, minus)
        t0 = Move('t', lo, lo + 1, mid)
        plus = Move('i', mid - 1, mid, hi)
        r0 = Move('r', lo, mid - 1, mid)
        t1 = Move('t', lo + 1, lo + 2, hi)
        yield 'W', (t0, plus, r0), (move, t1)
        return

    for cut in range(mid + 1, hi):
        a, b = raw[mid:cut], raw[cut:hi]
        if move.kind == 'r' or (move.kind == 'i' and first in SHAPE):
            yield '10' if move.kind == 'r' else '20', (move,), split_second(cut, move.kind, move.kind)
        if move.kind == 't' and a in SHAPE and b in SHAPE:
            ra, ca = SHAPE[a]
            rb, cb = SHAPE[b]
            rows, cols = SHAPE[second]
            if ra + rb == rows and ca == cb:
                yield '13', (move,), split_second(cut, 't', 't')
            if ra == rb and cb + ca == cols and advances(first, ca):
                yield '17', (move,), split_second(cut, 't', 'i')

    for cut in range(lo + 1, mid):
        a, b = raw[lo:cut], raw[cut:mid]
        if move.kind == 't' or (move.kind == 'i' and second in SHAPE):
            yield '11' if move.kind == 't' else '21', (move,), split_first(cut, move.kind, move.kind)
        if move.kind == 'r' and a in SHAPE and b in SHAPE:
            ra, ca = SHAPE[a]
            rb, cb = SHAPE[b]
            rows, cols = SHAPE[first]
            if ra == rb and cb + ca == cols:
                yield '12', (move,), split_first(cut, 'r', 'r')
            if ra + rb == rows and ca == cb:
                if advances(second, ra):
                    yield '14', (move,), split_first(cut, 'i', 'r')
                if advances(second, rb):
                    yield '15', (move, Move('i', lo, lo + hi - mid, cut + hi - mid)), (
                        Move('r', cut, mid, hi),)

    if move.kind == 't':
        # (16) starts with the near-column crossings *before* B on the
        # far columns. Its left hand side exposes the full t after an iota.
        for start in range(lo):
            a = raw[start:lo]
            if a + second in SHAPE and a in SHAPE:
                ra, ca = SHAPE[a]
                rb, cb = SHAPE[second]
                if ra == rb and SHAPE[a + second][1] == cb + ca:
                    yield '16', (Move('i', start, lo, mid),
                                 Move('t', start, start + mid - lo, hi)), (move,)


def laws(raw):
    active = primitive_moves(raw)
    for outer in active:
        yield from split_laws(raw, outer)
        for inner in active:
            if outer.hi <= inner.lo:
                yield 'delta', (inner, outer), (outer, inner)
            if outer.kind in ('i', 'r') and outer.mid <= inner.lo and inner.hi <= outer.hi:
                yield 'N_L' if outer.kind == 'i' else 'U_r', (
                    outer, inner.shift(outer.lo - outer.mid)), (inner, outer)
            if outer.kind in ('i', 't') and outer.lo <= inner.lo and inner.hi <= outer.mid:
                yield 'N_R' if outer.kind == 'i' else 'U_t', (inner, outer), (
                    outer, inner.shift(outer.hi - outer.mid))
    for lhs, rhs in shifted_joins(raw, primitive_moves):
        yield 'shifted_join', lhs, rhs


@cache
def metadata(left, right):
    occurrences = defaultdict(set)
    for raw in raw_histories(left, right):
        for move in primitive_moves(raw):
            occurrences[edge_key(raw, move)].add((raw, move))
    return {key: frozenset(value) for key, value in occurrences.items()}


@cache
def ground_all(left, right):
    edges, rules = {}, {}
    histories = raw_histories(left, right)
    for key, instances in metadata(left, right).items():
        raw, move = min(instances)
        edges[key] = Edge(hist(raw), hist(move.target(raw)), weight(raw, move))
    for raw in histories:
        for law, lhs, rhs in laws(raw):
            source, target = walk(raw, lhs), walk(raw, rhs)
            name = f'{law} {source.edges} {target.edges}'
            rules[name] = Rule(name, source, target, law.isdecimal() or law == 'binary_join_factorization')
    return Presentation({hist(raw) for raw in histories}, edges, rules.values())


@cache
def native_one(branches, before):
    """The actual 1-cell at a cut of the 2-word (one stage per branch)."""
    from check_two_moving_native import Value

    def obj(i):
        return Value(0, None, None, str(i))

    stages = tuple((branch, sum(s in ('xy', 'zw')[branch] for s, _ in before))
                   for branch in branches)
    return Value(1, obj(branches[0]), obj(branches[-1] + 1), stages)


def native_operand(state, lo, hi, branches, events=None):
    from check_two_moving_native import Value

    source, target = native_one(branches, state[:lo]), native_one(branches, state[:hi])
    start = Value(2, source, target, state[lo:hi])
    if events is None:
        return start
    history = History(start.trace, tuple(EVENTS[e] for e in events))
    return Value(3, start, Value(2, source, target, history.end), history)


def verify_faces(raw, move):
    """Evaluate the two native P boundary terms, with full globular guards."""
    prefix, first, second, suffix = (raw[:move.lo], raw[move.lo:move.mid],
                                     raw[move.mid:move.hi], raw[move.hi:])
    state = state_at(prefix)
    order = [s for s, _ in state]
    if move.kind == 'i':
        lo = min(map(order.index, slots(second)))
        mid, hi = min(map(order.index, slots(first))), max(map(order.index, slots(first))) + 1
        args = (native_operand(state, lo, mid, (0, 1), second),
                native_operand(state, mid, hi, (0, 1), first))
    else:
        block = {'r': first, 't': second, 'h': first[1:]}[move.kind]
        rows, cols = SHAPE[block]
        lo = order.index(cols[0])
        mid, hi = lo + len(cols), lo + len(cols) + len(rows)
        assert ''.join(order[lo:hi]) == cols + rows
        a = second if move.kind in ('r', 'h') else None
        b = {'r': None, 't': first, 'h': first[:1]}[move.kind]
        args = (native_operand(state, mid, hi, (0,), a), native_operand(state, lo, mid, (1,), b))
    op = OPERATIONS['iota' if move.kind == 'i' else move.kind]
    evaluate = native_evaluator().read
    env = dict(zip(('x0', 'x1'), args))
    assert all(evaluate(a, env) == evaluate(b, env) for a, b in op.guards)
    for term, expected in zip((op.source, op.target), (raw, move.target(raw))):
        face = evaluate(term, env).trace.pad(state[:lo], state[hi:])
        assert face.start == state and face.end == state_at(expected[:move.hi])
        decoded = ''.join(LETTER[e] for e in face.events)
        assert hist(prefix + decoded + suffix) == hist(expected)


@cache
def native_evaluator():
    from check_two_moving_native import Evaluator
    return Evaluator()


def check():
    from itertools import combinations_with_replacement

    totals = Counter()
    for a, b in combinations_with_replacement('XYZW', 2):
        graph = ground_all(a, b)
        for raw in raw_histories(a, b):
            assert state_at(raw) == tuple((s, (a+b).count(s.upper())) for s in 'xyzw')
            for move in primitive_moves(raw):
                verify_faces(raw, move)
                totals[move.kind] += 1
        laws_seen = Counter(name.split()[0] for name in graph.rules)
        assert laws_seen['W'] == laws_seen['binary_join_factorization']
        for rule in graph.rules.values():
            drop = graph.weight(rule.source) - graph.weight(rule.target)
            assert drop == (2 if rule.name.startswith('W ') else 0)
        print(f'{a}{b}: {len(graph.vertices)} classes, {len(graph.edges)} edges, '
              f'{len(graph.rules)} rules, {laws_seen["W"]} W, {laws_seen["shifted_join"]} shifted joins.')
    print('Native primitive faces checked for', dict(totals))


if __name__ == '__main__':
    check()
