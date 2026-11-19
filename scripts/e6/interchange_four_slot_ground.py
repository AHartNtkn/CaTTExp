"""Ground the support-free presentation P on the two-by-two crossing interval.

The left slots x,y have m,n ordered advances (X,Y respectively), and
the right slots z,w are stationary. The default is m=n=1. The initial 2-word is zwxy. The crossings p=wx, q=zx, r=wy,
s=zy have the two orders pqrs and prqs. Equation (K15) identifies these
orders when the whole block is contiguous. Smaller rectangular blocks
have only one order. Thus hist gives the exact degree-three classes.

At degree four we identify any primitive occurrences with the same two
history classes, weight and mixed atoms. This gives a sound quotient
for disproving reachability. The grounding retains composites as inputs,
including every rectangle in an r and every pair of disjoint spatial
histories in an iota. e.g. r against both z,w can have both orders of
the full crossing. Equations (10),(12),(14),(15),(20),(21) below enumerate
their positive instances. Every possible stationary or varying split is
a split of one of the two-element slot lists or the chronological unary
history. We use the block order exposing that split; the other direct
representative has the same edge key. Spatial and temporal whisker
equations preserve keys. In particular the key is invariant under K15
re-presentation of an operand or exterior prefix/suffix.

The right outer branch has no positive 3-history, so proper h,W,t,U_t
are absent. There are no higher input globes or third outer factor.
delta, N_L, N_R, U_r generate the remaining 5-steps. Splitting a
composite 4-variation or either input of delta into successive edges
gives a paste with the designated boundary. Disjoint temporal windows
in delta admit independently chosen raw representatives; in an N the
two spatial operands are disjoint, so neither can contain the full K15
block. In U_r the varying 4-input belongs to the left branch. Thus all
required raw instances occur. The search includes arbitrary chronological
4-prefix/suffix contexts. A closed cut containing the target of the comparison and excluding its
source proves absence of a reverse in P. A positive computation needs a typed lift, supplied
by the displayed temporal comparison when testing a rectangle.
"""

from collections import Counter
from functools import cache
from itertools import combinations

from interchange_path_grading import History, i_faces, r_faces, word
from interchange_reachability import Edge, Path, Presentation, Rule, solve, verify
from interchange_two_moving import Move


CROSSES = {'p': 'wx', 'q': 'zx', 'r': 'wy', 's': 'zy'}
EVENTS = {**{e: tuple(pair) for e, pair in CROSSES.items()}, 'X': ('x',), 'Y': ('y',)}
BLOCKS = frozenset(('p', 'q', 'r', 's', 'pq', 'rs', 'pr', 'qs', 'pqrs', 'prqs'))


@cache
def raw_histories(m=1, n=1):
    length = m + n + 4
    histories = []
    for crossing_positions in combinations(range(length), 4):
        remaining = [i for i in range(length) if i not in crossing_positions]
        for x_positions in combinations(remaining, m):
            for order in ('pqrs', 'prqs'):
                raw = ['Y'] * length
                for i in x_positions:
                    raw[i] = 'X'
                for i, event in zip(crossing_positions, order):
                    raw[i] = event
                histories.append(''.join(raw))
    return tuple(histories)


def hist(raw):
    return raw.replace('prqs', 'pqrs')


@cache
def slots(events):
    return frozenset(''.join(s for e in events for s in EVENTS[e]))


@cache
def state_at(prefix):
    return History(word('zwxy'), tuple(EVENTS[e] for e in prefix)).end


@cache
def primitive_moves(raw):
    result = []
    for lo, mid, hi in combinations(range(len(raw) + 1), 3):
        first, second = raw[lo:mid], raw[mid:hi]
        if (first in BLOCKS and all(e in 'XY' for e in second)
                and slots(second) <= slots(first)):
            result.append(Move('r', lo, mid, hi))
        order = [s for s, _ in state_at(raw[:lo])]
        if max(order.index(s) for s in slots(second)) < min(order.index(s) for s in slots(first)):
            result.append(Move('i', lo, mid, hi))
    return tuple(result)


def weight(raw, move):
    first, second = raw[move.lo:move.mid], raw[move.mid:move.hi]
    if move.kind == 'i':
        return len(first) * len(second)
    left = slots(first) & {'x', 'y'}
    right = slots(first) & {'z', 'w'}
    moment = second.count('X') - second.count('Y') if len(left) == 2 else 0
    return len(right) * (11 * len(second) + moment)


def edge_key(raw, move):
    first, second = raw[move.lo:move.mid], raw[move.mid:move.hi]
    atoms = ''.join(e + z for e in sorted(second) for z in sorted(slots(first) & {'z', 'w'})) \
        if move.kind == 'r' else 'i'
    return f'{hist(raw)}/{hist(move.target(raw))}/{weight(raw, move)}/{atoms}'


def walk(raw, sequence):
    names = []
    state = raw
    for move in sequence:
        assert move in primitive_moves(state), (state, move)
        names.append(edge_key(state, move))
        state = move.target(state)
    return Path(hist(raw), tuple(names))


def split_laws(raw, m):
    lo, mid, hi = m.lo, m.mid, m.hi
    first, second = raw[lo:mid], raw[mid:hi]
    if m.kind == 'r' or first in BLOCKS:
        for cut in range(mid+1, hi):
            yield '10' if m.kind == 'r' else '20', (m,), (
                Move(m.kind, lo, mid, cut), Move(m.kind, lo + cut - mid, cut, hi))
    for cut in range(lo+1, mid):
        a, b = raw[lo:cut], raw[cut:mid]
        if m.kind == 'i' and second in BLOCKS:
            yield '21', (m,), (Move('i', cut, mid, hi), Move('i', lo, cut, cut + hi - mid))
        if m.kind != 'r':
            continue
        if all(CROSSES[e][0] == 'w' for e in a) and all(CROSSES[e][0] == 'z' for e in b):
            yield '12', (m,), (Move('r', cut, mid, hi), Move('r', lo, cut, cut + hi - mid))
        if all(CROSSES[e][1] == 'x' for e in a) and all(CROSSES[e][1] == 'y' for e in b):
            if set(second) == {'X'}:
                yield '14', (m,), (Move('i', cut, mid, hi), Move('r', lo, cut, cut + hi - mid))
            if set(second) == {'Y'}:
                yield '15', (m, Move('i', lo, lo + len(second), cut + len(second))), (
                    Move('r', cut, mid, hi),)


def laws(raw):
    active = primitive_moves(raw)
    for outer in active:
        yield from split_laws(raw, outer)
        for inner in active:
            if outer.hi <= inner.lo:
                yield 'delta', (inner, outer), (outer, inner)
            if outer.mid <= inner.lo and inner.hi <= outer.hi:
                yield 'N_L' if outer.kind == 'i' else 'U_r', (
                    outer, inner.shift(outer.lo - outer.mid)), (inner, outer)
            if outer.kind == 'i' and outer.lo <= inner.lo and inner.hi <= outer.mid:
                yield 'N_R', (inner, outer), (outer, inner.shift(outer.hi - outer.mid))


@cache
def ground_all(m=1, n=1):
    vertices, edges, rules = set(), {}, {}
    for raw in raw_histories(m, n):
        vertices.add(hist(raw))
        for move in primitive_moves(raw):
            edges[edge_key(raw, move)] = Edge(hist(raw), hist(move.target(raw)), weight(raw, move))
        for law, lhs, rhs in laws(raw):
            source, target = walk(raw, lhs), walk(raw, rhs)
            key = f'{law} {source.edges} {target.edges}'
            rules[key] = Rule(key, source, target, law.isdecimal())
    return Presentation(vertices, edges, rules.values())


def verify_faces(raw, move):
    state = state_at(raw[:move.lo])
    order = ''.join(slot for slot, _ in state)
    first, second = raw[move.lo:move.mid], raw[move.mid:move.hi]
    if move.kind == 'i':
        left = min(map(order.index, slots(second)))
        cut = min(map(order.index, slots(first)))
        right = max(map(order.index, slots(first))) + 1
        source, target = i_faces(History(state[left:cut], tuple(EVENTS[e] for e in second)),
                                 History(state[cut:right], tuple(EVENTS[e] for e in first)))
    else:
        left = min(map(order.index, slots(first)))
        right = max(map(order.index, slots(first))) + 1
        cut = left + len(slots(first) & {'z', 'w'})
        source, target = r_faces(History(state[cut:right], tuple(EVENTS[e] for e in second)),
                                 state[left:cut])
    inverse = {value: key for key, value in EVENTS.items()}
    for face, expected in zip((source, target), (raw, move.target(raw))):
        padded = face.pad(state[:left], state[right:])
        decoded = ''.join(inverse[e] for e in padded.events)
        assert hist(raw[:move.lo] + decoded + raw[move.hi:]) == hist(expected)
        assert padded.start == state and padded.end == state_at(expected[:move.hi])


def check_rectangle(presentation, start, finish, inputs, cut_size):
    a, b, c, d = inputs
    source, target = walk(start, (c, d, a, b)), walk(start, (c, a, d, b))
    assert presentation.end(source) == presentation.end(target) == finish
    positive = solve(presentation, source, target)
    negative = solve(presentation, target, source)
    assert positive.reachable and len(positive.steps) == 1
    assert positive.steps[0].rule.startswith('delta ')
    assert verify(presentation, source, target, positive)
    assert not negative.reachable and len(negative.visited) == cut_size
    assert verify(presentation, target, source, negative)
    uses = Counter(s.rule.split()[0] for path in negative.visited for s, _ in presentation.successors(path))
    print(f'{start} -> {finish}: one forward rectangle, '
          f'{len(negative.visited)} paths in reverse cut: {dict(uses)}.')


def check():
    for m, n in ((2, 0), (1, 1), (0, 2)):
        presentation = ground_all(m, n)
        for raw in raw_histories(m, n):
            for move in primitive_moves(raw):
                verify_faces(raw, move)
        print(f'{m} X and {n} Y: {len(raw_histories(m,n))} raw histories, '
              f'{len(presentation.vertices)} history classes, '
              f'{len(presentation.edges)} projected 4-edges, {len(presentation.rules)} ground rules.')
    presentation = ground_all()
    check_rectangle(presentation, 'pqXrsY', 'XpqYrs', (
        Move('r', 1, 2, 3), Move('r', 0, 1, 2),
        Move('r', 4, 5, 6), Move('r', 3, 4, 5)), 14)
    # A acts on rX -> Xr by iota(X,r); after C, D acts on Yq -> qY
    # by iota(q,Y). B and C are mixed, with C sliding Y across qs.
    check_rectangle(presentation, 'prXqsY', 'XprqYs', (
        Move('i', 1, 2, 3), Move('r', 0, 1, 2),
        Move('r', 3, 5, 6), Move('i', 3, 4, 5)), 10)


if __name__ == '__main__':
    check()
