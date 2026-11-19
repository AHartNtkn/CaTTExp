"""Response 12 grounding on 321xy -> xy321 with one X or one Y.

Letters abc and def cross x and y, respectively, with columns 123 in
chronological order. Work on *all* atomic schedules. Each contiguous
rectangle can be re-expressed in any of its (7a,b) expansions, including
inside a temporal whisker. The least word in the undirected closure names
the 3-class. A primitive 4-edge records its two whole history classes,
Response 4 weight, and an unordered multiset of event-pair or mixed labels.
These data are unchanged by re-expressing an operand or whisker. Merging
such occurrences allows every original path and rewrite to project here.

The stationary branch forces the outer cut-zero completion to specialize
as in Response 18. On the moving branch the single unary admits no positive
4-variation. For a proper shifted join one input would lack the unary and
need four distinct slots for two disjoint crossings. Its other input would
need at least two more. For inner naturality both spatial histories have
positive mass, and the varying input can be treated one edge at a time.
Temporal comparison on composite paths pastes the single-edge comparisons.
In a temporal comparison the windows admit independent representatives;
in inner naturality they are disjoint spatial operands. In both cases the
grounding runs through all representatives exposing the chosen edge. Every
lower temporal context is included, and Presentation supplies top contexts.
"""

from collections import defaultdict
from functools import cache
from itertools import combinations, product

from interchange_path_grading import History, i_faces, r_faces, word
from interchange_reachability import Edge, Path, Presentation, Rule, solve, verify
from interchange_response12_rectangles import shifted_joins
from interchange_two_moving import Move
from marked_swap_schedules import expansions, schedules, table


START = '321xy'
SIGNED = {'3': -3, '2': -2, '1': -1, 'x': 1, 'y': 2}
START_SIGNED = tuple(map(SIGNED.__getitem__, START))
END_SIGNED = tuple(map(SIGNED.__getitem__, 'xy321'))
CROSSES = dict(zip('abcdef', product('xy', '123')))
EVENTS = {e: (col, row) for e, (row, col) in CROSSES.items()}
EVENTS.update(X=('x',), Y=('y',))
LETTER = {slots: e for e, slots in EVENTS.items()}


def letters(schedule):
    return ''.join(LETTER[col, row] for row, col in schedule)


def intervals(seq):
    return (seq[i:j] for i, j in combinations(range(len(seq) + 1), 2))


# expansions expects columns in spatial (far-to-near) order.
RECTANGLES = {letters(order): (rows, cols)
              for rows, cols in product(intervals('xy'), intervals('321'))
              for order in expansions(tuple(rows), tuple(cols))}
ALTERNATIVES = {p: tuple(q for q, shape in RECTANGLES.items() if shape == rect and q != p)
                for p, rect in RECTANGLES.items()}
ALTERNATIVES = {p: qs for p, qs in ALTERNATIVES.items() if qs}


@cache
def representatives(raw):
    """The full contextual K15 closure, also usable on a proper subword."""
    found, pending = {raw}, [raw]
    while pending:
        current = pending.pop()
        for fragment, others in ALTERNATIVES.items():
            i = current.find(fragment)  # Each crossing occurs only once.
            if i >= 0:
                for other in others:
                    after = current[:i] + other + current[i + len(fragment):]
                    if after not in found:
                        found.add(after)
                        pending.append(after)
    return tuple(sorted(found))


def hist(raw):
    return representatives(raw)[0]


BLOCKS = {rep: shape for raw, shape in RECTANGLES.items() for rep in representatives(raw)}


@cache
def raw_histories(unary):
    if unary not in ('X', 'Y'):
        raise ValueError('a strip carries exactly one unary advance, X or Y')
    # Negative and positive names number stationary and moving slots separately.
    orders = (letters(('xy'[r-1], str(c)) for r, c in seq)
              for seq in schedules(START_SIGNED, END_SIGNED))
    return tuple(raw[:i] + unary + raw[i:] for raw in orders for i in range(len(raw) + 1))


@cache
def slots(seq):
    return frozenset(s for e in seq for s in EVENTS[e])


@cache
def state_at(prefix):
    return History(word(START), tuple(EVENTS[e] for e in prefix)).end


@cache
def primitive_moves(raw):
    result = []
    for lo, mid, hi in combinations(range(len(raw) + 1), 3):
        first, second = raw[lo:mid], raw[mid:hi]
        if first in BLOCKS and second in ('X', 'Y') and second.lower() in BLOCKS[first][0]:
            result.append(Move('r', lo, mid, hi))
        order = [s for s, _ in state_at(raw[:lo])]
        if max(map(order.index, slots(second))) < min(map(order.index, slots(first))):
            result.append(Move('i', lo, mid, hi))
    return tuple(result)


def edge_labels(raw, move):
    """Label all event pairs of i, or all unary/column mixed atoms of r."""
    first, second = raw[move.lo:move.mid], raw[move.mid:move.hi]
    if move.kind == 'i':
        return tuple(sorted(('i', f, s) for f, s in product(first, second)))
    return tuple(('r', second, col) for col in sorted(BLOCKS[first][1]))


def weight(raw, move):
    first, second = raw[move.lo:move.mid], raw[move.mid:move.hi]
    if move.kind == 'i':
        return len(first) * len(second)
    rows, cols = BLOCKS[first]
    moment = len(rows) - 1 - 2 * rows.index(second.lower())
    return len(cols) * (11 + moment)


@cache
def edge_key(raw, move):
    labels = '.'.join(''.join(label) for label in edge_labels(raw, move))
    return f'{hist(raw)}/{hist(move.target(raw))}/{weight(raw, move)}/{labels}'


def walk(raw, sequence):
    names = []
    state = raw
    for move in sequence:
        assert move in primitive_moves(state), (state, move)
        names.append(edge_key(state, move))
        state = move.target(state)
    return Path(hist(raw), tuple(names))


def laws(raw):
    active = primitive_moves(raw)
    for outer in active:
        lo, mid, hi = outer.lo, outer.mid, outer.hi
        first, second = raw[lo:mid], raw[mid:hi]
        # Equation 10 would split a unary operand of chronological length one.
        if outer.kind == 'i' and first in BLOCKS:
            for cut in range(mid + 1, hi):
                yield '20', (outer,), (Move('i', lo, mid, cut), Move('i', lo + cut-mid, cut, hi))
        for cut in range(lo + 1, mid):
            a, b = raw[lo:cut], raw[cut:mid]
            if outer.kind == 'i':
                if second in BLOCKS:
                    yield '21', (outer,), (Move('i', cut, mid, hi), Move('i', lo, cut, cut + hi-mid))
                continue
            if a not in BLOCKS or b not in BLOCKS:
                continue
            ra, ca = BLOCKS[a]
            rb, cb = BLOCKS[b]
            rows, cols = BLOCKS[first]
            if ra == rb and cb + ca == cols:
                yield '12', (outer,), (Move('r', cut, mid, hi), Move('r', lo, cut, cut + hi-mid))
            if ra + rb == rows and ca == cb:
                if second == 'X':
                    yield '14', (outer,), (Move('i', cut, mid, hi), Move('r', lo, cut, cut + hi-mid))
                else:
                    yield '15', (outer, Move('i', lo, lo + 1, cut + 1)), (Move('r', cut, mid, hi),)
        for inner in active:
            if hi <= inner.lo:
                yield 'delta', (inner, outer), (outer, inner)
            if mid <= inner.lo and inner.hi <= hi:
                yield 'N_L' if outer.kind == 'i' else 'U_r', (
                    outer, inner.shift(lo - mid)), (inner, outer)
            if outer.kind == 'i' and lo <= inner.lo and inner.hi <= mid:
                yield 'N_R', (inner, outer), (outer, inner.shift(hi - mid))


@cache
def metadata(unary):
    result = defaultdict(set)
    for raw in raw_histories(unary):
        for move in primitive_moves(raw):
            result[edge_key(raw, move)].add((raw, move))
    return {key: frozenset(occurrences) for key, occurrences in result.items()}


@cache
def ground_all(unary):
    edges, rules = {}, {}
    for key, occurrences in metadata(unary).items():
        raw, move = min(occurrences)
        edges[key] = Edge(hist(raw), hist(move.target(raw)), weight(raw, move))
    vertices = {hist(raw) for raw in raw_histories(unary)}
    for raw in raw_histories(unary):
        for label, left, right in laws(raw):
            source, target = walk(raw, left), walk(raw, right)
            name = f'{label} {source.edges} {target.edges}'
            rules[name] = Rule(name, source, target, label.isdecimal())
    return Presentation(vertices, edges, rules.values())


def verify_faces(raw, move):
    """Typecheck the padded faces of each primitive occurrence."""
    prefix, first, second, suffix = (raw[:move.lo], raw[move.lo:move.mid],
                                     raw[move.mid:move.hi], raw[move.hi:])
    state = state_at(prefix)
    order = [s for s, _ in state]
    if move.kind == 'r':
        rows, cols = BLOCKS[first]
        lo = order.index(cols[0])
        mid, hi = lo + len(cols), lo + len(cols) + len(rows)
        assert ''.join(order[lo:hi]) == cols + rows
        faces = r_faces(History(state[mid:hi], (EVENTS[second],)), state[lo:mid])
    else:
        lo, mid, hi = (min(map(order.index, slots(second))), min(map(order.index, slots(first))),
                       max(map(order.index, slots(first))) + 1)
        faces = i_faces(History(state[lo:mid], tuple(EVENTS[e] for e in second)),
                        History(state[mid:hi], tuple(EVENTS[e] for e in first)))
    for face, expected in zip(faces, (raw, move.target(raw))):
        padded = face.pad(state[:lo], state[hi:])
        assert padded.start == state and padded.end == state_at(expected[:move.hi])
        decoded = ''.join(LETTER[e] for e in padded.events)
        assert hist(prefix + decoded + suffix) == hist(expected)


def check_classes(raws, unary):
    # K15 cannot traverse the unary. Independently compute the classes of
    # the two resulting intervals using dynamically enabled spatial blocks.
    @cache
    def classes(start, end):
        return table(start, end)[0]

    def order(events):
        return tuple((SIGNED[row], int(col)) for row, col in map(CROSSES.__getitem__, events))

    keys = {}
    for raw in raws:
        before, after = raw.split(unary)
        middle = tuple(SIGNED[s] for s, _ in state_at(before))
        keys[raw] = (middle, classes(START_SIGNED, middle)[order(before)],
                     classes(middle, END_SIGNED)[order(after)])
    for raw in raws:
        assert set(representatives(raw)) == {other for other in raws if keys[other] == keys[raw]}


def check_five_slot_rectangle(unary):
    # The early half has A = H² and B = H on the first two columns.
    # The late half uses the third column, with a mixed active input for
    # X and a mixed inactive input for Y. Both late inputs are positive.
    start = 'adbecf' + unary
    c, d = ((Move('i', 5, 6, 7), Move('r', 4, 5, 6)) if unary == 'X' else
            (Move('r', 4, 6, 7), Move('i', 4, 5, 6)))
    graph = ground_all(unary)

    def route(schedule):
        state, edges = start, []
        for label in schedule:
            if label == 'H':
                # K15 re-exposes the loop on exactly the first four events.
                assert state[:4] in ('adbe', 'abde') and hist(state) == hist('adbe' + state[4:])
                state = 'adbe' + state[4:]
                move = Move('i', 1, 2, 3)
            else:
                move = c if label == 'C' else d
            verify_faces(state, move)
            edges.extend(walk(state, (move,)).edges)
            state = move.target(state)
        return Path(hist(start), tuple(edges))

    source, target = route('CDHHH'), route('CHHDH')
    assert graph.end(source) == graph.end(target) == ('abdeXcf' if unary == 'X' else 'abdecYf')
    forward, reverse = solve(graph, source, target), solve(graph, target, source)
    assert forward.reachable and len(forward.steps) == 2 and verify(graph, source, target, forward)
    assert not reverse.reachable and verify(graph, target, source, reverse)
    print(f'{unary}: five-slot comparison, two forward steps, {len(reverse.visited)} paths in reverse cut.')


def check():
    for unary in 'XY':
        graph = ground_all(unary)
        raws = set(raw_histories(unary))
        check_classes(raws, unary)
        for raw in raws:
            assert state_at(raw) == tuple((s, int(s == unary.lower())) for s in 'xy321')
            assert not tuple(shifted_joins(raw, primitive_moves))
            for move in primitive_moves(raw):
                verify_faces(raw, move)
        print(f'{unary}: {len(raws)} schedules, {len(graph.vertices)} classes, '
              f'{len(graph.edges)} edges, {len(graph.rules)} rules.')
        check_five_slot_rectangle(unary)


if __name__ == '__main__':
    check()
