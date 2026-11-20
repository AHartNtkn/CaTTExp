"""Positive 4-moves and contextual K15 equalities on reduced sorting histories.

A raw 3-history records each adjacent inversion by its two names in ascending
order. At a temporal cut every spatial operand occupies an interval of the
current chronological 2-word. We enumerate every pair of adjacent nonempty
intervals, including spectators inside either operand, and every pair of
internal sorting histories (which may stop before sorting is complete).
For mixed faces all names in the second interval must precede all names in
the first along the outer tree. This is exactly the guard for their block
crossing. The surrounding temporal prefix/suffix and spatial padding are
arbitrary. Empty varying inputs specialize by degeneracy.

The 7a,b recursion gives all direct expansions of a block crossing. Additional
representatives reached by rewriting inside a block, an operand, or a whisker
appear via equality edges at their own windows. Such steps are bidirectional.
"""
from collections import defaultdict
from dataclasses import dataclass
from functools import cache
from itertools import combinations, product

from interchange_path_grading import History, cross, i_faces, r_faces, t_faces, word
from marked_swap_schedules import expansions


@dataclass(frozen=True)
class Move:
    """left/right are spatial slot words at lo, before a mixed block crosses.

    left_events/right_events are their respective internal varying histories.
    Thus r(A,b) has A on the right at lo and t(a,B) has B on the left.
    For i the right input acts first in the source. hi is exclusive.
    """
    family: str
    source: tuple
    target: tuple
    lo: int
    hi: int
    left: str
    right: str
    left_events: tuple
    right_events: tuple


def advance(state, event):
    if len(event) != 2 or event[0] >= event[1] or event[::-1] not in state:
        raise ValueError(f'{event!r} is not an enabled crossing of {state!r}')
    return state.replace(event[::-1], event)


def states(start, raw):
    yield start
    for event in raw:
        start = advance(start, event)
        yield start


@cache
def _prefixes(state):
    return ((),) + tuple(
        (pair[::-1], *tail)
        for i in range(len(state) - 1)
        for pair in (state[i:i+2],) if pair[0] > pair[1]
        for tail in _prefixes(advance(state, pair[::-1])))


@cache
def raw_histories(start, end=None):
    """All positive adjacent-crossing histories from start to end."""
    _check_slots(start)
    if end is None:
        end = ''.join(sorted(start))
    if sorted(start) != sorted(end):
        raise ValueError('the sorting interval endpoints must have the same strands')
    if start == end:
        return ((),)
    return tuple((b + a, *tail)
                 for a, b in zip(start, start[1:])
                 if a > b and end.index(a) > end.index(b)
                 for tail in raw_histories(advance(start, b + a), end))


def _check_slots(start):
    if not 1 <= len(start) <= 6 or len(set(start)) != len(start):
        raise ValueError('a sorting fiber has one to six distinct factor names')


@cache
def _blocks(left, right):
    # marked_swap_schedules takes movers first and stationary slots second.
    return tuple(sorted(tuple(a + b for a, b in p)
                        for p in expansions(tuple(right), tuple(left))))


def _history(start, events):
    return History(word(start), tuple(tuple(e[::-1]) for e in events))


def _raw(history):
    return tuple(b + a for a, b in history.events)


def _join_faces(a, b):
    source = b.pad(right=a.start).then(cross(a.start, b.end)).then(a.pad(right=b.end))
    target = a.pad(left=b.start).then(b.pad(right=a.end)).then(cross(a.end, b.end))
    return source, target


def _presentations(face, first, left, right):
    """All direct expansions of the designated rectangular block in one face."""
    base = _raw(face)
    width = len(left) * len(right)
    alternatives = _blocks(left, right)
    assert base[first:first+width] in alternatives
    return tuple(base[:first] + alternative + base[first+width:] for alternative in alternatives)


@cache
def _local(left, right):
    """Ground local faces once, independently of the surrounding word."""
    rows = []
    can_cross = max(right) < min(left)
    if can_cross:
        rect = _blocks(left, right)
        rows.extend(('K15', p, q, (), ()) for p in rect for q in rect if p != q)
    for le, re in product(_prefixes(left), _prefixes(right)):
        if not (le or re):
            continue
        b, a = _history(left, le), _history(right, re)
        if le and re:
            source, target = i_faces(b, a)
            rows.append(('i', _raw(source), _raw(target), le, re))
        if not can_cross:
            continue
        after_left = ''.join(s for s, _ in b.end)
        after_right = ''.join(s for s, _ in a.end)
        if not le:
            source, target = r_faces(a, b.start)
            family = 'r'
        elif not re:
            source, target = t_faces(a.start, b)
            family = 't'
        else:
            source, target = _join_faces(a, b)
            family = 'h'
        assert (source.start, source.end) == (target.start, target.end)
        source_options = _presentations(source, len(le), after_left, right)
        # In t, the varying left block acts after the crossing in the target.
        target_cut = 0 if family == 't' else len(le) + len(re)
        target_left = left if family == 't' else after_left
        target_options = _presentations(target, target_cut, target_left, after_right)
        rows.extend((family, p, q, le, re) for p, q in product(source_options, target_options))
    return rows


@cache
def _at_state(state):
    by_source = defaultdict(list)
    for low, cut, high in combinations(range(len(state) + 1), 3):
        left, right = state[low:cut], state[cut:high]
        for family, p, q, le, re in _local(left, right):
            by_source[p].append((family, q, left, right, le, re))
    return by_source


@cache
def moves(start, raw):
    """Ground each positive primitive or equality at every temporal window."""
    _check_slots(start)
    result = []
    for lo, state in enumerate(states(start, raw)):
        rules = _at_state(state)
        for hi in range(lo + 1, len(raw) + 1):
            for family, local, left, right, le, re in rules.get(raw[lo:hi], ()):
                target = raw[:lo] + local + raw[hi:]
                result.append(Move(family, raw, target, lo, hi, left, right, le, re))
    return tuple(result)


def reachable(start, raw):
    """Raw states reached by directed positive moves and bidirectional K15."""
    seen, pending = {raw}, [raw]
    while pending:
        for edge in moves(start, pending.pop()):
            if edge.target not in seen:
                seen.add(edge.target)
                pending.append(edge.target)
    return frozenset(seen)


def native_generators(slots):
    """Globular assignment for the native evaluator on a string of 2-globes."""
    from check_two_moving_native import Value
    from interchange_free import tree_generators

    data, _ = tree_generators([[[]] for _ in slots])
    values = {}
    for key, (degree, bounds) in data.items():
        source, target = (values[b] for b in bounds) if bounds else (None, None)
        if degree == 2:
            trace = word(slots[int(key.split('/')[0])])
        else:
            trace = (key,) if degree else key
        values[key] = Value(degree, source, target, trace)
    return values


@cache
def _native_triangle_faces(names):
    """Evaluate both native sides of equation 18 on a wedge of three 2-globes."""
    from check_two_moving_native import Evaluator
    from reachability_theory import EQUATIONS, OPERATIONS

    evaluate = Evaluator()
    evaluate.generators = native_generators(names)
    eq = next(e for e in EQUATIONS if e.name == '18')
    env = {var: evaluate.generators[f'{i}/0/0'] for i, (var, _) in enumerate(eq.variables)}
    assert all(evaluate.read(s, env) == evaluate.read(t, env) for s, t in eq.guards)
    ends = []
    for name, *children in (eq.left, eq.right):
        args = {f'x{i}': evaluate.read(expr, env) for i, expr in enumerate(children)}
        schema = OPERATIONS[name]
        assert all(evaluate.read(s, args) == evaluate.read(t, args) for s, t in schema.guards)
        ends.append(tuple(_raw(evaluate.read(expr, args).trace) for expr in (schema.source, schema.target)))
    assert ends[0] == ends[1]
    return ends[0]


def native_triangle(start, source, target):
    """Whether this contextual edge is the native r(chi,–) = t(–,chi) triangle."""
    source_states = tuple(states(start, source))
    target_states = tuple(states(start, target))
    if len(source) != len(target) or source_states[-1] != target_states[-1]:
        return False
    for lo in range(len(source) - 2):
        hi = lo + 3
        if source[:lo] != target[:lo] or source[hi:] != target[hi:]:
            continue
        names = ''.join(sorted(set(''.join(source[lo:hi]))))
        if len(names) != 3 or names[::-1] not in source_states[lo]:
            continue
        if (source[lo:hi], target[lo:hi]) == _native_triangle_faces(names):
            return True
    return False


def check():
    """Check enabledness, contextual native triangles and erasure on every edge."""
    from collections import Counter

    smaller_closure = cache(reachable)
    for start, count in (('a', 1), ('ba', 1), ('cba', 2), ('dcba', 16), ('edcba', 768)):
        histories = set(raw_histories(start))
        assert len(histories) == count
        families = Counter()
        triangles = set()
        for p in histories:
            for edge in moves(start, p):
                q = edge.target
                assert edge.source == p and q in histories
                families[edge.family] += 1
                if edge.family == 'K15':
                    assert any(rev.family == 'K15' and rev.target == p for rev in moves(start, q))
                if edge.family in ('r', 't') and len(edge.left + edge.right) == 3:
                    assert native_triangle(start, p, q)
                    triangles.add((p, q))
                for slot in start:
                    small = start.replace(slot, '')
                    source, target = (tuple(e for e in raw if slot not in e) for raw in (p, q))
                    assert target in smaller_closure(small, source)
        print(f'{start}: {len(histories)} histories, {len(triangles)} triangle boundaries, {dict(families)}')


if __name__ == '__main__':
    check()
