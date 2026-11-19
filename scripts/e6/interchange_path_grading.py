"""Check the degree-four grading and degree-five boundary drops on word histories."""

from dataclasses import dataclass
from itertools import permutations, product

from marked_swap_schedules import occurrences, schedules


@dataclass(frozen=True)
class History:
    start: tuple
    events: tuple = ()

    def walk(self):
        state = list(self.start)
        moment = 0
        for event in self.events:
            names = [name for name, version in state]
            pos = names.index(event[0])
            if len(event) == 1:
                name, version = state[pos]
                state[pos] = (name, version + 1)
            else:
                assert names[pos + 1] == event[1]
                state[pos], state[pos + 1] = state[pos + 1], state[pos]
            moment += len(state) - 2 * pos - len(event)
        return tuple(state), moment

    @property
    def end(self):
        return self.walk()[0]

    @property
    def moment(self):
        return self.walk()[1]

    @property
    def mass(self):
        return len(self.events)

    def pad(self, left=(), right=()):
        return History(left + self.start + right, self.events)

    def then(self, other):
        assert self.end == other.start
        return History(self.start, self.events + other.events)


def word(names):
    return tuple((name, 0) for name in names)


def cross(a, b):
    events = tuple((y, x) for x, _ in a for y, _ in reversed(b))
    result = History(b + a, events)
    assert result.end == a + b
    return result


def families(names):
    a, b = names
    events = ((a,), (b,), (b, a))
    for sequence in permutations(events):
        for size in range(4):
            yield History(word((b, a)), sequence[:size])


def parallel_drop(source, target):
    assert source.start == target.start and source.end == target.end
    assert source.mass == target.mass
    return source.moment - target.moment


def r_faces(a, b):
    source = cross(a.start, b).then(a.pad(right=b))
    target = a.pad(left=b).then(cross(a.end, b))
    assert parallel_drop(source, target) == 2 * a.mass * len(b)
    return source, target


def t_faces(a, b):
    source = b.pad(right=a).then(cross(a, b.end))
    target = cross(a, b.start).then(b.pad(left=a))
    assert parallel_drop(source, target) == 2 * len(a) * b.mass
    return source, target


def i_faces(a, b):
    source = b.pad(left=a.start).then(a.pad(right=b.end))
    target = a.pad(right=b.start).then(b.pad(left=a.end))
    assert parallel_drop(source, target) == 0
    return source, target


# All concrete histories below have at most nine slots and thirty transitions.
C = 40


def r(a, b):
    return len(b) * (C * a.mass + a.moment)


def t(a, b):
    return len(a) * (C * b.mass - b.moment)


def inner(a, b):
    return a.mass * b.mass


def join(a, b):
    return r(a, b.end) - inner(a, b)


def check_blocks():
    count = 0
    for u, v in product(range(1, 6), repeat=2):
        if u + v > 7:
            continue
        start = occurrences('L' * v + 'E' * u)
        end = occurrences('E' * u + 'L' * v)
        for order in schedules(start, end):
            history = History(word(start), tuple((-j, i) for i, j in order))
            assert history.end == word(end)
            assert history.mass == u * v and history.moment == 0
            padded = history.pad(word(('left',)), word(('right1', 'right2')))
            assert padded.moment == u * v
            count += 1
    return count


def check_presentations():
    count = 0
    spectator = word('xyz')
    for a, b in product(set(families('AB')), set(families('DE'))):
        f, g = a.start, b.start
        for cut in range(a.mass + 1):
            p = History(f, a.events[:cut])
            q = History(p.end, a.events[cut:])
            assert r(a, g) == r(p, g) + r(q, g)
            assert inner(a, b) == inner(p, b) + inner(q, b)
        for cut in range(b.mass + 1):
            p = History(g, b.events[:cut])
            q = History(p.end, b.events[cut:])
            assert t(f, b) == t(f, p) + t(f, q)
            assert inner(a, b) == inner(a, p) + inner(a, q)
        x, y = cross(spectator, g), cross(f, spectator)
        assert r(a, g + spectator) == r(a, g) + r(a, spectator)
        assert t(f + spectator, b) == t(f, b) + t(spectator, b)
        assert r(a.pad(right=spectator), g) == inner(a, x) + r(a, g)
        assert r(a.pad(left=spectator), g) + inner(x, a) == r(a, g)
        assert inner(b, y) + t(f, b.pad(right=spectator)) == t(f, b)
        assert t(f, b.pad(left=spectator)) == t(f, b) + inner(y, b)
        assert r(cross(f, g), spectator) == t(f, cross(g, spectator))
        assert (join(a, b) > 0) == (a.mass > 0)
        if not b.mass:
            assert join(a, b) == r(a, g)
        assert r(a, ()) == 0 and t((), b) == 0

        # Read the six schedules of the generic binary atom in actual word states.
        source = b.pad(right=f).then(cross(f, b.end)).then(a.pad(right=b.end))
        upper = a.pad(left=g).then(b.pad(right=a.end)).then(cross(a.end, b.end))
        assert parallel_drop(source, upper) == 2 * a.mass * len(g)
        v0 = cross(f, g).then(b.pad(left=f)).then(a.pad(right=b.end))
        v1 = cross(f, g).then(a.pad(right=g)).then(b.pad(left=a.end))
        u1 = b.pad(right=f).then(a.pad(left=b.end)).then(cross(a.end, b.end))
        end = a.pad(left=g).then(cross(a.end, g)).then(b.pad(left=a.end))
        for p, q, loss in ((source, v0, 2 * len(f) * b.mass), (v0, v1, 0),
                           (v1, end, 2 * len(g) * a.mass), (upper, u1, 0),
                           (upper, end, 2 * len(f) * b.mass)):
            assert parallel_drop(p, q) == loss
        lower_weight = t(f, b) + inner(a, b) + r(a, g)
        upper_weight = join(a, b) + t(a.end, b)
        assert lower_weight - upper_weight == 2 * a.mass * b.mass

        for p, q in (r_faces(a, g), t_faces(f, b), i_faces(a, b), (source, upper)):
            drop = parallel_drop(p, q)
            assert drop >= 0
            assert r(p, spectator) - r(q, spectator) == len(spectator) * drop
            assert t(spectator, q) - t(spectator, p) == len(spectator) * drop
            assert inner(p, a) == inner(q, a)
        count += 1
    return count


if __name__ == '__main__':
    print(f'Checked moments of {check_blocks()} fully executed block schedules.')
    print(f'Checked grading equations and signed boundaries on {check_presentations()} history pairs.')
