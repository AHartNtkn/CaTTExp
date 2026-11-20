"""Check binary semaphore zero tests and causal certification of their initial counts."""

from collections import deque
from itertools import product

from homotopy_polygraph_milestones import orders
from homotopy_polygraph_semaphore import Ring, clock_chart
from homotopy_polygraph_two_resources import profiles


def counter(r):
    return 5*r


def request(r, parity):
    return 5*r+1+parity


def ack(r, parity):
    return 5*r+3+parity


def initial_locks():
    # Controller is process 0, counters have monitors 1 and 2. The fourth
    # process of the typed ring stays positive on all ten binary resources.
    counts = [[int(i not in (0, 1 + r//5)) for r in range(10)] for i in range(4)]
    for r, parity in product(range(2), repeat=2):
        counts[0][request(r, parity)] = 1
        counts[r+1][ack(r, parity)] = 1
    return tuple(tuple(row) for row in counts)


def build(program):
    actors = [{}, {}, {}]
    def path(actor, start, end, word):
        graph = actors[actor]
        state = start
        for j, op in enumerate(word):
            target = end if j+1 == len(word) else ('step', len(graph), state, op)
            graph.setdefault(state, []).append((op, target))
            state = target
    for pc, instr in enumerate(program):
        if instr == 'halt':
            continue
        kind, r, *targets = instr
        for bits in product(range(2), repeat=2):
            start = pc, bits
            if kind == 'inc':
                path(0, start, (targets[0], bits), [('P', counter(r))])
            else:
                assert kind == 'test'
                zero, nonzero = targets
                path(0, start, (nonzero, bits), [('V', counter(r))])
                k = bits[r]
                flipped = list(bits)
                flipped[r] ^= 1
                path(0, start, (zero, tuple(flipped)),
                     [('V', request(r,k)), ('P', ack(r,k)),
                      ('V', ack(r,k)), ('P', request(r,k))])
    for r in range(2):
        for state, k, first in [('first', 0, True), (0, 0, False), (1, 1, False)]:
            word = [('P', request(r,k))]
            if not first:
                word.append(('P', ack(r,1-k)))
            word += [('P', counter(r)), ('V', counter(r)),
                     ('V', ack(r,k)), ('V', request(r,k))]
            path(r+1, state, 1-k, word)
    return actors


def reachable(program):
    actors = build(program)
    start = (((0, (0,0)), 'first', 'first'), initial_locks())
    seen, queue = {start}, deque([start])
    at_halt = set()
    while queue:
        controls, counts = queue.popleft()
        state = controls[0]
        if state[0] != 'step' and program[state[0]] == 'halt':
            at_halt.add((state[0], counts[0][counter(0)], counts[0][counter(1)]))
        for actor, graph in enumerate(actors):
            for (op, r), target in graph.get(controls[actor], ()):
                other = 1 + r//5 if actor == 0 else 0
                if (op == 'P' and counts[other][r]) or (op == 'V' and not counts[actor][r]):
                    continue
                row = list(counts[actor])
                row[r] += 1 if op == 'P' else -1
                after = list(counts)
                after[actor] = tuple(row)
                states = list(controls)
                states[actor] = target
                item = tuple(states), tuple(after)
                if item not in seen:
                    seen.add(item)
                    queue.append(item)
    return len(seen), at_halt


def certify_setup():
    words = [[], [], []]
    serial = []
    required = []
    def event(i, op):
        serial.append(i)
        position = i, len(words[i])
        words[i].append(op)
        return position
    def bracket(i, op):
        enter = event(i, None)
        event(i, op)
        leave = event(i, None)
        return enter, leave
    # None denotes a distinct probe marker (neutral in the binary base).
    for r in range(10):
        monitor = 1+r//5
        bracket(0, ('P',r))
        left, _ = bracket(0, ('V',r))
        _, right = bracket(monitor, ('P',r))
        bracket(monitor, ('V',r))
        required.append((left, right))
    pairs = {r: (0, 1+r//5) for r in range(10)}
    initial = [tuple(0 if i in pairs[r] else 1 for r in range(10)) for i in range(3)]
    states = profiles(words, initial)
    for mask in range(1 << 10):
        active = {r: pair for r,pair in pairs.items() if mask >> r & 1}
        order = orders(words, states, serial, active)
        recovered = sum(1 << r for r,(a,b) in enumerate(required) if b in order[a])
        assert recovered == mask
    print('Certified all 1,024 activation patterns from the projected probe precedences.')

    # Compare the complete projected order, including the accept marker, on
    # two different computation suffixes after the same observable setup.
    for r, k in product(range(2), repeat=2):
        bracket(0, ('P', request(r,k)))
        bracket(r+1, ('P', ack(r,k)))
    for actor in range(3):
        event(actor, None)  # go marker
    for r in range(2):
        monitor = 1 + r
        for actor, op, name in [(0,'V',request(r,0)), (monitor,'P',request(r,0)),
                                (monitor,'P',counter(r)), (monitor,'V',counter(r)),
                                (monitor,'V',ack(r,0)), (0,'P',ack(r,0)),
                                (0,'V',ack(r,0)), (monitor,'V',request(r,0)),
                                (0,'P',request(r,0))]:
            event(actor, (op,name))
    def table(extra):
        seq = [*serial] + [0]*(len(extra)+1)
        extended = [words[0]+extra+[None], *words[1:]]
        closure = orders(extended, profiles(extended, initial), seq, pairs)
        marks = [(i,j) for i, word in enumerate(extended) for j, op in enumerate(word) if op is None]
        halt = (0,len(extended[0])-1)
        assert all(halt in closure[e] for e in marks if e != halt)
        return len(marks), {(j,k) for j,a in enumerate(marks) for k,b in enumerate(marks) if b in closure[a]}
    n, canonical = table([])
    assert table([('P',counter(0)), ('P',counter(1)), ('V',counter(0))]) == (n, canonical)
    print(f'The same {n} marked events and {len(canonical)} strict comparisons survive both suffixes.')


def spatial_zero_test():
    r, k = 0, 0
    words = [[('V', request(r,k)), ('P', ack(r,k)),
              ('V', ack(r,k)), ('P', request(r,k))],
             [('P', request(r,k)), ('P', counter(r)), ('V', counter(r)),
              ('V', ack(r,k)), ('V', request(r,k))], [], []]
    layout = Ring(4)
    order = (0,1,1,1,1,0,0,1,0)
    for number in (0, 1, 2):
        initial = [list(row) for row in initial_locks()]
        initial[0][counter(r)] = number
        states = profiles(words, initial)
        pos = [0]*4
        for j, i in enumerate(order):
            legal = clock_chart(layout, words, states, pos, (i,), 10)
            if not legal:
                assert number > 0 and j == 2
                break
            pos[i] += 1
        else:
            assert number == 0
    print('Spatial clocks allow a zero read and block it at controller counts one and two.')


def check():
    # Repeated true zero tests on the same counter exercise both parity slots.
    # Wrong guesses must not reach the alternate accept states, even after two
    # successive requests or while the controller is using the other counter.
    programs = [
        ([('inc',0,1), ('test',0,3,2), 'halt', 'halt'], {(2,0,0)}),
        ([('test',0,1,5), ('test',0,2,5), ('test',0,3,5),
          ('inc',0,4), ('test',0,5,6), 'halt', 'halt'], {(6,0,0)}),
        ([('inc',0,1), ('test',1,2,5), ('inc',1,3), ('test',0,5,4),
          ('test',1,5,6), 'halt', 'halt'], {(6,0,0)}),
        ([('test',0,0,1), 'halt'], set()),
    ]
    for program, expected in programs:
        states, final = reachable(program)
        assert final == expected
        print(f'{states} reachable asynchronous states; accepting states {sorted(final)}.')
    spatial_zero_test()
    certify_setup()


if __name__ == '__main__':
    check()
