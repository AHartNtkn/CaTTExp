"""Enumerate asynchronous reads, literal tape appends and commits of a small tap tree."""

from collections import deque
from itertools import product


# Incoming edge mailbox: virgin, boot, idle, ask, 0/1/EOF, commit,
# committed, returned, retired. The root has a separate driver mailbox.
CHILDREN = ((1, 2), (3,), (), ())
TAPS = {1, 2, 3}
ORDER = (1, 3, 2)
PREP = frozenset(('virgin', 'boot', 'idle', 'ask', '0', '1', 'eof'))


def put(items, i, value):
    return items[:i] + (value,) + items[i+1:]


def initial(local=None, mail=None):
    return (local or (('new', 0, None),)*4, mail or ('boot', 'virgin', 'virgin', 'virgin'),
            'seed', 'open', ())


def successors(state, accepted):
    local, mail, tape, driver, fired = state
    for i, children in enumerate(CHILDREN):
        phase, cursor, bit = local[i]
        if phase == 'new':
            if mail[i] != 'boot' or any(mail[j] != 'virgin' for j in children):
                continue
            if i == 0 and tape != 'seed':
                continue
            m = put(mail, i, 'idle')
            for j in children:
                m = put(m, j, 'boot')
            for picked in ('0', '1') if i in TAPS else (None,):
                yield (put(local, i, ('idle', -1 if i in TAPS else 0, picked)), m,
                       'gHr' if i == 0 else tape, driver, fired)
            continue

        if phase in ('idle', 'work', 'wait') and all(mail[j] in PREP for j in children):
            if phase == 'idle' and mail[i] == 'ask':
                yield put(local, i, ('work', cursor, bit)), mail, tape, driver, fired
            if phase == 'work' and mail[i] == 'ask' and cursor == -1:
                yield put(local, i, ('idle', 0, bit)), put(mail, i, bit), tape, driver, fired
            if phase == 'work' and mail[i] == 'ask' and cursor == len(children):
                yield put(local, i, ('idle', cursor, bit)), put(mail, i, 'eof'), tape, driver, fired
            if phase == 'work' and mail[i] == 'ask' and 0 <= cursor < len(children):
                j = children[cursor]
                if mail[j] == 'idle':
                    yield put(local, i, ('wait', cursor, bit)), put(mail, j, 'ask'), tape, driver, fired
            if phase == 'wait' and mail[i] == 'ask':
                j = children[cursor]
                reply = mail[j]
                m = put(mail, j, 'idle')
                if reply == 'eof':
                    yield put(local, i, ('work', cursor+1, bit)), m, tape, driver, fired
                elif reply in ('0', '1'):
                    yield (put(local, i, ('idle', cursor, bit)), put(m, i, reply),
                           tape, driver, fired)

        if (phase == 'idle' and mail[i] == 'commit' and all(mail[j] == 'idle' for j in children)
                and (i != 0 or tape.startswith('aH'))):
            m = put(mail, i, 'committed')
            for j in children:
                m = put(m, j, 'commit')
            yield put(local, i, ('ready', cursor, bit)), m, tape, driver, fired
        if phase == 'ready' and bit == '1':
            yield put(local, i, ('done', cursor, bit)), mail, tape, driver, fired + (i,)
        if (phase in ('ready', 'done') and (bit != '1' or phase == 'done')
                and mail[i] == 'committed' and all(mail[j] == 'returned' for j in children)):
            m = put(mail, i, 'returned')
            for j in children:
                m = put(m, j, 'retired')
            yield put(local, i, ('closed', cursor, bit)), m, tape, driver, fired

    # Literal latch/head word rewrites. Only the root electronics see the latch.
    if driver == 'open' and mail[0] == 'idle' and tape.startswith('gH'):
        yield local, put(mail, 0, 'ask'), tape, 'wait', fired
    if driver == 'wait' and mail[0] in ('0', '1'):
        yield local, put(mail, 0, 'idle'), mail[0] + tape[1:], 'append', fired
    if driver == 'append' and tape[:2] in ('0H', '1H'):
        yield local, mail, 'gH' + tape[0] + tape[2:], 'open', fired
    if driver == 'wait' and mail[0] == 'eof' and tape.startswith('gH'):
        yield local, put(mail, 0, 'idle'), 'v' + tape[1:], 'verify', fired
    if driver == 'verify' and tape.startswith('vH') and tape.endswith('r'):
        if tape[2:-1][::-1] in accepted:
            yield local, put(mail, 0, 'commit'), 'aHr', 'close', fired
    if driver == 'close' and mail[0] == 'returned':
        yield local, put(mail, 0, 'retired'), tape, 'final', fired


def run(start, accepted):
    todo = deque([start])
    seen = {start}
    outcomes = set()
    while todo:
        state = todo.popleft()
        local, mail, tape, driver, fired = state
        if driver == 'final':
            assert all(phase == 'closed' for phase, _, _ in local)
            outcomes.add((''.join(local[i][2] for i in ORDER), fired))
        for other in successors(state, accepted):
            if other not in seen:
                seen.add(other)
                todo.append(other)
    return len(seen), outcomes


def main():
    from itertools import permutations

    accepted = {'000', '011', '101', '111'}
    states, outcomes = run(initial(), accepted)
    expected = {(bits, order) for bits in accepted
                for order in permutations(i for i, b in zip(ORDER, bits) if b == '1')}
    assert outcomes == expected
    print(f'{states} reachable states; all {len(outcomes)} accepted matrix and payload orders.')

    # A forged active station or pre-filled edge can answer in a truncated
    # computation. Neither can complete a fresh pair of master seals.
    n = 0
    local, mail, *_ = initial()
    for i in range(1, len(local)):
        for phase, value in product(('idle', 'ready', 'done', 'closed'), ('0', '1')):
            assert not run(initial(local=put(local, i, (phase, 0, value))), accepted)[1]
            n += 1
        for forged in ('idle', 'ask', '0', 'eof', 'committed', 'returned'):
            assert not run(initial(mail=put(mail, i, forged)), accepted)[1]
            n += 1
    print(f'{n} altered initial records checked against full return.')


if __name__ == '__main__':
    main()
