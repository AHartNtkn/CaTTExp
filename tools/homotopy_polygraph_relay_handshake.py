"""Enumerate partial handshake traces, their induced orders, and guarded time cubes."""

from itertools import combinations, product

from homotopy_polygraph_guarded_boxes import Board, acyclic_chart, compile_boxes


def tree_records():
    # The grandchild tests propagation past the first generation.
    children = [(0, 1), (0, 2), (1, 3)]
    relays = {2: 'alpha', 3: 'beta'}
    words = [('start', 'end'), ('start', 'open0', 'close0', 'end')]
    for i, j in children:
        words.append((f'open{i}', f'open{j}', f'close{j}', f'close{i}'))
    for i in range(1, 4):
        middle = (relays[i],) if i in relays else ()
        words.append((f'open{i}', *middle, f'close{i}'))
    events = sorted({event for word in words for event in word})
    interfaces = set()
    valid = full = 0
    for subset in product((False, True), repeat=len(events)):
        active = {event for event, bit in zip(events, subset) if bit}
        fragments = []
        for word in words:
            indices = [i for i, event in enumerate(word) if event in active]
            if indices and len(indices) != indices[-1] - indices[0] + 1:
                break
            fragments.append([word[i] for i in indices])
        else:
            valid += 1
            reachable = {v: set() for v in active}
            for fragment in fragments:
                for a, b in zip(fragment, fragment[1:]):
                    reachable[a].add(b)
            for v in events:
                if v in active:
                    for targets in reachable.values():
                        if v in targets:
                            targets.update(reachable[v])
            assert all(v not in target for v, target in reachable.items())
            assert 'beta' not in reachable.get('alpha', ()) and 'alpha' not in reachable.get('beta', ())
            if {'start', 'end'} <= active:
                full += 1
                assert active == set(events)
            names = ('start', 'alpha', 'beta', 'end')
            visible = tuple(e for e in names if e in active)
            induced = tuple((a, b) for a in visible for b in visible if b in reachable[a])
            assert all(names.index(a) < names.index(b) for a, b in induced)
            interfaces.add((visible, induced))
    print(f'{valid} realizable event subsets among {2**len(events)}; '
          f'{full} complete seal record; {len(interfaces)} interfaces.')
    return interfaces


def audit(interfaces):
    board = Board(2, 2, [])
    table, _ = compile_boxes(board)
    pairs = tuple(combinations(range(board.n), 2))
    taps = [('alpha', 0, 0), ('beta', 1, 1)]
    checked = 0
    cases = []
    for visible, induced in interfaces:
        ids = {e: i for i, e in enumerate(visible, board.n)}
        handshakes = [(ids[a], ids[b]) for a, b in induced]
        effective = Board(2, 2, [(a, b) for name, a, b in taps if name in ids])
        cases.append((ids, handshakes, effective))
    for roles in product(range(4), repeat=board.n):
        fixed = [table[a, roles[a], b, roles[b]] for a, b in pairs if roles[a] and roles[b]]
        s, t = roles[board.s] == 3, roles[board.t] == 3
        for ids, handshakes, effective in cases:
            if s and t and not {'start', 'end'} <= ids.keys():
                continue
            if s and 'end' in ids and 'start' not in ids or t and 'start' in ids and 'end' not in ids:
                continue
            extra = list(handshakes)
            if s and 'start' in ids:
                extra.append((board.s, ids['start']))
            if t and 'end' in ids:
                extra.append((ids['end'], board.t))
            for name, a, b in taps:
                if name in ids:
                    if roles[a] & 2:
                        extra.append((a, ids[name]))
                    j = len(board.rows) + b
                    if roles[j] & 1:
                        extra.append((ids[name], j))
            assert acyclic_chart(board.n + len(ids), [*fixed, extra]) == effective.guard(roles)
            checked += 1
    print(f'{checked} comparisons of partial-record charts with their effective incidence matrices.')


if __name__ == '__main__':
    audit(tree_records())
