"""Compare sealed word computations with the spatial charts of the guarded switch."""

from itertools import combinations, product

from homotopy_polygraph_guarded_boxes import Board, acyclic_chart, compile_boxes


# Both controls read an entire token between u and v. The two inner
# types allow repeated counter letters but at most one instruction head.
TYPES = {'Q': 'uv', 'U': 'uv', '[': 'up', ']': 'tv', 'x': 'pp', 'y': 'tt',
         **{h: 'pt' for h in 'ijkah'}}
START = ('Q', '[i]')
FINISH = ('[h]', 'U')
ACCEPT = [START, ('i', 'xj'), ('j', 'ky'), ('xk', 'a'), ('ay', 'h'), FINISH]
LOOP = [START, ('i', 'j'), ('j', 'i'), FINISH]


def poles(word):
    edges = [TYPES[c] for c in word]
    assert all(a[1] == b[0] for a, b in zip(edges, edges[1:]))
    return edges[0][0] + edges[-1][1]


def run(word, rules):
    """Follow literal subword matches to a terminal state or the first repetition."""
    history = []
    while word not in history:
        history.append(word)
        matches = [(word[:i] + rhs + word[i + len(lhs):])
                   for lhs, rhs in rules for i in range(len(word)) if word.startswith(lhs, i)]
        assert len(matches) <= 1
        if not matches:
            return history
        after, = matches
        assert poles(word) == poles(after)
        word = after
    return history + [word]


def check(board):
    table, _ = compile_boxes(board)
    # compile_boxes chooses a new pair-private site at height S for this read pair.
    marked = Board(len(board.rows), len(board.cols),
                   [(a, b - len(board.rows)) for a, b in board.missing])
    marked.arcs.append((board.s, 3, board.t, 3))
    with_port, _ = compile_boxes(marked)
    pairs = tuple(combinations(range(board.n), 2))

    accepting = run('Q', ACCEPT)
    looping = run('Q', LOOP)
    assert accepting == ['Q', '[i]', '[xj]', '[xky]', '[ay]', '[h]', 'U']
    assert looping == ['Q', '[i]', '[j]', '[i]']
    assert run('[h]', LOOP) == ['[h]', 'U']
    # Include partial records starting or ending inside a tape. Repeated head
    # operations in a looping record are separate spatial occurrences.
    traces = {tuple(words[i:j]) for words in [accepting, looping, run('[h]', LOOP)]
              for i in range(len(words)) for j in range(i + 1, len(words) + 1)}
    read_patterns = set()
    for words in traces:
        for use_q, use_u in product([False, True], repeat=2):
            possibilities = [tuple(k for k, word in enumerate(words) if word == token)
                             if needed else (None,)
                             for token, needed in [('Q', use_q), ('U', use_u)]]
            placements = list(product(*possibilities))
            assert len(placements) == int((not use_q or words[0] == 'Q')
                                          and (not use_u or words[-1] == 'U'))
            if placements and use_q and use_u:
                assert words == tuple(accepting)
            for q, u in placements:
                read_patterns.add((len(words) - 1, q, u))

    tested = 0
    for roles in product(range(4), repeat=board.n):
        active = [(i, roles[i], j, roles[j]) for i, j in pairs if roles[i] and roles[j]]
        spatial = tuple(table[key] for key in active)
        ordinary = acyclic_chart(board.n, spatial)
        assert ordinary == board.guard(roles)
        assert acyclic_chart(board.n, (with_port[key] for key in active)) == ordinary
        for length, q, u in read_patterns:
            if (roles[board.s] == 3, roles[board.t] == 3) != (q is not None, u is not None):
                continue
            # Place actual tape transitions on their chain, then each marker
            # at its observed gap. Projecting the chain must preserve legality.
            chain = range(board.n, board.n + length)
            edges = list(zip(chain, chain[1:]))
            for actor, gap in [(board.s, q), (board.t, u)]:
                if gap is None:
                    continue
                if gap > 0:
                    edges.append((chain[gap - 1], actor))
                if gap < length:
                    edges.append((actor, chain[gap]))
            assert acyclic_chart(board.n + length, (*spatial, edges)) == ordinary
            tested += 1
    print(f'{len(traces)} sealed or partial records, {4**board.n} cubes, '
          f'{tested} comparisons with the explicit instruction chain.')


if __name__ == '__main__':
    check(Board(3, 3, [(0, 0), (1, 1), (2, 2)]))
