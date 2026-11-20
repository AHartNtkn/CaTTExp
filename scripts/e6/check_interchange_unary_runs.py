"""Test the one-slot contractions and their handling of shared chronological words."""

from dataclasses import replace
from itertools import product

from interchange_shared_whiskers import Words
from interchange_unary_runs import Cylinder, PaddedRuns, Runs, UnaryRuns
from interchange_two_moving import histories, moves, POSITIONS, SUPPORT


def atom(record):
    return Runs(record, 0, None)


def word(arena, values):
    result = 0
    for value in values:
        result = arena.join(result, value)
    return result


def check_sweeps():
    # The two moving 4-loops are the earlier and later weight-one loops of K63.
    # Collapsing the fresh stationary span reads each pure insertion as its
    # original moving word. Each comparison here is inside one such pure lane.
    lower = Words()
    solver = UnaryRuns(lower.join, lower.equal)
    count = 0
    for size in range(1, 7):
        for letters in product(range(2), repeat=size):
            moving, left, right = [[lower.letter(base+i) for i in letters] for base in (0, 2, 4)]

            def piece(i, j):
                return Cylinder('outer', 'w', 'w', word(lower, left[:i]),
                                word(lower, moving[i:j]), word(lower, right[j:]),
                                word(lower, left[i:j]), word(lower, right[i:j]))

            direct = atom(piece(0, size))
            for mask in range(1 << (size-1)):
                cuts = [0] + [i for i in range(1, size) if mask & (1 << (i-1))] + [size]
                path = None
                for i, j in zip(cuts, cuts[1:]):
                    path = solver.product(path, atom(piece(i, j)))
                assert path.last is None and solver.same(path.first, direct.first)
                count += 1
    print(f"{count} typed moving subdivisions on the two-loop vocabulary agree with the whole cylinder.")

    # A cut at the center of a shared moving word with 2^100 periods.
    x, l, r = [lower.join(lower.letter(i), lower.letter(i+1)) for i in (0, 2, 4)]
    for _ in range(99):
        x, l, r = (lower.join(z, z) for z in (x, l, r))
    a = Cylinder('outer', 'w', 'w', 0, x, r, l, r)
    b = Cylinder('outer', 'w', 'w', l, x, 0, l, r)
    wide = Cylinder('outer', 'w', 'w', 0, lower.join(x,x), 0, lower.join(l,l), lower.join(r,r))
    assert solver.equal(solver.product(atom(a), atom(b)), atom(wide))
    print("Split and direct cylinders on 2^100 periods have equal normal records.")


def check_partial_products():
    # A noncancellative category for the record algorithm. Length-two words
    # xy and yx become equal after adjoining both prescribed outside guards.
    # This tests the two pad equations without relying on cancellation.
    def canon(s):
        return s.replace('ayxb', 'axyb')
    def join(a,b):
        return canon(a+b)
    solver = UnaryRuns(join, lambda a,b: canon(a) == canon(b))
    a = Cylinder(0,0,0,'ayx','b','bb','b','b')
    b = Cylinder(0,0,0,'axyb','b','b','b','b')
    c = Cylinder(0,0,0,'ayxbb','b','','b','b')
    d = Cylinder(1,0,0,'','x','','x','x')
    assert solver.merge(a,b) is not None and solver.merge(b,c) is not None
    assert solver.same(solver.merge(solver.merge(a,b),c), solver.merge(a,solver.merge(b,c)))
    assert solver.merge(a,c) is None and solver.merge(c,d) is None

    def explicit(records):
        # Exhaust the binary contraction choices independently of SLP bracketing.
        pending, seen, ends = [records], {records}, set()
        while pending:
            w = pending.pop()
            children = []
            for i, (left, right) in enumerate(zip(w, w[1:])):
                merged = solver.merge(left, right)
                if merged is not None:
                    children.append(w[:i] + (merged,) + w[i+2:])
            if not children:
                ends.add(w)
            for v in children:
                if v not in seen:
                    seen.add(v)
                    pending.append(v)
        assert len(ends) == 1
        return ends.pop()

    count = 0
    for records in product((a,b,c,d), repeat=5):
        expected = explicit(records)
        def fold(seq):
            if len(seq) == 1:
                return atom(seq[0])
            i = len(seq)//2
            return solver.product(fold(seq[:i]), fold(seq[i:]))
        normal = solver.code(fold(records))
        assert solver.words.equal(normal, word(solver.words, [solver.token(v) for v in expected]))
        count += 1
    block = solver.product(atom(a), atom(d))
    power = block
    for _ in range(90):
        power = solver.product(power, power)
    assert solver.words.length[solver.code(power)] == 2**91
    assert not solver.equal(solver.product(power, atom(d)), solver.product(power, atom(a)))
    print(f"{count} bracketed record words agree with exhaustive contractions, "
          "and a changed block after 2^90 periods is detected.")


def check_deferred_pads():
    # Two distinct lower spellings with a common left equalizer.
    def join(a, b):
        return (a+b).replace('ayxb', 'axyb')
    solver = UnaryRuns(join, lambda a, b: join('', a) == join('', b))
    paths = PaddedRuns(solver, '')
    a = Cylinder(0, 0, 0, 'yx', 'b', 'b', 'b', 'b')
    b = Cylinder(0, 0, 0, 'xyb', 'b', '', 'b', 'b')
    first, second = paths.atom(a, 1), paths.atom(b, 1)
    two = paths.join(first, second)
    wide = paths.atom(Cylinder(0, 0, 0, 'yx', 'bb', '', 'bb', 'bb'), 2)
    x = paths.pad('a', two, '')
    y = paths.pad('a', wide, '')
    assert paths.distinguishes(two, wide, 1)
    assert not paths.boundary(x, 1)
    # Compare all witnesses against explicit normalization, including intervals
    # spanning several blocks and a product containing different intrinsic tags.
    records = {first: [a], second: [b], two: [a,b], wide: [paths.rules[wide][1]]}
    for node in list(records):
        for pre, post in (('a',''), ('','c'), ('a','c')):
            child = paths.pad(pre, node, post)
            records[child] = [replace(r, prefix=join(pre, r.prefix), suffix=join(r.suffix, post))
                              for r in records[node]]
    d = replace(b, tag=1, moving='c')
    last = paths.atom(d, 1)
    for node in list(records):
        records[paths.join(node, last)] = records[node] + [d]
    def code(raw):
        value = None
        for r in raw:
            value = solver.product(value, atom(r))
        return solver.code(value)
    codes = {node: code(raw) for node, raw in records.items()}
    checked = 0
    for u, v in product(records, repeat=2):
        if paths.weights[u] != paths.weights[v]:
            continue
        end = paths.weights[u]
        witnesses = any(paths.distinguishes(u, v, i, j)
                        for i in range(end+1) for j in [None, *range(i+1, end+1)])
        assert witnesses != solver.words.equal(codes[u], codes[v])
        checked += 1
    assert not any(paths.distinguishes(x, y, i, j) for i in range(3) for j in (None, 1, 2))
    print(f"{checked} padded record pairs checked exhaustively, including a seam "
          "that merges only under its exterior pad.")


def check_shared_sweep():
    lower = Words()
    solver = UnaryRuns(lower.join, lower.equal)
    paths = PaddedRuns(solver, 0)
    z, l, r = [lower.letter(i) for i in range(3)]
    root = paths.atom(Cylinder('outer', 'w', 'w', 0, z, 0, l, r), 1)
    for _ in range(70):
        root = paths.join(paths.pad(0, root, r), paths.pad(l, root, 0))
        z, l, r = (lower.join(v, v) for v in (z, l, r))
    end = 1 << 70
    direct = paths.atom(Cylinder('outer', 'w', 'w', 0, z, 0, l, r), end)
    for i in (1, end//3, end//2, end-1):
        assert not paths.boundary(root, i) and not paths.distinguishes(root, direct, i)
        record, offset = paths.at(root, i)
        assert offset == 0
        assert lower.length[record.prefix] == i and lower.length[record.suffix] == end-1-i
    assert not paths.distinguishes(root, direct, 0, end)
    print("Read interior seams and the whole moving product of a genuine "
          "2^70-step shared sweep against the direct cylinder.")


def check_four_step_bound():
    def scores(history):
        completed = 0
        placed = 0
        moment = 0
        for i, event in enumerate(history):
            state = POSITIONS[completed]
            pos = min(state.index(slot) for slot in SUPPORT[event])
            moment += (len(history)-i-1)*pos
            if event in 'ab':
                completed += 1
            elif (event == 'X' and completed == 0) or (event == 'Y' and completed < 2):
                placed += 1
        return placed, moment

    counts = {'r': 0, 'i': 0}
    for state in histories(2, 3):
        before, moment = scores(state)
        for move in moves(state):
            after, next_moment = scores(move.target(state))
            if move.kind == 'r':
                assert after > before
            else:
                assert after == before and next_moment < moment
            counts[move.kind] += 1
    print(f"Four-dimensional measure checked on {counts['r']} moving naturalities "
          f"and {counts['i']} positional exchanges.")


if __name__ == '__main__':
    check_sweeps()
    check_partial_products()
    check_deferred_pads()
    check_shared_sweep()
    check_four_step_bound()
