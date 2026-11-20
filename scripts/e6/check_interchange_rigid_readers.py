"""Check finite-reader lifting on a noncancellative category and a doubled grid."""

from functools import reduce
from itertools import combinations, permutations
from math import comb

from check_interchange_grid_contractions import four_cells
from check_interchange_grid_five import refinements
from check_interchange_grid_windows import convert
from check_interchange_rigid_group import letters
from grid_loop_words import classes, states
from interchange_grid_five import GridReader
from interchange_grid_windows import merge, residual, start as initial_reader
from interchange_rigid_readers import Occurrences, ReaderCodes
from interchange_shared_whiskers import Words


class Grammar(list):
    def add(self, *rule):
        self.append(rule)
        return len(self)-1


class IntervalReader:
    """Finite rank-three path table for the two-by-two crossing interval."""
    def __init__(self, reverse):
        self.reverse = reverse
        self.output = Words()
        self.names = {}

    def run(self, state, word):
        state = state + (word[::-1] if self.reverse else word)
        return state, 0

    def finish(self, state):
        if self.reverse:
            state = state[::-1]
        if state == 'acbd':
            state = 'abcd'
        return self.output.letter(self.names.setdefault(state, len(self.names)))


def check_two_coordinates():
    # Use a test tower with loop heads on the two extremal single edges.
    # Its base is the actual interval; the two loop heads are formal here.
    rules = Grammar()
    first = rules.add('head', 4, 'on a')
    last = rules.add('head', 4, 'on d')
    a = rules.add('base', '', first, 'bcd')
    b = rules.add('base', '', first, 'cbd')
    c = rules.add('base', 'abc', last, '')
    d = rules.add('base', 'acb', last, '')
    readers = [ReaderCodes(rules, IntervalReader(rev), 3, rev) for rev in (False, True)]
    assert [reader.equal_coordinate(a, b, '') for reader in readers] == [True, False]
    assert [reader.equal_coordinate(c, d, '') for reader in readers] == [False, True]
    print("Each one-sided comparison misses a distinct pair of parallel paths in the finite-base tower.")


def check_grid():
    width = 4
    all_letters, parents = four_cells(width)
    start = tuple((r,k) for k in (4,3,2,1) for r in (0,1))
    table = classes((width,width), (0,0))
    loops = [w for w in all_letters if
             table[w[0]+w[1]+w[2]+w[3]] == table[w[0]+w[2]+w[1]+w[3]] == table[start]]
    wide = next(w for w in sorted(loops) if len(w[1]) == len(w[2]) == 2)
    splits = {}
    for pair, parent in parents.items():
        splits.setdefault(parent, []).append(pair)
    raw, tiles, ids = Words(), [], {}

    def word(seq):
        result = 0
        for tile in seq:
            if tile not in ids:
                ids[tile] = len(tiles)
                tiles.append(tile)
            result = raw.join(result, raw.letter(ids[tile]))
        return result

    def corner(pos):
        pre, post = start[:pos], start[pos+2:]
        f, g = (start[pos+1],), (start[pos],)
        mid = states((4,4), pre)[-1]
        end = states(mid, g+f)[-1]
        norm = classes((4,4), mid)[pre], f, g, classes(end, (0,0))[post]
        assert norm in loops
        return word((convert(norm),))

    e, l = corner(1), corner(5)
    u, v = raw.join(l, e), raw.join(e, l)
    wide_a, wide_b = map(word, refinements(wide, splits))
    rules = Grammar()
    empty = rules.add('empty')
    d = rules.add('head', 5, 'D')
    h = rules.add('head', 6, 'square on D,D')
    readers = []
    for rev in (False, True):
        stream = GridReader(width, (0,0), tiles, raw, Words(), rev)
        sa, a = stream.run((), wide_a)
        sb, b = stream.run((), wide_b)
        assert sa != sb
        assert stream.output.equal(stream.output.join(a, stream.finish(sa)),
                                   stream.output.join(b, stream.finish(sb)))
        readers.append(ReaderCodes(rules, stream, 4, rev))

    def same(x, y):
        return all(r.equal_coordinate(x, y) for r in readers)

    def base(a, x, b):
        return rules.add('base', a, x, b)

    def join(x, y):
        return rules.add('join', x, y)

    def fold(sites):
        return reduce(raw.join, sites, 0)

    def six_step(order, pos):
        # A 6-square switches two neighbouring sites updated consecutively.
        sites = [u]*len(order)
        moves = []
        for site in order:
            moves.append(base(fold(sites[:site]), d, fold(sites[site+1:])))
            sites[site] = v
        lo = order[pos+1]
        assert order[pos] == lo+1
        old = [v if i in order[:pos] else u for i in range(len(order))]
        lower = base(fold(old[:lo]), h, fold(old[lo+2:]))
        pre = reduce(join, moves[:pos], empty)
        post = reduce(join, moves[pos+2:], empty)
        step = rules.add('right', rules.add('left', pre, lower), post)
        return step, (tuple(order[:pos]), lo, tuple(order[pos+2:]))

    count = 0
    for n in range(2, 6):
        for start_order in permutations(range(n)):
            by_code = {}
            pending = [(start_order, empty, ())]
            while pending:
                order, current, records = pending.pop()
                key = tuple(letters(r.group, r.value(current)) for r in readers)
                assert key not in by_code or by_code[key] == records
                by_code[key] = records
                count += 1
                for i, (a,b) in enumerate(zip(order, order[1:])):
                    if a == b+1:
                        step, rec = six_step(order, i)
                        after = order[:i] + (b,a) + order[i+2:]
                        pending.append((after, join(current, step), records + (rec,)))
    # Two parallel orders of positive six-dimensional steps at disjoint pairs.
    begin = (1,0,3,2)
    before = join(six_step(begin, 0)[0], six_step((0,1,3,2), 2)[0])
    after = join(six_step(begin, 2)[0], six_step((1,0,2,3), 0)[0])
    assert same(base(wide_a, before, wide_b), base(wide_b, before, wide_a))
    assert not same(base(wide_a, before, wide_b), base(wide_b, after, wide_a))

    # Distribute a noncancellative base context through a 5-pad on H.
    pre = base(0, d, raw.join(u,u))
    core = base(v, h, 0)
    direct = base(wide_a, rules.add('left', pre, core), wide_a)
    distributed = rules.add('left', base(wide_b, pre, wide_b),
                            base(raw.join(wide_b,v), h, wide_b))
    assert same(direct, distributed)
    # Descend first through the 6-record, then into its immediate left
    # 5-pad. Both sides of D include the inherited nontrivial 4-context.
    indexed = Occurrences(rules, 4)

    def lower_fields(root):
        name, actions = indexed.occurrence([(root, ())], 0)
        assert name == (6, 'square on D,D')
        field = indexed.field(actions, 5, 'left')
        name, actions = indexed.occurrence(field, 0)
        assert name == (5, 'D')
        result = []
        for side in ('left', 'right'):
            terms = indexed.field(actions, 4, side)
            assert all(not context for _, context in terms)
            result.append(fold(pad for pad, _ in terms))
        return result

    def complete(reader, node):
        state, output = reader.run((), node)
        return reader.output.join(output, reader.finish(state))

    for root in (direct, distributed):
        fields = lower_fields(root)
        for r, actual, expected in zip(readers, fields, (wide_b, raw.join(raw.join(u,u), wide_b))):
            reader = r.reader
            assert reader.output.equal(complete(reader, actual), complete(reader, expected))
    # Reuse the same shared input across long 5-paths with different cuts.
    sweep = d
    for i in range(8):
        if i % 2 == 0:
            old, p, q = sweep, u, v
        sweep = join(base(0, sweep, u), base(v, sweep, 0))
        if i % 2:
            pieces = [base(fold([q]*j), old, fold([p]*(3-j))) for j in range(4)]
            quarter = reduce(join, pieces)
            assert same(base(wide_a, sweep, wide_b), base(wide_b, quarter, wide_a))
        u, v = raw.join(u,u), raw.join(v,v)
    print(f"{count} six-dimensional paths agree with named-site records. Two parallel batch orders are distinct.")
    print("Different live reader states give equal padded six-cells; binary and quaternary sweeps agree through 256 sites.")


def check_nested_selection():
    # Formal loop heads: at each stage the new head is a loop on the
    # appropriate iterated identity at the previous loop's target.
    rules = Grammar()
    levels = 48
    ranks = [4 + (1 << j) for j in range(levels)]
    value = rules.add('head', ranks[0], 0)
    for j in range(1, levels):
        pad = value
        for _ in range(32):
            pad = rules.add('join', pad, pad)
        head = rules.add('head', ranks[j], j)
        value = rules.add('base', ('left',j), rules.add('left', pad, head), ('right',j))
    indexed = Occurrences(rules, 4)
    field, index = [(value, ())], 0
    for j in reversed(range(levels)):
        name, actions = indexed.occurrence(field, index)
        assert name == (ranks[j],j)
        if j:
            field = indexed.field(actions, ranks[j-1], 'left')
            assert sum(indexed.count[node] for node, _ in field) == 1 << 32
            index = (1 << 32)-1
    for side in ('left','right'):
        result = [pad for pad, _ in indexed.field(actions, 4, side)]
        order = reversed(range(1, levels)) if side == 'left' else range(1, levels)
        assert result == [(side,j) for j in order]
    print("Selected a leaf through 48 sparse ranks and 47 shared pads of length 2^32.")


def check_state_bound():
    ctx = initial_reader(0)

    def normalize(word):
        stack = []
        for tile in word:
            stack.append(tile)
            while len(stack) >= 2:
                parent = merge(*stack[-2:], ctx, ctx)
                if parent is None:
                    break
                stack[-2:] = [parent]
        return tuple((residual(ctx, t.pre), t.f, t.g, residual(ctx, t.revpost)) for t in stack)

    total = 0
    for k in range(1, 6):
        m = k+1
        width = 2*m+2
        f = tuple((0,i) for i in range(m, 0, -1))
        g = tuple((1,i) for i in range(2*m, m, -1))
        spare = ((0,width),(1,width),(0,width-1),(1,width-1))
        pre = spare + tuple((0,i) for i in range(2*m, m, -1))
        post = tuple((1,i) for i in range(m, 0, -1))
        start = pre+g+f+post
        full = pre+f+g+post
        assert states((width,width), start)[-1] == (0,0)
        assert states((width,width), full)[-1] == (0,0)

        def exchange(w, left, right):
            j = w.index(right)
            assert w[j+1] == left
            tile = convert((w[:j], (left,), (right,), w[j+2:]))
            after = w[:j]+(left,right)+w[j+2:]
            assert states((width,width), after)[-1] == (0,0)
            return tile, after

        def loop(w):
            tile, after = exchange(w, spare[2], spare[1])
            # The common two-column K15 rectangle identifies the new 3-path.
            assert residual(ctx, ''.join('ud'[row] for row,_ in w)) == residual(
                ctx, ''.join('ud'[row] for row,_ in after))
            return tile

        distinguished, accepted, continuations = set(), set(), set()
        for horizontal in combinations(range(2*k), k):
            w, atoms = start, []
            i, j = 0, len(g)
            for turn in range(2*k):
                if turn in horizontal:
                    pairs = [(f[i],b) for b in reversed(g[:j])]
                    i += 1
                else:
                    j -= 1
                    pairs = [(a,g[j]) for a in f[i:]]
                for a,b in pairs:
                    tile, w = exchange(w,a,b)
                    atoms.append(tile)
            assert len(atoms) == m*m-1
            end, after = exchange(w, f[-1], g[0])
            assert after == full
            at_cut, at_end = loop(w), loop(full)
            continuations.add((end, at_cut, at_end))
            accepted.add(normalize(atoms+[end, at_end]))
            distinguished.add(normalize(atoms+[at_cut, end]))
        assert len(continuations) == len(accepted) == 1
        assert len(distinguished) == comb(2*k,k)
        total += len(distinguished)
    print(f"{total} typed prefixes satisfy both continuation tests through width 14, with 252 distinct outputs at that width.")


if __name__ == '__main__':
    check_two_coordinates()
    check_grid()
    check_nested_selection()
    check_state_bound()
