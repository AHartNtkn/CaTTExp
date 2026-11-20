"""Serialize raw tracks into local changes of states one dimension lower."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache, reduce
from itertools import product
from pathlib import Path

from catt import (comp2, disc_tree, fv_tm, infer, maximal_vars, ps_boundary_vars,
                  ps_dim, restrict, src, sub_from, subst_tm, tdim, tdim_tm, tgt,
                  tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_intermediates import (Chart, charts, example, fill_chart,
                                              terms_of_rank)


def temporal(ctx, start, edges):
    if not edges:
        return ident(ctx, start)
    return reduce(lambda a, b: comp2(ctx, tdim_tm(ctx, start), a, b), edges)


def promote(ctx, term, slot, edge):
    """Lift one change through the indicated top-dimensional argument."""
    _, root, ty, args = term
    generic = ('coh', root, ty, tuple(map(v, range(len(root)))))
    new = list(args)
    assert args[slot] == src(ctx, edge)
    new[slot] = tgt(ctx, edge)
    return fill_chart(ctx, Chart(root, generic, args), Chart(root, generic, tuple(new)),
                      [slot], {(args[slot], new[slot]): edge})


def occurrence(term, variable):
    if term[0] == 'v':
        assert term == v(variable)
        return ()
    child, = (j for j, a in enumerate(term[3]) if variable in fv_tm(a))
    return (child,) + occurrence(term[3][child], variable)


def at(ctx, term, address, edge):
    if not address:
        assert term == src(ctx, edge)
        return edge
    i, *rest = address
    return promote(ctx, term, i, at(ctx, term[3][i], rest, edge))


def boundary(ctx, sign, term, rank):
    face, inclusion = restrict(ctx, ps_boundary_vars(ctx, rank, sign))
    ren = [None] * len(ctx)
    for i, x in enumerate(inclusion):
        ren[x[1]] = v(i)
    return face, inclusion, subst_tm(term, ren)


@cache
def serialize(ctx, term):
    """The ordered elementary edges, retaining a cap when the generic ends differ."""
    rank = tdim_tm(ctx, term)-1
    if term[0] == 'v' or ps_dim(term[1]) <= rank:
        return (term,)
    _, root, ty, args = term
    trunk, left, b = boundary(root, '-', ty[2], rank)
    other, right, d = boundary(root, '+', ty[3], rank)
    assert trunk == other and infer(trunk, b) == infer(trunk, d)
    links = {t[2][1]: (k, t[3][1]) for k, t in enumerate(root) if tdim(t) == rank}
    labels = [args[q[1]] for q in left]
    word = []
    for j, (lo, hi) in enumerate(zip(left, right, strict=True)):
        i = lo[1]
        if i == hi[1]:
            continue
        address = occurrence(b, j)
        while i != hi[1]:
            z, i = links[i]
            for edge in serialize(ctx, args[z]):
                state = subst_tm(b, labels)
                word.append(at(ctx, state, address, edge))
                labels[j] = tgt(ctx, edge)
            assert labels[j] == args[i]
    if b != d:
        word.append(subst_tm(head(trunk, b, d), labels))
    state = src(ctx, term)
    for edge in word:
        assert src(ctx, edge) == state
        state = tgt(ctx, edge)
    assert state == tgt(ctx, term)
    return tuple(word)


@cache
def common(ctx, a, b):
    """Find one ground full-chart relation between two parallel terms."""
    if infer(ctx, a) != infer(ctx, b):
        return None
    index = {(c.arity, c.labels, infer(c.arity, c.term)): c for c in charts(ctx, a)}
    for d in charts(ctx, b):
        c = index.get((d.arity, d.labels, infer(d.arity, d.term)))
        if c is not None:
            return subst_tm(head(c.arity, c.term, d.term), c.labels)
    return None


@cache
def elementary(ctx, a, b):
    """All elementary edges, rooted at every rank-preserving occurrence."""
    if infer(ctx, a) != infer(ctx, b):
        return ()
    edges = {}
    for c, d in product(charts(ctx, a), charts(ctx, b)):
        if c.arity == d.arity and c.labels == d.labels and infer(c.arity, c.term) == infer(d.arity, d.term):
            edges[subst_tm(head(c.arity, c.term, d.term), c.labels)] = None
    if a[0] == b[0] == 'coh' and a[:3] == b[:3]:
        for i, ty in enumerate(a[1]):
            if tdim(ty)+1 != tdim_tm(ctx, a):
                continue
            if any(x != y for j, (x, y) in enumerate(zip(a[3], b[3], strict=True)) if i != j):
                continue
            for child in elementary(ctx, a[3][i], b[3][i]):
                edges[promote(ctx, a, i, child)] = None
    return tuple(edges)


def holes(ctx, state, addr=()):
    yield addr, state
    if state[0] == 'coh':
        for i, ty in enumerate(state[1]):
            if tdim(ty)+1 == tdim_tm(ctx, state):
                yield from holes(ctx, state[3][i], addr+(i,))


def plug(term, address, value):
    if not address:
        return value
    i, *rest = address
    args = list(term[3])
    args[i] = plug(args[i], rest, value)
    return (*term[:3], tuple(args))


def path_matrix(ctx, start, goal, extra=()):
    """Return the target vector and finite short-relation matrix on the supplied states."""
    rank = tdim_tm(ctx, start)-1
    first, last = serialize(ctx, start), serialize(ctx, goal)
    endpoints = [pole for edge in (*first, *last) for pole in infer(ctx, edge)[2:]]
    vertices = terms_of_rank(ctx, (*extra, src(ctx, start), tgt(ctx, start), *endpoints), rank)
    edges = {a: [edge for b in vertices for edge in elementary(ctx, a, b)] for a in vertices}
    flat = {e: i for i, e in enumerate(e for a in vertices for e in edges[a])}
    assert all(e in flat for e in (*first, *last))
    # A chart key describes a clique of path relations. A spanning star of
    # each clique suffices; choose its center after restricting to a context.
    words = []
    groups = {}
    for a in vertices:
        paths = [()] + [(e,) for e in edges[a]]
        paths.extend((e,f) for e in edges[a] for f in edges[tgt(ctx,e)])
        for word in paths:
            term = temporal(ctx, a, word)
            index = len(words)
            words.append((a, word))
            for c in charts(ctx, term):
                key = c.arity, c.labels, infer(c.arity, c.term)
                groups.setdefault(key, set()).add(index)

    contexts = {}
    for a in vertices:
        for address, inner in holes(ctx, a):
            contexts[plug(a, address, None), address, infer(ctx, inner)] = a

    def vector(p, q):
        values = [0]*len(flat)
        for e in p:
            values[flat[e]] -= 1
        for e in q:
            values[flat[e]] += 1
        return tuple(values)

    columns = {}
    for (_, address, ty), frame in contexts.items():
        states = {a: plug(frame, address, a) for a in vertices if infer(ctx, a) == ty}
        states = {a: b for a, b in states.items() if b in edges}
        images = {e: at(ctx, b, address, e) for a, b in states.items()
                  for e in edges[a] if tgt(ctx, e) in states}
        assert all(e in flat for e in images.values())
        transported = {i: tuple(images[e] for e in word)
                       for i, (a, word) in enumerate(words) if a in states and all(e in images for e in word)}
        for group in groups.values():
            indices = sorted(group & transported.keys())
            if len(indices) < 2:
                continue
            base = transported[indices[0]]
            for i in indices[1:]:
                col = vector(base, transported[i])
                if any(col):
                    columns[col] = None
    return vector(first, last), tuple(columns)


def integer_span(target, columns):
    """Integer echelon reduction by unimodular column operations."""
    basis = {}
    for values in columns:
        v = list(values)
        for i in range(len(v)):
            while v[i]:
                if i not in basis:
                    basis[i] = v if v[i] > 0 else [-x for x in v]
                    break
                b = basis[i]
                q = v[i] // b[i]
                v = [x-q*y for x, y in zip(v, b, strict=True)]
                if v[i]:
                    basis[i], v = v, b
            else:
                continue
            break
    rest = list(target)
    for i in range(len(rest)):
        if rest[i]:
            if i not in basis or rest[i] % basis[i][i]:
                return False
            q = rest[i] // basis[i][i]
            rest = [x-q*y for x, y in zip(rest, basis[i], strict=True)]
    return True


def promote_relation(ctx, state, slot, proof):
    """Transport a track between arrows through a fixed argument occurrence."""
    edge, end_edge = infer(ctx, proof)[2:]
    first = promote(ctx, state, slot, edge)
    last = promote(ctx, state, slot, end_edge)
    # The first promotion introduced one maximal arrow variable at the changed slot.
    root, args = first[1], first[3]
    changed = [i for i, ty in enumerate(root) if tdim(ty)+1 == tdim_tm(ctx, edge)]
    k, = changed
    assert args[k] == edge and last[3][k] == end_edge
    return promote(ctx, first, k, proof)


def check(rank, emitter):
    ctx, u, goal, _, _ = example(rank)
    a, b = serialize(ctx, u), serialize(ctx, goal)
    start = src(ctx, u)
    assert len(a) == 1 and len(b) == 2
    assert all(e in elementary(ctx, src(ctx, e), tgt(ctx, e)) for e in (*a, *b))
    states = terms_of_rank(ctx, (u, goal), rank-1)
    assert all(src(ctx, e) in states and tgt(ctx, e) in states for e in (*a, *b))
    # Detect a common outer whisker and read its two inner elementary changes.
    ranked = [j for j, t in enumerate(start[1]) if tdim(t)+1 == rank-1]
    for slot in ranked:
        inner_start = start[3][slot]
        inner_states = [t for t in states if infer(ctx, t) == infer(ctx, inner_start)]
        for mid in inner_states:
            for f, g in product(elementary(ctx, inner_start, mid), elementary(ctx, mid, inner_start)):
                if promote(ctx, start, slot, f) == b[0] and promote(ctx, tgt(ctx, b[0]), slot, g) == b[1]:
                    return check_relations(ctx, u, goal, a, b, start, slot, f, g, emitter)
    raise AssertionError('no inner path in the lower-state graph')


def check_relations(ctx, u, goal, a, b, start, slot, f, g, emitter):
    # The rooted relation has length one against two. Lift it through the
    # occurrence, then distribute its right-hand path across that occurrence.
    inner = src(ctx, f)
    pair = temporal(ctx, inner, (f, g))
    for cap in elementary(ctx, inner, inner):
        lifted = promote(ctx, start, slot, cap)
        left = common(ctx, a[0], lifted)
        relation = common(ctx, cap, pair)
        if left is not None and relation is not None:
            break
    else:
        raise AssertionError('no elementary detour at the fixed state')
    middle = promote_relation(ctx, start, slot, relation)
    last = common(ctx, tgt(ctx, middle), temporal(ctx, start, b))
    assert last is not None
    tracks = [left, middle, last]
    if u != a[0]:
        tracks.insert(0, common(ctx, u, a[0]))
    written_end = temporal(ctx, start, b)
    if written_end != goal:
        tracks.append(common(ctx, written_end, goal))
    assert all(track is not None for track in tracks)
    witness = temporal(ctx, u, tracks)
    assert infer(ctx, witness)[2:] == (u, goal)
    if emitter:
        emitter.check_type('statePaths', ctx, witness, infer(ctx, witness))
    print(f'Rank {tdim_tm(ctx, u)}: reconstructed the comparison from lower-state edges.', flush=True)


def check_grid(rank):
    """Sweep two independent columns, changing the generic writing across the sweep."""
    r = rank-1
    trunk = tree_ctx(string_tree(0, [r, r]))
    slots = maximal_vars(trunk)
    plain = ucomp(trunk)
    disk = tree_ctx(disc_tree(r))
    top = v(len(disk)-1)
    wrapped = subst_tm(head(disk, src(disk, top), tgt(disk, top)),
                       sub_from(disk, trunk, {top[1]: plain}))
    counts = (2, 3)
    arity = tree_ctx(tuple(string_tree(r, [rank]*length)[0] for length in counts))
    maxima = list(map(v, maximal_vars(arity)))
    columns = (maxima[:2], maxima[2:])
    starts = [src(arity, edges[0]) for edges in columns]

    def labels(pos):
        values = [tgt(arity, edges[i-1]) if i else start
                  for i, edges, start in zip(pos, columns, starts, strict=True)]
        return sub_from(trunk, arity, dict(zip(slots, values, strict=True)))

    def cap(pos):
        return subst_tm(head(trunk, plain, wrapped), labels(pos))

    def step(frame, pos, axis):
        state = subst_tm(frame, labels(pos))
        return at(arity, state, occurrence(frame, slots[axis]), columns[axis][pos[axis]])

    def route(frame, pos, axes):
        pos = list(pos)
        word = []
        for axis in axes:
            word.append(step(frame, pos, axis))
            pos[axis] += 1
        return word

    def difference(word, other):
        c = Counter(other)
        c.subtract(word)
        return c

    total = Counter()
    def square(word, other):
        base = src(arity, word[0])
        a, b = temporal(arity, base, word), temporal(arity, base, other)
        assert common(arity, a, b) is not None
        total.update(difference(word, other))

    start = (0, 0)
    ab, ba = [0, 0, 1, 1, 1], [1, 1, 1, 0, 0]
    for i in range(counts[0]):
        for j in range(counts[1]):
            square(route(plain, (i,j), (0,1)), route(plain, (i,j), (1,0)))
    pos = [0, 0]
    for axis in ba:
        old = pos.copy()
        pos[axis] += 1
        square([step(plain, old, axis), cap(pos)], [cap(old), step(wrapped, old, axis)])
    first = route(plain, start, ab) + [cap(counts)]
    second = [cap(start)] + route(wrapped, start, ba)
    assert total == difference(first, second)
    generic = head(arity, subst_tm(plain, labels(start)), subst_tm(wrapped, labels(counts)))
    assert serialize(arity, generic) == tuple(first)
    print(f'Rank {rank}: six exchange squares and five writing-change squares agree with the full boundary.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rank', type=int, default=4)
    parser.add_argument('--agda', type=Path)
    config = parser.parse_args()
    if config.rank < 4:
        parser.error('choose a second or higher identity (rank at least four)')
    emitter = Emitter() if config.agda else None
    ctx, a, b, *_ = example(4)
    target, cols = path_matrix(ctx, a, b)
    assert any(target) and integer_span(target, cols)
    assert not integer_span((1, 0), [(2, 0), (0, 1)])
    assert integer_span((1, 1), [(2, 0), (3, 1)])
    print(f'Second identity: integer span verified with {len(target)} named edges and {len(cols)} columns.', flush=True)
    check_grid(2)
    check_grid(4)
    for rank in range(4, config.rank+1):
        check(rank, emitter if rank == config.rank else None)
    if emitter:
        config.agda.write_text(emitter.module(config.agda.stem, 'Local relations on paths of lower-rank states.'))
