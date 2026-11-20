"""Validate local normal tiles and their finite-context readers on two-row grids."""

from collections import defaultdict
from itertools import combinations_with_replacement
from random import Random

from check_interchange_grid_contractions import four_cells
from grid_loop_words import classes
from interchange_grid_windows import Expressions, Tile, covering, equal, feed, read_coordinate, residual, start, units


def rows(events):
    return "".join("ud"[i] for i, _ in events)


def reverse(word):
    return word[::-1].translate(str.maketrans("ud", "du"))


def convert(record):
    pre, f, g, post = record
    return Tile(rows(pre), tuple(b for _, b in f), tuple(b for _, b in g), reverse(rows(post)))


def check_readers(n):
    shuffles = list(combinations_with_replacement(range(n+1), 2))
    count = 0
    for x in shuffles:
        for y in shuffles:
            if any(a < b for a, b in zip(x, y)):
                continue
            names = {}
            for raw, rep in classes(x, y).items():
                w = rows(raw)
                h = x[1]-x[0]
                left = residual(start(h), w)
                right = residual(start(y[1]-y[0]), reverse(w))
                assert reverse(left) == right
                assert names.setdefault(left, rep) == rep
                for cut in range(len(w)+1):
                    for k in range(len(w)+1):
                        p = feed(start(h), w[:cut], k)
                        assert read_coordinate(p, w[cut:], k) == left[k:k+1]
                        count += 1
            assert len(set(names.values())) == len(names)
    print(f"Forward and reverse pad readers match the contextual classes; {count} split-coordinate checks.")


def check_merges(n):
    letters, parents = four_cells(n)
    data = {w: convert(w) for w in letters}
    ctx = start(0)

    def name(t):
        return residual(ctx, t.pre), t.f, t.g, residual(ctx, t.revpost)

    for (a, b), wide in parents.items():
        atoms = tuple(units(data[a])) + tuple(units(data[b]))
        for i in range(len(atoms)):
            actual, offset = covering(atoms, i, ctx, ctx)
            assert offset == i and name(actual) == name(data[wide])
    print(f"Compared every unit position in {len(parents)} genuine contextual binary subdivisions.")


def check_locality(n):
    letters, parents = four_cells(n)
    top = classes((n, n), (0, 0))
    outgoing = defaultdict(list)
    for t in sorted(letters):
        p, f, g, q = t
        if len(f) == len(g) == 1:
            outgoing[top[p+g+f+q]].append((t, top[p+f+g+q]))
    rng = Random(711)
    checked = 0
    radius = n*n-1
    for _ in range(12):
        state = rng.choice(list(outgoing))
        raw, stack = [], []
        for _ in range(90):
            if not outgoing[state]:
                break
            t, state = rng.choice(outgoing[state])
            raw.append(convert(t))
            stack.append(t)
            while len(stack) >= 2 and tuple(stack[-2:]) in parents:
                stack[-2:] = [parents[tuple(stack[-2:])]]
        pos = 0
        for t in stack:
            target = convert(t)
            for offset in range(target.area):
                lo, hi = max(0, pos-radius), min(len(raw), pos+radius+1)
                result, local_offset = covering(raw[lo:hi], pos-lo, start(0), start(0))
                assert (result.f, result.g, local_offset) == (target.f, target.g, offset)
                for x, y in ((result.pre, target.pre), (result.revpost, target.revpost)):
                    assert residual(start(0), x) == residual(start(0), y)
                pos += 1
                checked += 1
    print(f"{checked} local records agree with full independent contractions on typed walks.")


def check_terms():
    n = 4
    letters, parents = four_cells(n)
    top = classes((n, n), (0, 0))

    def boundary(w):
        p, f, g, q = w
        return top[p+g+f+q], top[p+f+g+q]

    a, b = next(pair for pair, wide in parents.items()
                if len(wide[1]) == len(wide[2]) == 2 and boundary(wide)[0] == boundary(wide)[1])
    wide = parents[a, b]
    base = boundary(wide)[0]
    other = next(w for w in sorted(letters) if w != wide and boundary(w) == (base, base)
                 and len(w[1])*len(w[2]) == 1)
    raw = Expressions()

    def lazy(w):
        # Expose the actual prefixes/suffixes as shared structural nodes.
        t = convert(w)
        return raw.pad(t.pre, raw.tile(Tile("", t.f, t.g, "")), t.revpost)

    expected = raw.tile(convert(wide))
    pieces = raw.cat(lazy(a), lazy(b))
    # The two loop powers have equal area, so the difference requires a record check.
    changed = lazy(other)
    for _ in range(2):
        changed = raw.cat(changed, changed)
    assert not equal(raw, expected, changed, n, 0, 0)
    power = expected
    for _ in range(24):
        power = raw.cat(power, power)
    first = raw.cat(power, pieces)
    second = raw.cat(power, expected)
    wrong = raw.cat(power, changed)
    assert equal(raw, first, second, n, 0, 0)
    assert not equal(raw, first, wrong, n, 0, 0)
    print(f"Equal-area comparison detects a changed final loop after {2**24} copies.")


def check_branching(blocks):
    # Find a genuine reversible pair of 4-paths between distinct 3-histories
    # on a three-column interval. Each block can then be in either state.
    table = classes((3, 3), (0, 0))
    edges = {}
    for record in sorted(four_cells(3)[0]):
        p, f, g, q = record
        u, v = table[p+g+f+q], table[p+f+g+q]
        if u != v:
            edges[u, v] = record
    u, v = next((a, b) for a, b in edges if (b, a) in edges)
    htable = classes((2, 2), (0, 0))
    loop = next(w for w in sorted(four_cells(2)[0])
                if htable[w[0]+w[2]+w[1]+w[3]] == htable[w[0]+w[1]+w[2]+w[3]])

    raw = Expressions()

    def shifted(w, offset):
        t = convert(w)
        return raw.tile(Tile(t.pre, tuple(b+offset for b in t.f),
                             tuple(b+offset for b in t.g), t.revpost))

    size = 2 + 3*blocks
    word = shifted(loop, size-2)
    base = rows(loop[0]+loop[2]+loop[1]+loop[3])
    for i in range(blocks):
        offset = size-2-3*(i+1)
        at_u = raw.pad("", word, reverse(rows(u)))
        at_v = raw.pad("", word, reverse(rows(v)))
        advance = raw.pad(base, shifted(edges[u, v], offset), "")
        back = raw.pad(base, shifted(edges[v, u], offset), "")
        word = raw.cat(raw.cat(at_u, advance), raw.cat(at_v, back))
        base += rows(u)
    flat = 0
    labels = set()
    for k in range(raw.sizes[word]):
        tile = raw.at(word, k)
        if tile.f == (loop[1][0][1]+size-2,):
            labels.add(residual(start(0), tile.revpost))
        flat = raw.cat(flat, raw.tile(tile))
    assert len(labels) == 2**blocks
    assert equal(raw, word, flat, size, 0, 0)
    print(f"The shared loop has {len(labels)} distinct normalized right pads; "
          "its lazy and fully distributed paths agree.")


if __name__ == "__main__":
    check_readers(4)
    check_merges(6)
    check_locality(4)
    check_terms()
    check_branching(4)
