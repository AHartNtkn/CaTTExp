"""Test streaming 4-pad codes and equality of actual whiskered 5-squares."""

from itertools import product
from random import Random

from check_interchange_grid_contractions import four_cells
from check_interchange_grid_windows import convert
from grid_loop_words import classes, states
from interchange_grid_five import GridReader, equal_five
from interchange_grid_windows import units
from interchange_shared_whiskers import Words


def refinements(w, splits):
    options = splits.get(w)
    if not options:
        return [(convert(w),)]
    return [p+q for pair in options for p, q in product(
        refinements(pair[0], splits), refinements(pair[1], splits))]


def check():
    width = 4
    letters, parents = four_cells(width)
    table = classes((4, 4), (0, 0))
    initial = tuple((r, k) for k in (4, 3, 2, 1) for r in (0, 1))
    base = table[initial]

    def based(w):
        pre, f, g, post = w
        return table[pre+g+f+post] == table[pre+f+g+post] == base

    loops = sorted(w for w in letters if based(w))
    wide = next(w for w in loops if len(w[1]) == len(w[2]) == 2)
    splits = {}
    for pair, parent in parents.items():
        splits.setdefault(parent, []).append(pair)
    first, second = refinements(wide, splits)
    raw, tiles, tile_ids = Words(), [], {}

    def word(sequence):
        root = 0
        for t in sequence:
            if t not in tile_ids:
                tile_ids[t] = len(tiles)
                tiles.append(t)
            root = raw.join(root, raw.letter(tile_ids[t]))
        return root

    def normalize(end, reader):
        buf, emitted = reader.run((), end)
        return reader.output.join(emitted, reader.finish(buf))

    # Compare independently chosen spellings of actual contextual 4-loops in a stream.
    rng = Random(920)
    pwide, qwide = word(first), word(second)
    bases = [word(tuple(units(convert(w)))) for w in loops]
    cases = 0
    for reverse in (False, True):
        out = Words()
        stream = GridReader(width, (0, 0), tiles, raw, out, reverse)
        for _ in range(80):
            left = right = 0
            for _ in range(rng.randrange(2, 12)):
                a = rng.choice(bases+[pwide])
                b = qwide if a == pwide else a
                left, right = raw.join(left, a), raw.join(right, b)
            assert out.equal(normalize(left, stream), normalize(right, stream))
            cases += 1
        # Strip the common first/last corners. The independent two middle tiles
        # are distinct even after quotienting their lower labels.
        a, b = word(first[1:3]), word(second[1:3])
        for i in (0, 3):
            assert out.equal(normalize(word((first[i],)), stream),
                             normalize(word((second[i],)), stream))
        assert not out.equal(normalize(a, stream), normalize(b, stream))
        assert out.equal(normalize(pwide, stream), normalize(qwide, stream))

    # E,L are the two H loops at the common full crossing; their temporal
    # square D has source LE and target EL. Choose the contextual occurrences
    # with the other full two-column block fixed.
    def corner(pos):
        p, q = initial[:pos], initial[pos+2:]
        f, g = (initial[pos+1],), (initial[pos],)
        def candidate(w):
            return (w[1:3] == (f, g) and len(w[0]) == len(p) and len(w[3]) == len(q)
                    and table[w[0]+g+f+w[3]] == base)
        # Inactive block spellings have the same normalized prefix/suffix.
        s = states((4, 4), p)[-1]
        e = states(s, g+f)[-1]
        canon = classes((4, 4), s)[p], f, g, classes(e, (0, 0))[q]
        assert canon in loops and candidate(canon)
        return word((convert(canon),))

    early, late = corner(1), corner(5)
    source, target = raw.join(late, early), raw.join(early, late)
    rules = [('atom', 0, 0, 0)]

    def add(rule):
        rules.append(rule)
        return len(rules)-1

    def cat(a,b):
        return add(('cat', a,b))

    def pad(l,a,r):
        return add(('pad', l,a,r))

    p = q = 0
    for i in range(18):
        if not i % 2:
            quarter, u, v = q, source, target
        reverse_batches = cat(pad(source, p, 0), pad(0, p, target))
        p = cat(pad(0, p, source), pad(target, p, 0))
        if i % 2:
            t1 = pad(0, quarter, raw.join(u, raw.join(u,u)))
            t2 = pad(v, quarter, raw.join(u,u))
            t3 = pad(raw.join(v,v), quarter, u)
            t4 = pad(raw.join(v,raw.join(v,v)), quarter, 0)
            q = cat(t1, cat(t2, cat(t3,t4)))
        source, target = raw.join(source, source), raw.join(target, target)

    def same(a,b):
        return equal_five(rules, (a,b), width, (0,0), tiles, raw)

    assert same(pad(pwide,p,qwide), pad(qwide,q,pwide))
    assert not same(pad(pwide, p, qwide), pad(qwide, reverse_batches, pwide))
    print(f"{cases} bidirectional pad-code comparisons; unequal middle routes have equal padded values.")
    print(f"Two sweeps of {2**18} rigid squares agree under different two-axis pad splits; "
          "the opposite batch schedule differs at the same boundary.")


if __name__ == '__main__':
    check()
