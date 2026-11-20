"""Check compressed context differences on the doubled-loop square and raw records."""

from random import Random

from grid_loop_words import check_grid
from interchange_shared_whiskers import RigidPaths, Words


def check_doubled(h):
    # D: LE -> EL is the contextual 5-square of the doubled grid.
    words = Words()
    early, late = words.letter(0), words.letter(1)
    u, v = words.join(late, early), words.join(early, late)
    paths = RigidPaths(words)
    d = paths.atom(0)
    p = q = d
    source, target = u, v
    # Build the same ordered sweep over 2^h sites by joining halves and by
    # joining four quarters with the immediate whiskerings distributed.
    for level in range(h):
        if level % 2 == 0:
            quarter = q
            quarter_pad = target  # The target and the reversed source both spell (EL)^k.
        p = paths.join(paths.pad(0, p, target), paths.pad(target, p, 0))
        if level % 2:
            a = 0
            parts = []
            for i in range(4):
                b = 0
                for _ in range(3-i):
                    b = words.join(b, quarter_pad)
                parts.append(paths.pad(a, quarter, b))
                a = words.join(a, quarter_pad)
            q = paths.join(parts[0], paths.join(parts[1], paths.join(parts[2], parts[3])))
            assert paths.equal(p, q)
        source = words.join(source, source)
        target = words.join(target, target)
    # Reverse the ordering of the next two batches, keeping their outside faces.
    forward = paths.join(paths.pad(0, p, target), paths.pad(target, p, 0))
    backward = paths.join(paths.pad(source, p, 0), paths.pad(0, p, source))
    assert not paths.equal(forward, backward)
    print(f"Compared binary and quaternary sweeps over {2**h} occurrences; "
          "the opposite batch order is distinct at the same boundary.")


def check_small():
    rng = Random(519)
    words = Words()
    pads = [(0, ()), (words.letter(0), (0,)), (words.letter(1), (1,))]
    for _ in range(12):
        (a, x), (b, y) = rng.choices(pads, k=2)
        pads.append((words.join(a, b), x + y))
    paths = RigidPaths(words)
    pool = [(None, ()), (paths.atom(0), ((0, (), ()),)), (paths.atom(1), ((1, (), ()),))]
    for _ in range(180):
        p, raw = rng.choice(pool)
        if rng.randrange(2):
            (a, x), (b, y) = rng.choices(pads, k=2)
            candidate = paths.pad(a, p, b)
            records = tuple((g, x+l, y+r) for g, l, r in raw)
        else:
            q, right = rng.choice(pool)
            candidate = paths.join(p, q)
            records = raw + right
        independent = None
        for label, l, r in records:
            def literal(word):
                result = 0
                for c in reversed(word):
                    result = words.join(words.letter(c), result)
                return result
            leaf = paths.atom(label, literal(l), literal(r))
            independent = paths.join(independent, leaf)
        assert paths.equal(candidate, independent)
        q, raw_q = rng.choice(pool)
        assert paths.equal(candidate, q) == (records == raw_q)
        pool.append((candidate, records))
    print("180 shared constructions agree with independently expanded contextual records.")


if __name__ == '__main__':
    check_grid()
    check_small()
    check_doubled(24)
