"""Audit top occurrences in the signed disk faces used for forced inhabitation."""

from collections import Counter, defaultdict
from itertools import product

from interchange_cylinders import boundary
from interchange_double_variation import PATHS, path_table


def seed_rows(pair):
    """Top words of the seed hemispheres from hom rank three up."""
    if pair == (3, 3):
        return {
            3: (tuple("yabcx"), tuple("xhfy")),
            4: (PATHS["P"], PATHS["D"]),
            5: (("exchange", "E23", "G"), ("E32", "H")),
            6: (("E33",),) * 2,
        }
    if pair == (3, 2):
        return {
            3: (tuple("abcx"), tuple("xhf")),
            4: (("W", "fx", "hx"), ("cx", "bx", "K")),
            5: (("E32",),) * 2,
        }
    assert pair == (2, 3)
    return {
        3: (tuple("yabc"), tuple("hfy")),
        4: (("ay", "by", "cy", "W"), ("W", "hy", "fy")),
        5: (("E23",),) * 2,
    }


def raise_disk(old, pair, moving, changes):
    """Build the raw row words. Lower fixed actions leave their top tags intact."""
    p, q = pair[moving], pair[1 - moving]
    new = {rank: words for rank, words in old.items() if rank < p}
    # A context entry specifies the top-rank prefix and suffix on that layer.
    contexts = [((), ()), ((), ())]
    for rank in range(p, p + q + 1):
        src = (rank - p) % 2 if moving else 0
        dst = 1 - src
        endpoints = [
            tuple(contexts[layer][0] + row + contexts[layer][1] for layer in (src, dst))
            for row in old[rank]
        ]
        new[rank] = endpoints[0][0], endpoints[1][1]
        tags = []
        for side, (before, after) in enumerate(endpoints):
            if rank == p:
                tag = "y" if moving else "x"
            else:
                tag = ("raise", moving, p + 1, min(q, rank), rank,
                       None if rank == p + q else side)
                change = Counter(after)
                change.subtract(before)
                for label, delta in change.items():
                    if delta:
                        changes[label].add(delta)
            tags.append(tag)
        contexts[src] = (), (tags[1],)
        contexts[dst] = (tags[0],), ()
    assert tags[0] == tags[1]
    new[p + q + 1] = ((tags[0],),) * 2
    return new


def check_incidence(limit):
    seed = seed_rows((3, 3))
    source, target = seed[5]
    changes = defaultdict(set)
    for tag in ("G", "H", "E32", "E23"):
        changes[tag].add(target.count(tag) - source.count(tag))
    disks = {pair: seed_rows(pair) for pair in ((3, 2), (2, 3), (3, 3))}
    for p, q in sorted(product(range(2, limit + 1), repeat=2), key=sum):
        if (p, q) in disks or (p, q) == (2, 2):
            continue
        moving = int(p < 4 and q > 3)
        old_pair = (p, q - 1) if moving else (p - 1, q)
        disks[p, q] = raise_disk(disks[old_pair], old_pair, moving, changes)
    for label, deltas in changes.items():
        if isinstance(label, tuple):
            _, moving, _, _, _, side = label
            assert side is not None  # a principal never occurs with a net change
            assert deltas == ({1} if moving == side else {-1})
        else:
            assert label in {"E23", "G", "E32", "H"}
            assert deltas == ({-1} if label in {"E23", "G"} else {1})
    return len(disks), len(changes)


def check_sibling_chains():
    # Read the differential at the surviving moving face. This separates the
    # direct tensor from every other positive sum supported on the moving input.
    count = 0
    for moving, degree, fixed_degree in product(range(2), range(4, 12), range(1, 9)):
        for side in (0, 1):
            pair = [(degree, 2), (fixed_degree, side)]
            if moving:
                pair.reverse()
            column = {basis: coeff for basis, coeff in boundary(tuple(pair)).items()
                      if basis[moving] == (degree - 1, 1)}
            assert len(column) == 1
            (basis, coeff), = column.items()
            assert basis[1 - moving] == (fixed_degree, side)
            assert coeff == ((-1) ** fixed_degree if moving else 1)
            count += 1
    return count


def check_smaller_bridge():
    # In the bare (4,3) graph read the change in the count of J(x^0,y).
    # A pure insert or a fixed pad is carried on both sides with its fields.
    changes = {}
    for head, source in (("G", "L"), ("H", "R")):
        for layer in (0, 1):
            changes[head, layer] = (layer == 0) * (
                PATHS["D"].count("J") - PATHS[source].count("J"))
    for fixed in (2, 3):
        for side, row in enumerate(seed_rows((3, fixed))[4]):
            # The source is on layer zero and the target on layer one.
            changes["bridge", fixed, side] = -row.count("J")
    for row in seed_rows((3, 2))[4] + seed_rows((2, 3))[4]:
        assert "J" not in row
    assert {k for k, v in changes.items() if v < 0} == {("bridge", 3, 1)}
    assert path_table(PATHS["P"]) != path_table(PATHS["D"])
    assert PATHS["D"].count("J") == 1


if __name__ == "__main__":
    disks, labels = check_incidence(12)
    print(f"{disks} disks through (12,12), {labels} one-sided tag counts")
    print(f"{check_sibling_chains()} moving-face differential columns separated")
    check_smaller_bridge()
    print("Only the positive (4,3) bridge can consume the marked J")
