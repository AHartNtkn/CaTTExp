"""Construct the one-probe fifth-degree tests as straight-line programs on meridians."""
from argparse import ArgumentParser
from itertools import permutations, product
import json

from semistrict_surface_history_group import cyclic, inv, reduced
from semistrict_surface_shared_edge import braid_image


def cyclic_candidates(rank):
    letters = tuple(range(1, rank + 1)) + tuple(range(-rank, 0))
    current = [()]
    candidates = set()
    for _ in range(rank):
        current = [w + (x,) for w in current for x in letters if not w or w[-1] != -x]
        candidates.update(cyclic(w) for w in current)
    return sorted(candidates, key=lambda w: (len(w), w))


def build(size):
    if size < 1:
        raise ValueError('expected a positive size')
    nodes = []
    def add(*op):
        nodes.append(op)
        return len(nodes) - 1

    previous = None
    for rank in range(1, size + 1):
        leaves = [add('word', w) for w in cyclic_candidates(rank)]
        if previous is not None:
            leaves.append(previous)
        tag = rank + 1
        level = [add('conjugate', tag, i, leaf) for i, leaf in enumerate(leaves, 1)]
        while len(level) > 1:
            next_level = [add('commutator', a, b) for a, b in zip(level[::2], level[1::2])]
            if len(level) % 2:
                next_level.append(level[-1])
            level = next_level
        previous = add('commutator', level[0], add('word', (tag,)))
    return nodes


def evaluate(nodes, product_of, inverse, one, generators):
    values = []
    for node in nodes:
        if node[0] == 'word':
            val = one
            for letter in node[1]:
                g = generators[abs(letter) - 1]
                val = product_of(val, g if letter > 0 else inverse(g))
        elif node[0] == 'conjugate':
            _, tag, power, child = node
            conjugator = one
            for _ in range(power):
                conjugator = product_of(conjugator, generators[tag - 1])
            val = product_of(product_of(conjugator, values[child]), inverse(conjugator))
        else:
            assert node[0] == 'commutator'
            a, b = (values[i] for i in node[1:])
            val = product_of(product_of(a, b), product_of(inverse(a), inverse(b)))
        values.append(val)
    return values[-1]


def as_word(nodes, holes):
    return evaluate(nodes, lambda a, b: reduced(a + b), inv, (),
                    [(i,) for i in range(1, holes + 1)])


def point_push(w):
    moves = []
    for g in w:
        i = abs(g)
        walk = tuple(range(1, i))
        loop = walk + (i, i) + inv(walk)
        moves.extend(loop if g > 0 else inv(loop))
    return tuple(moves)


def read_push(holes, movie):
    """Read crossings of downward rays with all stationary strands held fixed."""
    row = list(range(holes + 1))  # 0 is the probe
    reading = []
    for g in movie:
        i = abs(g) - 1
        a, b = row[i:i + 2]
        assert a == 0 or b == 0
        if a == 0 and g < 0:
            reading.append(-b)
        if b == 0 and g > 0:
            reading.append(a)
        row[i:i + 2] = [b, a]
    assert row == list(range(holes + 1))
    return reduced(reading)


def finite_action(w):
    # Partial permutations along a freely reduced path extend to permutations.
    maps = {}
    for i, g in enumerate(w):
        a, b = (i, i + 1) if g > 0 else (i + 1, i)
        table = maps.setdefault(abs(g), {})
        assert a not in table
        table[a] = b
    states = set(range(len(w) + 1))
    inverses = {}
    for g, table in maps.items():
        assert len(set(table.values())) == len(table)
        table.update(zip(sorted(states - table.keys()), sorted(states - set(table.values())), strict=True))
        inverses[g] = {v: k for k, v in table.items()}
    place = 0
    for g in w:
        place = (maps[g] if g > 0 else inverses[-g])[place]
    assert place == len(w) and place != 0


def audit():
    lengths = []
    for size in (1, 2, 3):
        holes = size + 1
        nodes = build(size)
        w = as_word(nodes, holes)
        assert read_push(holes, point_push(w)) == w
        finite_action(w)
        for i in range(1, holes + 1):
            assert not reduced(x for x in w if abs(x) != i)
        lengths.append(len(w))

    # Compare the first mixed movie in the faithful Artin action, fixing the probe
    # and all the stationary occurrences at the end.
    w = as_word(build(1), 2)
    movie = point_push(w)
    assert braid_image(3, movie) != braid_image(3, ())

    group = tuple(permutations(range(3)))
    unit = group[0]
    def mul(a, b):
        return tuple(b[i] for i in a)
    def rev(a):
        return tuple(a.index(i) for i in unit)
    checks = 0
    nodes = build(2)
    candidates = cyclic_candidates(2)
    for images in product(group, repeat=3):
        # Evaluate the premise independently at the short words.
        if any(evaluate([('word', w)], mul, rev, unit, images) == unit for w in candidates):
            assert evaluate(nodes, mul, rev, unit, images) == unit
            checks += 1
    assert checks > 0

    # The earlier test can be the only killed leaf at the next size.
    zero = (0, 0, 0)
    basis = [tuple(int(j == i) for j in range(3)) for i in range(3)]
    def plus(a, b):
        return tuple((x + y) % 5 for x, y in zip(a, b, strict=True))
    def neg(a):
        return tuple(-x % 5 for x in a)
    assert all(evaluate([('word', w)], plus, neg, zero, basis) != zero for w in candidates)
    assert all(evaluate(build(i), plus, neg, zero, basis) == zero for i in (1, 2))
    return dict(reduced_lengths=lengths, finite_group_implications=checks, inherited_relation=True)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--size', type=int)
    parser.add_argument('--switches', action='store_true', help='expand the program into signed adjacent switches')
    args = parser.parse_args()
    if args.size is None:
        print(json.dumps(audit()))
        return
    nodes = build(args.size)
    result = dict(punctures=args.size + 1, program=nodes)
    if args.switches:
        result['switches'] = point_push(as_word(nodes, args.size + 1))
    print(json.dumps(result))


if __name__ == '__main__':
    main()
