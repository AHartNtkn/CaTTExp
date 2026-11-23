"""Check per-position Moore sweeps at insertions which split a scalar position."""
from argparse import ArgumentParser
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from random import Random
from tempfile import TemporaryDirectory

from partial_cylinder_steiner import trees
from semistrict_surface_configuration_blocks import project, subsets
from semistrict_surface_forest_expansion import graph, substitute
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_moore_insertion import Diagram, height, labelling
from semistrict_surface_scalar_pairs import positions


Q = Fraction
GRID = tuple(map(Q, (0, '1/3', 1)))


@dataclass
class MoorePath:
    length: Fraction
    at: object  # normalized parameter -> lower cell

    def __post_init__(self):
        self.length = Q(self.length)


def identity(x, rank=1):
    for _ in range(rank):
        x = MoorePath(0, lambda t, value=x: value)
    return x


def blend(a, b, t):
    if not isinstance(a, MoorePath):
        return (1-t)*a + t*b
    return MoorePath((1-t)*a.length + t*b.length, lambda u: blend(a.at(u), b.at(u), t))


def realize(sample):
    if not isinstance(sample, tuple):
        return Q(sample)
    values = list(map(realize, sample))
    if len(values) == 1:
        return identity(values[0])
    length = len(values)-1
    def at(t):
        index = min(int(t*length), length-1)
        return blend(values[index], values[index+1], t*length-index)
    return MoorePath(length, at)


def realize_tuple(data):
    return Diagram(tuple(map(realize, data.cells)), tuple(map(realize_tuple, data.children)))


def prefix(path, time):
    if not path.length:
        return path
    return MoorePath(time, lambda t: path.at(t*time/path.length))


def concat(a, b):
    if not a.length:
        return b
    if not b.length:
        return a
    length = a.length+b.length
    def at(t):
        time = t*length
        return a.at(time/a.length) if time <= a.length else b.at((time-a.length)/b.length)
    return MoorePath(length, at)


def serial(a, b, above_cut):
    if above_cut == 1:
        return concat(a, b)
    left = MoorePath(a.length, lambda t: serial(a.at(t), b.at(0), above_cut-1))
    right = MoorePath(b.length, lambda t: serial(a.at(1), b.at(t), above_cut-1))
    return concat(left, right)


def standard(data, rank):
    if not data.children:
        return identity(data.cells[0], rank)
    children = iter(standard(d, rank-1) for d in data.children)
    cell = next(children)
    for child in children:
        cell = serial(cell, child, rank)
    return cell


def sync(cells, rank):
    if not rank:
        return tuple(cells)
    return MoorePath(sum(p.length for p in cells), lambda t: sync([p.at(t) for p in cells], rank-1))


def constant(data, x):
    return Diagram((x,)*len(data.cells), tuple(constant(d, identity(x)) for d in data.children))


def duration(data, depth):
    if depth == 1:
        return sum(d.cells[0].length for d in data.children)
    return sum(duration(d, depth-1) for d in data.children)


def sweep(data, depth, time):
    if depth == 1:
        cells, children = [data.cells[0]], []
        for child in data.children:
            path = child.cells[0]
            spent = min(path.length, time)
            active = prefix(path, spent) if time else identity(cells[-1])
            time -= spent
            cells.append(active.at(1))
            children.append(constant(child, active))
        return Diagram(tuple(cells), tuple(children)), time
    children = []
    for child in data.children:
        part, time = sweep(child, depth-1, time)
        children.append(part)
    return Diagram(data.cells, tuple(children)), time


def snapshot(p, rank):
    if not rank:
        return p
    return p.length, tuple(snapshot(p.at(t), rank-1) for t in GRID)


def check_split_discs():
    left = MoorePath(1, lambda t: t)
    right = MoorePath(2, lambda t: 2*t)
    # At elapsed time one a serial sweep has just completed the left path.
    merged = sync([left, right], 1)
    assert merged.at(1/merged.length) == (Q(1, 3), Q(2, 3))
    rng, counts = Random(8123), Counter()
    for size in range(4, 9):
        for tree in trees(size):
            for n in (2, 3):
                local = []
                for pos in positions(tree, n):
                    child = tree
                    for i in pos:
                        child = child[i]
                    local.append(child)
                if len(local) < 2 or not 1 <= max(map(height, local)) <= 2:
                    continue
                rank = max(map(height, local))
                data = [realize_tuple(labelling(k, rng)) for k in local]
                top = sync([standard(d, rank) for d in data], rank)
                for stage in range(1, rank+1):
                    section = top
                    for _ in range(rank-stage):
                        section = section.at(0)
                    lengths = [duration(d, stage) for d in data]
                    assert section.length == sum(lengths)
                    for t in GRID:
                        parts = []
                        for d, length in zip(data, lengths, strict=True):
                            swept, unused = sweep(d, stage, t*length)
                            assert not unused
                            parts.append(standard(swept, rank))
                        inside = sync(parts, rank)
                        outside = identity(prefix(section, t*section.length), rank-stage)
                        assert snapshot(inside, rank) == snapshot(outside, rank), (tree, n, stage, t, lengths, snapshot(inside, rank), snapshot(outside, rank))
                        counts['split-disc prefixes'] += 1
                        if t not in (0, 1) and len(set(lengths)) > 1:
                            counts['unequal-clock interior fractions'] += 1
    return counts


def coherent_value(chain, q, palette):
    # A point on a simplex of graph vertices. Its barycentric coordinate
    # varies with the whole chain; a last face retains the earlier weights.
    if not palette:
        return graph((), 0)
    threshold = sum(w * len(t) for t, w in chain)/len(palette)
    order = [x for x in palette if x in chain[-1][0]]
    return graph(order, int(q < threshold))


def operad_value(outer, fibres, chain, q):
    roots = frozenset(fibres)
    parent = {x: i for i, (names, _) in fibres.items() for x in names}
    induced = tuple((frozenset(parent[x] for x in s), w) for s, w in chain)
    outside = outer(project(induced, roots), q)
    inside = {i: get(project(chain, names), q) for i, (names, get) in fibres.items()}
    return substitute(outside, inside)


def check_coherent_graphs(empty_fibre):
    def labelled(names):
        return frozenset(names), lambda chain, q: coherent_value(chain, q, names)
    leaves = (0, 1, 2) if empty_fibre else (0, 1, 2, 3)
    first = {8: labelled((5, 4)), 9: labelled((6,))}
    second = {4: labelled((0, 1)), 5: labelled((2,)), 6: labelled(() if empty_fibre else (3,))}
    outside = labelled((9, 8))[1]
    flat = {}
    for root, (mid, get) in first.items():
        sub = {i: second[i] for i in mid}
        flat[root] = (frozenset().union(*(names for names, _ in sub.values())),
                      lambda ch, q, get=get, sub=sub: operad_value(get, sub, ch, q))
    nested = lambda ch, q: operad_value(outside, first, ch, q)
    count = 0
    for a in subsets(leaves):
        for b in subsets(a):
            chain = ((a, Q(1, 3)), (b, Q(2, 3)))
            for q in (Q(1, 4), Q(1, 2), Q(3, 4)):
                assert operad_value(nested, second, chain, q) == operad_value(outside, flat, chain, q)
                last_face = ((a, Q(1)), (b, Q(0)))
                shorter = operad_value(nested, second, ((a, Q(1)),), q)
                assert operad_value(outside, flat, last_face, q) == shorter.restrict(b)
                count += 1
    return count


def check_birth_insertion(checkout):
    exe = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        (folder / 'Arity.catt').write_text("""import examples/eh-common
def expanded = coh [ [[a,b],[c]] : swap_src(comp[a,b],c) -> swap_tgt(comp[a,b],c) ]
def nested {f{a}g{b}h}{i{c}j} = swap(comp[a,b],c)
""")
        ctx = '(x : *) (a : id(id(x)) -> id(id(x))) (m : comp[a,a] -> a) (e : id(id(id(x))) -> a)'
        args = 'comp[a,[e]],m,m'
        (folder / 'Birth.catt').write_text(
            f'import Arity\ndef birth_insertion {ctx} : nested({args}) -> expanded({args}) = id(expanded({args}))\n')
        accepted(run(exe, folder, 'Birth.catt', ['--sua']), 'Birth.catt', ['birth_insertion'])
        rejected(run(exe, folder, 'Birth.catt', ['--su']), 'Birth.catt', 'birth_insertion')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    for name, count in check_split_discs().items():
        print(f'{name}: {count}')
    print('Coherent substitutions and last faces:', sum(check_coherent_graphs(e) for e in (False, True)))
    if args.catt_strict:
        check_birth_insertion(args.catt_strict.resolve())
        print('Checked insertion at a nonstandard head with a birth and two merges.')
