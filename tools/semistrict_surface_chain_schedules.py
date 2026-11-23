"""Check integral wire interval bases and class-three tests on a schedule grid."""
from argparse import ArgumentParser
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
from random import Random
from tempfile import TemporaryDirectory

from sympy import Matrix, eye

from semistrict_surface_concurrent_rules import Network, cut_matrices, pair_map, subsets
from semistrict_surface_exact_boundary import accepted, rejected, run


class Components:
    def __init__(self, vertices):
        self.parents = {v: v for v in vertices}

    def root(self, v):
        while v != self.parents[v]:
            v = self.parents[v]
        return v

    def join(self, v, w):
        a, b = self.root(v), self.root(w)
        if a == b:
            return False
        self.parents[b] = a
        return True


def partitions(live, steps):
    components = Components(set(live).union(*(ins | outs for ins, outs in steps)))
    for ins, outs in steps:
        first = min(ins)
        for w in ins | outs:
            components.join(first, w)
    return partition_by(live, components.root)


def partition_by(live, key):
    blocks = {}
    for w in live:
        blocks.setdefault(key(w), set()).add(w)
    return tuple(frozenset(block) for block in blocks.values())


def meet(live, left, right):
    # Intersection of sublattices of block-constant vectors.
    if not left or not right:
        return ()
    components = Components(live)
    for block in left + right:
        for w in block:
            components.join(min(block), w)
    return partition_by(live, components.root)


def complement(blocks, left, right):
    # Choose a unit vector on each edge outside a spanning forest. With only
    # one partition, keep all except one coordinate in each of its blocks.
    if not left and not right:
        return blocks
    if not left or not right:
        parts = left or right
        return [b for b in blocks if all(min(p) not in b for p in parts)]
    graph = Components([(0, p) for p in left] + [(1, p) for p in right])
    extra = []
    for b in blocks:
        v = next(p for p in left if b <= p)
        w = next(p for p in right if b <= p)
        if not graph.join((0, v), (1, w)):
            extra.append(b)
    return extra


def interval_bases(initial, steps):
    """Return the actual transported 0/1 columns, keyed by their birth."""
    live = sorted(initial)
    columns = {}
    history = []
    for k in range(len(steps) + 1):
        past = [()] + [partitions(live, steps[i:k]) for i in range(k + 1)]
        future = [()] + [partitions(live, steps[k:j]) for j in range(len(steps), k - 1, -1)]
        for i in (range(1, len(past)) if k == 0 else [len(past) - 1]):
            for j in range(1, len(future)):
                blocks = meet(live, past[i], future[j])
                left = meet(live, past[i - 1], future[j])
                right = meet(live, past[i], future[j - 1])
                for b in complement(blocks, left, right):
                    columns[k, len(columns)] = b
        mat = Matrix([[int(w in b) for b in columns.values()] for w in live])
        assert abs(mat.det()) == 1
        for p, q in product(past, future):
            blocks = meet(live, p, q)
            count = sum(bool(blocks) and all(not b & cell or cell <= b for cell in blocks)
                        for b in columns.values())
            assert count == len(blocks)
        history.append((tuple(live), columns))
        if k < len(steps):
            ins, outs = steps[k]
            columns = {label: (b - ins) | (outs if ins <= b else set())
                       for label, b in columns.items() if not ins & b or ins <= b}
            assert len(columns) == len(live) - len(ins) + 1
            live = sorted((set(live) - ins) | outs)
    return history


def check_bases():
    rng = Random(82415)
    histories = cuts = 0
    for _ in range(200):
        initial = set(range(rng.randint(1, 5)))
        live = initial.copy()
        recent = initial.copy()
        fresh = len(initial)
        steps = []
        for _ in range(rng.randint(2, 7)):
            first = rng.choice(sorted(recent))
            ins = {first, *rng.sample(sorted(live - {first}), rng.randrange(len(live)))}
            count = rng.randint(1, min(4, 7 - len(live - ins)))
            recent = set(range(fresh, fresh + count))
            fresh += count
            steps.append((ins, recent))
            live = (live - ins) | recent
        cuts += len(interval_bases(initial, steps))
        histories += 1
    return histories, cuts


def check_refinements():
    """Compare every two-step splitting of a four-event schedule at actual wire times."""
    checks = 0
    for arcs in subsets(combinations(range(4), 2)):
        wires = [(None, e) for e in range(4)] + [(e, None) for e in range(4)] + sorted(arcs)
        net = Network(4, wires)

        def schedules(cut):
            if len(cut) == 4:
                yield ()
                return
            enabled = [e for e in net.events if e not in cut and cut | {e} in net.cuts]
            for batch in subsets(enabled):
                if batch:
                    for tail in schedules(cut | batch):
                        yield (batch,) + tail

        def stationary(schedule):
            cut = frozenset()
            for batch in schedule:
                yield net.cuts[cut].difference(*(net.inputs[e] for e in batch))
                cut |= batch

        def split(schedule):
            for i, batch in enumerate(schedule):
                for left in subsets(batch):
                    if left and left != batch:
                        yield schedule[:i] + (left, batch-left) + schedule[i+1:]

        def restrict(schedule, values, finer):
            result = {}
            for i, (batch, live) in enumerate(zip(finer, stationary(finer))):
                j = next(k for k, parent in enumerate(schedule) if batch <= parent)
                for w in live:
                    if (j, w) in values:
                        result[i, w] = values[j, w]
                    else:
                        birth, death = wires[w]
                        assert (birth in schedule[j]) != (death in schedule[j])
                        result[i, w] = int(death in schedule[j])
            for w in range(len(wires)):
                times = [t for (_, v), t in result.items() if v == w]
                assert times == sorted(times)
            return result

        for schedule in schedules(frozenset()):
            values = {(i, w): Fraction(i+1, len(schedule)+1)
                      for i, live in enumerate(stationary(schedule)) for w in live}
            for middle in split(schedule):
                middle_times = restrict(schedule, values, middle)
                for fine in split(middle):
                    assert restrict(middle, middle_times, fine) == restrict(schedule, values, fine)
                    checks += 1
    return checks


def check_grid():
    # Two dependent pairs of events, running independently of one another.
    wires = [(None, 0), (0, 1), (1, None), (None, 2), (2, 3), (3, None)]
    net = Network(4, [wire for wire in wires for _ in range(2)])
    target_cuts = [(0, 2), (1, 1), (2, 0)]
    letters = []
    for i in range(3):
        letter = eye(4)
        letter[i, i + 1] = 1
        letters.append(letter)

    def coordinates(c):
        return len(c & {0, 1}), len(c & {2, 3})

    def character(c):
        i, j = coordinates(c)
        return Matrix([[(-1)**(x+y) if (x//2, y//2) == (i, 3+j) else 0
                        for x, y in combinations(sorted(net.cuts[c]), 2)]])

    def value(c, index):
        pos = coordinates(c)
        return (letters[target_cuts.index(pos)]**character(c)[index]
                if pos in target_cuts else eye(4))

    # Check every incidence directly on the original pairs of wires.
    edges = 0
    for c, live in net.cuts.items():
        for e in net.events:
            after = c | {e}
            if after == c or after not in net.cuts:
                continue
            stationary = live - net.inputs[e]
            same = {w: {w} for w in stationary}
            for side, cut in ((net.inputs[e], c), (net.outputs[e], after)):
                incidence = pair_map(stationary | {~e}, net.cuts[cut], same | {~e: side}, -1)
                if coordinates(cut) in target_cuts:
                    assert (character(cut) * incidence).is_zero_matrix
            edges += 1
    cuts = list(net.cuts)
    for c, d in product(cuts, repeat=2):
        if c <= d:
            for i, j in product(range(6), repeat=2):
                a, b = value(c, i), value(d, j)
                assert a*b == b*a
    selected = [next(c for c in cuts if coordinates(c) == pos) for pos in target_cuts]
    a, b, z = [next(value(c, i) for i in range(6) if value(c, i) == letter)
               for c, letter in zip(selected, letters)]
    comm = a*b*a.inv()*b.inv()
    answer = eye(4)
    answer[0, 3] = 1
    assert comm*z*comm.inv()*z.inv() == answer
    # Independently reconstruct the commutation graph from the transported bases.
    histories = [interval_bases({offset, offset+1},
                   [({offset + 2*k, offset + 2*k+1}, {offset + 2*k+2, offset + 2*k+3})
                    for k in range(2)]) for offset in (0, 6)]
    active = {}
    for c in cuts:
        labels = [(h, label) for h, k in enumerate(coordinates(c))
                  for label in histories[h][k][1]]
        active[c] = {tuple(sorted(v)) for v in combinations(labels, 2)}
    vertices = set.union(*active.values())
    commuting = {frozenset((v, w)) for c, d in product(cuts, repeat=2) if c <= d
                 for v, w in product(active[c], active[d]) if v != w}
    missing = len(vertices)*(len(vertices)-1)//2 - len(commuting)
    assert (len(vertices), missing) == (22, 9)
    return edges, len(vertices), missing


def check_branching_flags():
    pairs = list(combinations(range(3), 2))
    wires = [(None, e) for e in range(3)]
    wires += [(e, 3+i) for e, pair in enumerate(pairs) for i in pair]
    wires += [(3+i, None) for i in range(3)]
    net = Network(6, wires)
    final = sorted(net.cuts[frozenset(net.events)])
    planes = []
    for e, (i, j) in enumerate(pairs):
        remaining = [e, 3+i, 3+j]
        assert frozenset(net.events).difference(remaining) in net.cuts
        blocks = partitions(final, [(net.inputs[t], net.outputs[t]) for t in remaining])
        assert frozenset([final[i], final[j]]) in blocks and len(blocks) == 2
        planes.append(blocks)
    assert len(set(planes)) == 3
    assert meet(final, meet(final, planes[0], planes[1]), planes[2]) == (frozenset(final),)


def check_stages():
    # A four-port middle event synchronizes two independent squares.
    wires = [(None, 0), (None, 1), (0, 2), (1, 2),
             (2, 3), (2, 4), (3, None), (4, None)]
    net = Network(5, [w for w in wires for _ in range(2)])
    ranks = cut_matrices(net, -1)
    assert ranks == (48, 22, 26)
    return ranks


def check_rice(checkout):
    context = '(x : *)' + ''.join(f' ({w} : id(id(x)) -> id(id(x)))' for w in 'abcdefghijkl')
    for rule, ins, outs in [('p', 'a,b', 'c,d'), ('q', 'c,d', 'e,f'),
                             ('r', 'g,h', 'i,j'), ('s', 'i,j', 'k,l')]:
        context += f' ({rule} : comp[{ins}] -> comp[{outs}])'
    args = 'comp[p,q],comp[r,s]'
    crossing = f'swap({args})'
    old_type = f'comp[{crossing},id(swap_tgt({args}))] -> {crossing}'
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        exe = checkout / 'target/release/catt_strict'
        for name, term in [('Unit', f'unitor_r({crossing})'), ('Identity', f'id({crossing})')]:
            file = name + '.catt'
            (folder / file).write_text('import examples/eh-common\n'
                                       f'def fill {context} : {old_type} = {term}\n')
            for flags in ([], ['--sua']):
                result = run(exe, folder, file, flags)
                if not flags and name == 'Identity':
                    rejected(result, file, 'fill')
                else:
                    accepted(result, file, ['fill'])


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    print('Two-step schedule refinements with matching wire times:', check_refinements())
    print('Serial histories and unimodular cut bases:', *check_bases())
    print('Grid incidences, Artin generators, noncommuting pairs:', *check_grid())
    print('The nested commutator has (1,4)-entry one in UT(4,Z).')
    check_branching_flags()
    print('The three distinct branching planes share a rank-one intersection.')
    print('Synchronized squares: cut generators, relation rank, abelian rank:', *check_stages())
    if args.catt_strict:
        check_rice(args.catt_strict.resolve())
        print('Checked a raw unitor and a converted identity at the same grid 6-type.')
