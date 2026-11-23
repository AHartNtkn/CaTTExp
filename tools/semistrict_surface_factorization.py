"""Test the relative cut factorization calculation and its spatial cube on actual terms."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from itertools import combinations, permutations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_concurrent_rules import Network, pair_map, subsets
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_schedule_homology import rank_mod
from semistrict_surface_serial_detection import refines, schedules


def inner_cuts(schedule):
    cut = frozenset()
    result = set()
    for batch in schedule[:-1]:
        cut |= batch
        result.add(cut)
    return result


def check_relative_pair(events, arcs):
    cells = list(schedules(events, arcs))
    chains = defaultdict(list)
    relative = defaultdict(list)

    def extend(chain):
        d = len(chain)-1
        chains[d].append(chain)
        # A fixed-cut factorization contains this simplex precisely when all
        # of its schedules retain that cut.
        common = set.intersection(*(inner_cuts(s) for s in chain))
        assert common == inner_cuts(chain[0])
        if not common:
            relative[d].append(chain)
        for t in cells:
            if t != chain[-1] and refines(t, chain[-1]):
                extend(chain+(t,))

    for s in cells:
        extend((s,))
    counts = [len(relative[d]) for d in range(max(chains)+1)]
    for p in (2, 3):
        ranks = [0]
        for d in range(1, len(counts)):
            row = {v:i for i,v in enumerate(relative[d-1])}
            cols = [{face: (-1)**k for k in range(d+1)
                     if (face := v[:k]+v[k+1:]) in row}
                    for v in relative[d]]
            ranks.append(rank_mod(cols, row, p))
        ranks.append(0)
        betti = [n-ranks[d]-ranks[d+1] for d,n in enumerate(counts)]
        assert all(b == int(not arcs and d == len(events)-1) for d,b in enumerate(betti))
    return sum(map(len, chains.values()))


def check_intervals():
    intervals = simplices = boolean = 0
    for arcs in subsets(combinations(range(4), 2)):
        net = Network(4, sorted(arcs))
        for lower, upper in product(net.cuts, repeat=2):
            if lower < upper:
                diff = upper-lower
                required = {(e, f) for e, f in arcs if e in diff and f in diff}
                simplices += check_relative_pair(diff, required)
                boolean += not required
                intervals += 1
    return intervals, boolean, simplices


def check_cluster_sections():
    count = 0
    for sizes in product((1, 2, 3), repeat=3):
        blocks = {}
        for i, size in enumerate(sizes):
            blocks[i] = set(range(sum(sizes[:i]), sum(sizes[:i])+size))
        ports = set.union(*blocks.values())
        reps = {w: {i for i,b in blocks.items() if w == min(b)} for w in ports}
        for sign in (-1, 1):
            expansion = pair_map(blocks.keys(), ports, blocks, sign)
            restriction = pair_map(ports, blocks.keys(), reps, sign)
            assert (restriction*expansion).is_Identity
            count += 1
    return count


def check_partial_names():
    # Outgoing arrows from a pure index include all partial bijections to
    # surviving directed wires. Factorization through a subset is by support.
    names = frozenset(range(4))
    small = list(subsets(names))
    checks = 0
    for size in range(5):
        for image in permutations(names, size):
            keep = frozenset(image)
            for s, t in product(small, repeat=2):
                assert (keep <= s and keep <= t) == (keep <= (s & t))
                if keep <= s:
                    intermediate = tuple(sorted(s))
                    lift = tuple(intermediate.index(v) for v in image)
                    assert tuple(intermediate[i] for i in lift) == image
                checks += 1
    return checks


def check_lifted_bridge():
    # The moving-end two-rule square has a middle alternating character in
    # each order. Send their unit loops to two transpositions on three sheets.
    square = Network(2, [(None, e) for e in range(2) for _ in range(2)]
                        + [(e, None) for e in range(2) for _ in range(2)])
    for early, late in ((0, 1), (1, 0)):
        cut = frozenset([early])
        live = square.cuts[cut]
        outputs, inputs = sorted(square.outputs[early]), sorted(square.inputs[late])
        ordered = list(combinations(sorted(live), 2))
        values = {(v, w): (-1)**(i+j) for i,v in enumerate(outputs) for j,w in enumerate(inputs)}
        row = [values.get((v,w), -values.get((w,v), 0)) for v,w in ordered]
        assert 1 in row
        for block in (set(inputs), set(outputs)):
            rest = live-block
            incidence = pair_map(rest | {-1}, live, {v: {v} for v in rest} | {-1: block}, -1)
            assert all(sum(a*b for a,b in zip(row, col)) == 0 for col in incidence.columnspace())

    left, right = (1, 0, 2), (0, 2, 1)
    # An excursion over the bridge, around the right loop, back, then around
    # the left loop has the same augmented relative effect as a plain bridge.
    # Following the sheets distinguishes the two relative classes.
    classes = []
    for i in range(3):
        j = right[i]
        lifted = Counter([i, left[j]])
        lifted[j] -= 1
        assert sum(lifted.values()) == 1
        classes.append(tuple(lifted[k] for k in range(3)))
    assert (1, -1, 1) in classes
    return classes


def route(order):
    stages = []
    states = list('fhj')
    for i in order:
        entries = states.copy()
        entries[i] = '['+'abc'[i]+']'
        stages.append('comp['+','.join(entries)+']')
        states[i] = 'gik'[i]
    return 'comp['+','.join(stages)+']'


def hexagon():
    body = 'import examples/eh-common\n'
    args = '{f{a}g}{h{b}i}{j{c}k}'
    shape = '[[a],[b],[c]]'
    routes = {}
    for order in permutations(range(3)):
        name = 'r'+''.join('abc'[i] for i in order)
        body += f'def {name} {args} = {route(order)}\n'
        routes[order] = name+'(a,b,c)'
    paths = [[(0,1,2),(1,0,2),(1,2,0),(2,1,0)], [(0,1,2),(0,2,1),(2,0,1),(2,1,0)]]
    composites = []
    for side, path in zip(('left', 'right'), paths):
        steps = []
        for i,(x,y) in enumerate(zip(path, path[1:])):
            name = side+'abc'[i]
            body += f'def {name} = coh [ {shape} : {routes[x]} -> {routes[y]} ]\n'
            steps.append(name+'(a,b,c)')
        composites.append('comp['+','.join(steps)+']')
    body += f'def hexcell = coh [ {shape} : {composites[0]} -> {composites[1]} ]\n'
    return body, composites


def check_rice(checkout):
    body, composites = hexagon()
    exe = checkout / 'target/release/catt_strict'
    count = 0
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder/'examples').symlink_to(checkout/'examples', target_is_directory=True)
        (folder/'Hex.catt').write_text(body)
        for degree in (3, 4, 5):
            pole = 'x'
            for _ in range(degree-1):
                pole = f'id({pole})'
            context = '(x : *)'+''.join(f' ({w} : {pole} -> {pole})' for w in 'abcdefghijkl')
            for name, pair, out in [('p','a,b','c,d'), ('q','e,f','g,h'),
                                    ('r','i,j','k,l'), ('z','i,j','k,l')]:
                context += f' ({name} : comp[{pair}] -> comp[{out}])'
            source, target = (s.replace('(a,b,c)', '(p,q,r)') for s in composites)
            for name, term in [('Cube', 'hexcell(p,q,r)'), ('Wrong', 'hexcell(p,q,z)')]:
                file = name+'.catt'
                (folder/file).write_text('import Hex\n'
                    f'def boundary {context} : {source} -> {target} = {term}\n')
                for flags in ([], ['--sua']):
                    result = run(exe, folder, file, flags)
                    if name == 'Cube':
                        accepted(result, file, ['boundary'])
                    else:
                        rejected(result, file, 'boundary')
                    count += 1
    return count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    print('Intervals, Boolean intervals and schedule simplices:', *check_intervals())
    print('Signed port sections:', check_cluster_sections())
    print('Partial name-map intersections:', check_partial_names())
    print('Lifted bridge classes with an excursion:', check_lifted_bridge())
    if args.catt_strict:
        print('Raw and SUA hexagon boundary checks:', check_rice(args.catt_strict.resolve()))
