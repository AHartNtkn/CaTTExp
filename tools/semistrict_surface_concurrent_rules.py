"""Check path multigrades, cut projections and the independent-rule square."""
from argparse import ArgumentParser
from itertools import combinations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from sympy import Matrix, zeros
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_shared_edge import braid_image, inverse
from semistrict_surface_planar_tiers import reduce_letters


def subsets(items):
    items = sorted(items)
    for count in range(len(items) + 1):
        for selected in combinations(items, count):
            yield frozenset(selected)


class Network:
    """Wires run from an earlier event (or source) to a later event (or sink)."""

    def __init__(self, count, wires):
        self.events = range(count)
        self.wires = wires
        self.inputs = [{k for k, (_, t) in enumerate(wires) if t == e} for e in self.events]
        self.outputs = [{k for k, (s, _) in enumerate(wires) if s == e} for e in self.events]
        self.cuts = {}
        for cut in subsets(self.events):
            if all(s is None or s in cut for s, t in wires if t in cut):
                self.cuts[cut] = {k for k, (s, t) in enumerate(wires)
                                  if (s is None or s in cut) and t not in cut}

    def check_frontiers(self):
        # Negative labels distinguish marked events from occupied wires.
        paths = []

        def extend(path, k):
            _, target = self.wires[k]
            path = path | {k}
            if target is None:
                paths.append(path)
            else:
                for following in self.outputs[target]:
                    extend(path | {~target}, following)

        for k in self.cuts[frozenset()]:
            extend(set(), k)
        # Exact covers in the path multigrade, independent of the cut enumeration.
        covers = set()
        def search(remaining, selected):
            if not remaining:
                covers.add(frozenset(selected))
                return
            for marker in paths[min(remaining)]:
                hits = {i for i, p in enumerate(paths) if marker in p}
                if hits <= remaining:
                    search(remaining-hits, selected | {marker})
        search(set(range(len(paths))), set())

        cubes = set()
        for cut, live in self.cuts.items():
            enabled = {e for e in self.events if self.inputs[e] <= live}
            for batch in subsets(enabled):
                stationary = live.difference(*(self.inputs[e] for e in batch))
                cubes.add(frozenset(stationary | {~e for e in batch}))
        assert covers == cubes
        return len(cubes)

    def blocks(self, anchor):
        assigned = {w: {w} for w in self.cuts[anchor]}
        for e in sorted(anchor, reverse=True):
            self.concentrate(assigned, self.outputs[e], self.inputs[e])
        for e in self.events:
            if e not in anchor:
                self.concentrate(assigned, self.inputs[e], self.outputs[e])
        return assigned

    @staticmethod
    def concentrate(assigned, incident, opposite):
        names = set().union(*(assigned[w] for w in incident))
        for w in opposite:
            assigned[w] = names if w == min(opposite) else set()


def pair_map(source, target, blocks, parity):
    left = list(combinations(sorted(source), 2))
    right = list(combinations(sorted(target), 2))

    def entry(i, j):
        x, y = right[i]
        p, q = left[j]
        return int(x in blocks[p] and y in blocks[q]) + parity*int(x in blocks[q] and y in blocks[p])

    return Matrix(len(right), len(left), entry)


def cut_matrices(net, parity):
    cuts = list(net.cuts)
    sizes = [len(list(combinations(net.cuts[c], 2))) for c in cuts]
    rows = []
    for anchor in cuts:
        blocks = net.blocks(anchor)
        rows.append(Matrix.hstack(*(pair_map(net.cuts[c], net.cuts[anchor], blocks, parity) for c in cuts)))
    cols = []
    for c, live in net.cuts.items():
        for e in net.events:
            after = c | {e}
            if e in c or after not in net.cuts:
                continue
            stationary = live - net.inputs[e]
            site = stationary | {~e}
            same = {w: {w} for w in stationary}
            a = pair_map(site, live, same | {~e: net.inputs[e]}, parity)
            b = pair_map(site, net.cuts[after], same | {~e: net.outputs[e]}, parity)
            blocks = [zeros(s, a.cols) for s in sizes]
            blocks[cuts.index(c)] = a
            blocks[cuts.index(after)] = -b
            cols.append(Matrix.vstack(*blocks))
    probes, rels = Matrix.vstack(*rows), Matrix.hstack(*cols)
    assert (probes*rels).is_zero_matrix
    ranks = (probes.cols, rels.rank(), probes.rank())
    assert ranks[0] == sum(ranks[1:])
    return ranks


def check_square(net):
    # In either middle cut, the mixed-pair alternating functional annihilates
    # the two incident clustering maps. Opposite orders give distinct letters.
    for first, second in ((0, 1), (1, 0)):
        middle = net.cuts[frozenset([first])]
        left, right = sorted(net.outputs[first]), sorted(net.inputs[second])
        basis = list(combinations(sorted(middle), 2))
        values = {tuple(sorted((x, y))): (-1)**(i+j)*(1 if x < y else -1)
                  for i, x in enumerate(left) for j, y in enumerate(right)}
        test = Matrix([[values.get(pair, 0) for pair in basis]])
        incident = []
        for e, cluster in ((first, set(left)), (second, set(right))):
            rest = middle - cluster
            blocks = {w: {w} for w in rest} | {~e: cluster}
            incident.append(pair_map(rest | {~e}, middle, blocks, -1))
        assert (test*Matrix.hstack(*incident)).is_zero_matrix
        assert Matrix.hstack(*incident).rank() == 5 and 1 in test
    a, b = Matrix([[1, 1], [0, 1]]), Matrix([[1, 0], [1, 1]])
    assert a*b*a.inv()*b.inv() != Matrix.eye(2)


def cable(word, sizes):
    # Replace each moving strand by its parallel copies. Zero copies forget it.
    sizes = list(sizes)
    result = []
    for crossing in word:
        i = abs(crossing)-1
        a, b = sizes[i:i+2]
        offset = sum(sizes[:i])
        sign = 1 if crossing > 0 else -1
        for k in range(b):
            for j in reversed(range(a)):
                result.append(sign*(offset+k+j+1))
        sizes[i:i+2] = [b, a]
    return tuple(result)


def check_planar():
    gens = [(1, 1), (2, 2), (3, 3), (1, 2, 2, -1), (2, 3, 3, -2)]
    gens += list(map(inverse, gens))
    left, right = [2, 0, 1, 1], [1, 1, 2, 0]
    count = 0
    for p, q in product(gens, repeat=2):
        word = p+q
        together = braid_image(4, cable(word, [2, 0, 2, 0]))
        assert braid_image(4, cable(cable(word, left), right)) == together
        assert braid_image(4, cable(cable(word, right), left)) == together
        count += 1
    # At the middle cut, an alternating sum of the four cross-block linking
    # numbers vanishes after either cabling. It can obstruct a simultaneous batch.
    def alternating(word):
        order = list(range(4))
        value = 0
        for x in word:
            j = abs(x)-1
            l, r = sorted(order[j:j+2])
            if l < 2 <= r:
                value += (1 if x > 0 else -1)*(-1)**(l+r)
            order[j:j+2] = order[j:j+2][::-1]
        return value
    for g in gens:
        assert alternating(cable(g, left)) == alternating(cable(g, right)) == 0
    assert alternating((2, 2)) != 0
    return count


def check_planar_links():
    # At a six-wire cut the three prospective edges cluster disjoint pairs.
    # Check feasibility by intersecting cosets of the actual pure braid
    # subgroups with the cabling projections, including incompatible edges.
    from functools import lru_cache

    @lru_cache(None)
    def project(i, word):
        sizes = [1]*6
        sizes[2*i:2*i+2] = [2, 0]
        return reduce_letters(cable(word, sizes))

    @lru_cache(None)
    def artin(word):
        return braid_image(6, word)

    def feasible(reps, indices):
        x = ()
        done = []
        for i in indices:
            y = reduce_letters(inverse(x) + reps[i])
            for j in done:
                y = project(j, y)
            x = reduce_letters(x+y)
            done.append(i)
            delta = reduce_letters(inverse(reps[i])+x)
            if artin(project(i, delta)) != artin(delta):
                return False
        for j in done:
            delta = reduce_letters(inverse(reps[j])+x)
            assert artin(project(j, delta)) == artin(delta)
        return True

    good = bad = 0
    for reps in product(((), (2, 2), (4, 4), (2, 2, 3, 3)), repeat=3):
        pairs = all(feasible(reps, pair) for pair in combinations(range(3), 2))
        assert feasible(reps, (0, 1, 2)) == feasible(reps, (2, 1, 0)) == pairs
        good += pairs
        bad += not pairs
    assert good and bad
    return good, bad


def check_rice(checkout):
    exe = checkout / 'target/release/catt_strict'
    scalar = 'id(id(x)) -> id(id(x))'
    ctx = '(x : *)' + ''.join(f' ({p} : {scalar})' for p in 'abcdefgh')
    ctx += ' (p : comp[a,b] -> comp[c,d]) (q : comp[e,f] -> comp[g,h])'
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for name, term in [('Cross', 'swap(p,q)'), ('Wrong', 'swap(q,p)')]:
            file = name + '.catt'
            (folder / file).write_text('import examples/eh-common\n'
                f'def crossing {ctx} : swap_src(p,q) -> swap_tgt(p,q) = {term}\n')
            for flags in ([], ['--sua']):
                result = run(exe, folder, file, flags)
                if name == 'Cross':
                    accepted(result, file, ['crossing'])
                else:
                    rejected(result, file, 'crossing')

        (folder / 'Three.catt').write_text("""import examples/eh-common
def initial {f{a}g}{h{b}i}{j{c}k} = swap_src(swap_src(a,b),c)
def reversed {f{a}g}{h{b}i}{j{c}k} = swap_tgt(swap_tgt(a,b),c)
def outward = coh [ [[a],[b],[c]] : initial(a,b,c) -> reversed(a,b,c) ]
def back = coh [ [[a],[b],[c]] : reversed(a,b,c) -> initial(a,b,c) ]
def roundtrip = coh [ [[a],[b],[c]] : comp[outward(a,b,c),back(a,b,c)] -> id(initial(a,b,c)) ]
""")
        planar = '(x : *)' + ''.join(f' ({p} : id(x) -> id(x))' for p in 'abcdefghijkl')
        for name, a, b, c, d in (('p', 'a','b','c','d'), ('q', 'e','f','g','h'), ('r', 'i','j','k','l')):
            planar += f' ({name} : comp[{a},{b}] -> comp[{c},{d}])'
        (folder / 'Planar.catt').write_text('import Three\n' +
            f'def fill {planar} : comp[outward(p,q,r),back(p,q,r)] -> id(initial(p,q,r)) = roundtrip(p,q,r)\n')
        for flags in ([], ['--sua']):
            accepted(run(exe, folder, 'Planar.catt', flags), 'Planar.catt', ['fill'])


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    count = 0
    for arcs in subsets(combinations(range(4), 2)):
        wires = [(None, e) for e in range(4)] + [(e, None) for e in range(4)] + sorted(arcs)
        count += Network(4, wires).check_frontiers()
    print('Path multigrade frontiers over all 64 four-event edge sets:', count)
    square = Network(2, [(None, 0)]*2 + [(0, None)]*2 + [(None, 1)]*2 + [(1, None)]*2)
    fork = Network(3, [(None, 0), (0, 1), (0, 2), (None, 1), (None, 2), (1, None), (2, None)])
    for net in (square, fork):
        for sign in (1, -1):
            print('Pair generators, relation rank, probe rank:', cut_matrices(net, sign))
    check_square(square)
    print('Planar two-block braid projections:', check_planar())
    print('Six-strand coset triples with and without a common lift:', *check_planar_links())
    if args.catt_strict:
        check_rice(args.catt_strict.resolve())
        print('Checked the rank-three exchange and a planar three-rule round trip at their degree-five boundaries.')
