"""Check configuration block composition on coherent subset cones and a mixed attachment."""
from argparse import ArgumentParser
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import accepted, rejected, run


@dataclass(frozen=True)
class Graph:
    order: tuple
    levels: tuple

    def restrict(self, keep):
        return Graph(tuple(i for i in self.order if i in keep),
                     tuple((i, j, l) for i, j, l in self.levels if i in keep and j in keep))


def block(left, right, level):
    crossing = tuple((*sorted((i, j)), level) for i in left.order for j in right.order)
    return Graph(left.order + right.order, tuple(sorted(left.levels + right.levels + crossing)))


def subsets(names):
    return tuple(frozenset(s) for size in range(len(names)+1) for s in combinations(names, size))


def project(chain, names):
    # A degeneracy accumulates the barycentric weights of equal consecutive sets.
    result = []
    for s, weight in chain:
        t = s & names
        if result and result[-1][0] == t:
            result[-1] = (t, result[-1][1] + weight)
        else:
            result.append((t, weight))
    return tuple(result)


def path_at(chain, order, fraction, quantile):
    # A point of the nerve is a weighted chain of graphs. Read its graph at
    # the specified quantile; a product of nerves uses the same quantile.
    clock = 1 + sum(w * len(s) for s, w in chain)
    names = tuple(i for i in order if i in chain[-1][0])
    level = int(quantile < fraction)
    return clock, Graph(names, tuple((i, j, level) for i, j in combinations(sorted(names), 2)))


def serial(left, right, level):
    def evaluate(chain, fraction, quantile):
        lclock, _ = left(chain, 0, quantile)
        rclock, _ = right(chain, 0, quantile)
        time = fraction * (lclock+rclock)
        a = min(1, time/lclock) if lclock else 0
        b = max(0, (time-lclock)/rclock) if rclock else 0
        return lclock+rclock, block(left(chain, a, quantile)[1], right(chain, b, quantile)[1], level)
    return evaluate


def named(order):
    def evaluate(chain, fraction, quantile):
        return path_at(project(chain, frozenset(order)), order, fraction, quantile)
    return evaluate


def check_cones():
    names = frozenset(range(4))
    all_sets = subsets(names)
    chains = [((s, Fraction(1, 4)), (t, Fraction(1, 2)), (u, Fraction(1, 4)))
              for s in all_sets for t in all_sets if t <= s for u in all_sets if u <= t]
    orders = ((2, 0), (3,), (1,))
    parts = list(map(named, orders))
    empty = Graph((), ())
    def unit(chain, fraction, quantile):
        return 0, empty
    counts = dict(associativities=0, faces=0, units=0)
    for level in range(3):
        left = serial(serial(parts[0], parts[1], level), parts[2], level)
        right = serial(parts[0], serial(parts[1], parts[2], level), level)
        for chain in chains:
            for fraction, quantile in product(map(Fraction, ('0','1/5','2/3','1')),
                                              map(Fraction, ('1/6','3/4'))):
                value = left(chain, fraction, quantile)
                assert value == right(chain, fraction, quantile)
                assert value == left(project(chain, names), fraction, quantile)
                assert value[0] == 3 + sum(w*len(s) for s, w in chain)
                counts['associativities'] += 1
                # At the final face restrict the preceding graph while keeping
                # its clock; zero barycentric weight implements that face.
                previous = ((chain[0][0], Fraction(1, 3)), (chain[1][0], Fraction(2, 3)))
                before, g = left(previous, fraction, quantile)
                after = left(previous + ((chain[2][0], 0),), fraction, quantile)
                assert after == (before, g.restrict(chain[2][0]))
                counts['faces'] += 1
                for joined in (serial(unit, parts[0], level), serial(parts[0], unit, level)):
                    assert joined(chain, fraction, quantile) == parts[0](chain, fraction, quantile)
                    counts['units'] += 1
    # Erasing all names in a moving block retains a positive empty clock.
    empty_chain = ((frozenset(), Fraction(1)),)
    assert parts[0](empty_chain, 1, 0) == (1, empty)
    assert unit(empty_chain, 1, 0) == (0, empty)
    return counts


def check_orders():
    count = 0
    for order in permutations(range(4)):
        a = Graph(order[:2], ((*sorted(order[:2]), 2),))
        b, c = (Graph((i,), ()) for i in order[2:])
        for i, j in product(range(3), repeat=2):
            # At a cut the outer level is the minimum of the two gap levels.
            if i <= j:
                result = block(a, block(b, c, j), i)
            else:
                result = block(block(a, b, i), c, j)
            assert result.order == order
            expected = {tuple(sorted((x, y))): l for x, y, l in
                        [(order[0], order[1], 2), (order[2], order[3], j)]
                        + [(x, order[2], i) for x in order[:2]]
                        + [(x, order[3], min(i, j)) for x in order[:2]]}
            assert result.levels == tuple(sorted((*e, l) for e, l in expected.items()))
            for s in subsets(order):
                x, y, z = (g.restrict(s) for g in (a, b, c))
                out = block(x, block(y, z, j), i) if i <= j else block(block(x, y, i), z, j)
                assert out == result.restrict(s)
                count += 1
    return count


def check_attachment(checkout, seam):
    binary = checkout / 'target/release/catt_strict'
    base = '(x : *) (a : id(id(x)) -> id(id(x)))'
    ctx = base + ''.join(f' ({p} : {seam} -> {seam})' for p in 'uvwt')
    ctx += f' (z : comp[comp[comp[id({seam}),u],v],w] -> t)'
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'Fit.catt').write_text(f"""def fit = coh [ x{{u}}y{{v}}z{{w}}t : comp[u,comp[v,w]] -> comp[comp[comp[id(x),u],v],w] ]
def raw_fit {ctx} : comp[u,comp[v,w]] -> t = comp[fit(u,v,w),z]
""")
        accepted(run(binary, folder, 'Fit.catt'), 'Fit.catt', ['raw_fit'])
        for filename, name, boundary in [('Convert', 'convert', 'comp[u,comp[v,w]] -> t'),
                                         ('Reverse', 'reverse', 't -> comp[u,comp[v,w]]')]:
            path = filename + '.catt'
            (folder / path).write_text(f'def {name} {ctx} : {boundary} = z\n')
            rejected(run(binary, folder, path), path, name)
            result = run(binary, folder, path, ['--sua'])
            if name == 'convert':
                accepted(result, path, [name])
            else:
                rejected(result, path, name)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    print('Block restrictions at mixed cuts:', check_orders())
    print('Barycentric subset cones:', check_cones())
    if args.catt_strict:
        for first_degree in (4, 7):
            seam = 'comp[a,a]'
            for _ in range(first_degree - 4):
                seam = f'id({seam})'
            check_attachment(args.catt_strict.resolve(), seam)
            print(f'First attachment in degree {first_degree}: both boundaries checked in degree {first_degree+1}.')
