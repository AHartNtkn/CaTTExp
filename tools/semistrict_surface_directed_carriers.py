"""Check directed configuration carriers and port erasures for the rank-three square."""
from argparse import ArgumentParser
from itertools import combinations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_configuration_blocks import block, subsets
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_forest_expansion import graph, substitute


# Each event has four traversing paths, one for each input/output combination.
PATHS = tuple(product(range(2), repeat=3))


def ports(paths, phases):
    result = {}
    for e, i, j in paths:
        phase = phases[e]
        port = (e, phase, (i, 0, j)[phase])  # input, event site, output
        result.setdefault(port, set()).add((e, i, j))
    return result


def retract(value, level, reverse):
    groups = [value.restrict([p for p in value.order if p[0] == e]) for e in range(2)]
    if reverse:
        groups.reverse()
    return block(*groups, level)


def leq(left, right):
    il = {p: i for i, p in enumerate(left.order)}
    ir = {p: i for i, p in enumerate(right.order)}
    for (p, q, a), (u, v, b) in zip(left.levels, right.levels, strict=True):
        assert (p, q) == (u, v)
        if a > b or (a == b and (il[p] < il[q]) != (ir[p] < ir[q])):
            return False
    return True


def insert(value, source, target):
    # A cube face inserts the endpoint vertex at its site; all other sites
    # have one retained port. The token order fixes the endpoint bracketing.
    fibres = {p: graph(sorted(q for q, marks in target.items() if marks <= source[p]), 2)
              for p in value.order}
    return substitute(value, fibres)


def check_cubes():
    face_count = erase_count = mixed_orders = 0
    for paths in subsets(PATHS):
        for phases in product(range(3), repeat=2):
            source = ports(paths, phases)
            order = sorted(source, key=lambda p: (p[2], p[0], p[1]))
            value = graph(order, 2)
            for reverse, level in product((False, True), range(3)):
                split = retract(value, level, reverse)
                if not leq(split, value):
                    continue
                mixed_orders += value.order != split.order
                for i, phase in enumerate(phases):
                    if phase == 1:
                        for side in (0, 2):
                            new = list(phases)
                            new[i] = side
                            target = ports(paths, new)
                            direct = retract(insert(value, source, target), level, reverse)
                            assert direct == insert(split, source, target)
                            face_count += 1
                for forgotten in paths:
                    remaining = ports(paths - {forgotten}, phases)
                    assert split.restrict(remaining) == retract(value.restrict(remaining), level, reverse)
                    erase_count += 1
    return face_count, erase_count, mixed_orders


def check_site_tests():
    # Pairs at the same event site carry no graph edge. Independently inspect
    # both corners to verify exactly which lower bounds allow its characteristic arrow.
    count = excluded = 0
    for chosen in subsets([p for p in PATHS if p[0] == 0]):
        for p, q in combinations(sorted(chosen), 2):
            for level, sign in product(range(3), (-1, 1)):
                def allowed(edge):
                    return edge is None or edge[0] > level or edge == (level, sign)
                ends = []
                for phase in (0, 2):
                    carriers = ports(chosen, (phase, 0))
                    ordered = sorted(carriers)
                    a, b = (next(i for i, k in enumerate(ordered) if r in carriers[k]) for r in (p, q))
                    if a != b:
                        ends.append((2, 1 if a < b else -1))
                site_allowed = all(map(allowed, ends))
                vertex = graph(ports(chosen, (1, 0)), 0)
                corner_tests = []
                for phase in (0, 2):
                    carriers = ports(chosen, (phase, 0))
                    corner = insert(vertex, ports(chosen, (1, 0)), carriers)
                    a, b = (next(k for k in corner.order if r in carriers[k]) for r in (p, q))
                    if a == b:
                        corner_tests.append(True)
                    else:
                        h = next(h for x, y, h in corner.levels if {x, y} == {a, b})
                        corner_tests.append(allowed((h, 1 if corner.order.index(a) < corner.order.index(b) else -1)))
                assert site_allowed == all(corner_tests)
                count += 1
                excluded += not site_allowed
    assert excluded
    return count, excluded


def check_class_two():
    # Integral Heisenberg quotient. Conjugation can change the central entry
    # of a cut generator, while the commutator reads the determinant.
    def mul(p, q):
        a, b, c = p
        x, y, z = q
        return a+x, b+y, c+z+a*y

    def inv(p):
        a, b, c = p
        return -a, -b, a*b-c

    count = 0
    for a, b in product((-3, -1, 1, 3), repeat=2):
        for c, d in product(range(-2, 3), repeat=2):
            p, q = (a, 0, c), (0, b, d)
            word = mul(mul(p, q), mul(inv(p), inv(q)))
            assert word == (0, 0, a*b)
            count += 1
    return count


def check_rice(checkout):
    binary = checkout / 'target/release/catt_strict'
    scalar = 'id(id(x)) -> id(id(x))'
    unit = 'id(id(id(x)))'
    names = 'abcdefgh'
    def composite(seq):
        return 'comp['+','.join(seq)+']' if len(seq) > 1 else (seq[0] if seq else unit)

    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        generic = '(x : *)' + ''.join(f' ({z} : {scalar})' for z in names)
        generic += ' (p : comp[a,b] -> comp[c,d]) (q : comp[e,f] -> comp[g,h])'
        (folder / 'Route.catt').write_text('import examples/eh-common\n'
            f'def route {generic} = swap_src(p,q)\n')
        lines = ['import Route']
        expected = []
        for number, paths in enumerate(subsets(PATHS)):
            ends = [ports(paths, (s,s)) for s in (0, 2)]
            kept = {names[4*e+s+i] for end in ends for e,s,i in end}
            ctx = '(x : *)' + ''.join(f' ({z} : {scalar})' for z in names if z in kept)
            args = ['x'] + [z if z in kept else unit for z in names]
            active = []
            for e, rule in enumerate('pq'):
                ins = [z for z in names[4*e:4*e+2] if z in kept]
                outs = [z for z in names[4*e+2:4*e+4] if z in kept]
                if ins:
                    ctx += f' ({rule} : {composite(ins)} -> {composite(outs)})'
                    args.append(rule)
                    active.append(rule)
                else:
                    assert not outs
                    args.append(f'id({unit})')
            short = 'swap_src(p,q)' if len(active) == 2 else (active[0] if active else f'id({unit})')
            name = f'erase_{number}'
            lines.append(f'def {name} {ctx} : route({",".join(args)}) -> {short} = id({short})')
            expected.append(name)
        (folder / 'Delete.catt').write_text('\n'.join(lines)+'\n')
        accepted(run(binary, folder, 'Delete.catt', ['--sua']), 'Delete.catt', expected)
        wrong = generic + ' (v : comp[a,b] -> comp[c,d])'
        (folder / 'Wrong.catt').write_text('import Route\n'
            f'def wrong {wrong} : swap_src(p,q) -> swap_src(v,q) = id(swap_src(v,q))\n')
        rejected(run(binary, folder, 'Wrong.catt', ['--sua']), 'Wrong.catt', 'wrong')
    return len(expected)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    print('Split cube faces, one-path deletions, interleaved orders:', *check_cubes())
    print('Site bounds tested and excluded at their endpoints:', *check_site_tests())
    print('Nonzero commutator images in the class-two quotient:', check_class_two())
    if args.catt_strict:
        print('Published-insertion boundary restrictions checked:', check_rice(args.catt_strict.resolve()))
