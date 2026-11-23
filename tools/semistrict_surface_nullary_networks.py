"""Check event sheets, port expansions and specialized raw cube boundaries."""
from argparse import ArgumentParser
from itertools import combinations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from sympy import Matrix

from semistrict_surface_concurrent_rules import Network, pair_map, subsets
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_factorization import hexagon


def check_event_sheets(net):
    """Compare directed executions from the initial sheet with the ideal cubes."""
    initial = frozenset(w for w, (start, _) in enumerate(net.wires) if start is None)
    pending = [(frozenset(), initial)]
    reached = {}
    actual_cubes = set()
    while pending:
        sheet, live = pending.pop()
        if sheet in reached:
            assert reached[sheet] == live
            continue
        reached[sheet] = live
        enabled = [e for e in net.events if e not in sheet and net.inputs[e] <= live]
        for batch in subsets(enabled):
            consumed = set().union(*(net.inputs[e] for e in batch))
            created = set().union(*(net.outputs[e] for e in batch))
            stationary = live - consumed
            assert not stationary & created
            actual_cubes.add((sheet, batch, stationary))
            if batch:
                pending.append((sheet | batch, stationary | created))
    assert reached == net.cuts
    expected = set()
    for cut, live in net.cuts.items():
        for batch in subsets(set(net.events) - cut):
            if all(cut | {e} in net.cuts for e in batch):
                stationary = live.difference(*(net.inputs[e] for e in batch))
                expected.add((cut, batch, frozenset(stationary)))
    assert actual_cubes == expected
    return len(actual_cubes)


def check_frontiers():
    # The same ordinary scalar colour can occur at every port. In particular
    # there are executions with the same live colours on different sheets.
    networks = cubes = 0
    for arcs in subsets(combinations(range(3), 2)):
        for incoming, outgoing in product(subsets(range(3)), repeat=2):
            wires = (sorted(arcs) + [(None, e) for e in sorted(incoming)]
                     + [(e, None) for e in sorted(outgoing)] + [(None, None)])
            cubes += check_event_sheets(Network(3, wires))
            networks += 1
    empty = Network(3, [])
    assert len(empty.cuts) == 8 and len(set(map(frozenset, empty.cuts.values()))) == 1
    assert check_event_sheets(empty) == 27
    return networks, cubes


def check_port_sections():
    # One independent batch with two active sites and one bypass wire. Direct
    # cabling matrices also see when neither end detects the site-site class.
    sections = missing_pairs = 0
    for arities in product(range(3), repeat=4):
        before = arities[:2] + (1,)
        after = arities[2:] + (1,)
        for sign in (-1, 1):
            matrices = []
            for sizes in (before, after):
                blocks = {e: set(range(sum(sizes[:e]), sum(sizes[:e+1])))
                          for e in range(len(sizes))}
                ports = set().union(*blocks.values())
                expand = pair_map(blocks, ports, blocks, sign)
                matrices.append(expand)
                if all(sizes):
                    representatives = {w: {e for e, block in blocks.items() if w == min(block)}
                                       for w in ports}
                    assert (pair_map(ports, blocks, representatives, sign) * expand).is_Identity
                    sections += 1
            if all(matrix[:, 0].is_zero_matrix for matrix in matrices):
                assert 0 in before[:2] and 0 in after[:2]
                missing_pairs += 1
    assert missing_pairs
    return sections, missing_pairs


def port_basis(wires, blocks):
    # Columns are the block sum followed by all but its first individual port.
    columns = []
    for block in blocks:
        if block:
            columns.append(set(block))
            columns.extend({w} for w in block[1:])
    return Matrix(len(wires), len(columns), lambda i, j: int(wires[i] in columns[j]))


def check_cut_groups():
    # Transform actual cabling maps to the proposed integral bases. A transfer
    # relation may identify or kill vertices but must never multiply them.
    count = killed = 0
    for arities in product(range(3), repeat=4):
        wires = [(None, e) for e in range(2) for _ in range(arities[e])]
        wires += [(e, None) for e in range(2) for _ in range(arities[e + 2])]
        wires.append((None, None))
        net = Network(2, wires)
        for cut in net.cuts:
            for e in set(net.events) - cut:
                sites = [[~e] if k == e else sorted(net.outputs[k] if k in cut else net.inputs[k])
                         for k in net.events] + [[len(wires) - 1]]
                site_wires = sorted(w for block in sites for w in block)
                site_basis = port_basis(site_wires, sites)
                for end in (cut, cut | {e}):
                    blocks = [sorted(net.outputs[k] if k in end else net.inputs[k])
                              for k in net.events] + [[len(wires) - 1]]
                    live = sorted(net.cuts[end])
                    end_basis = port_basis(live, blocks)
                    assert abs(end_basis.det()) == abs(site_basis.det()) == 1
                    ports = {w: blocks[e] if w == ~e else [w] for w in site_wires}
                    cable = Matrix(len(live), len(site_wires),
                                   lambda i, j: int(live[i] in ports[site_wires[j]]))
                    changed = end_basis.inv() * cable * site_basis
                    for i, j in combinations(range(changed.cols), 2):
                        pair = [changed[a, i] * changed[b, j] - changed[b, i] * changed[a, j]
                                for a, b in combinations(range(changed.rows), 2)]
                        assert sum(abs(x) for x in pair) <= 1
                        killed += not any(pair)
                        count += 1
    assert killed
    return count, killed


def check_typed_cubes(checkout):
    cube, faces = hexagon()
    modes = ([], ['--sua'])
    count = 0
    with TemporaryDirectory() as directory:
        folder = Path(directory)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        (folder / 'Hex.catt').write_text(cube)
        for n in (2, 3, 4):
            pole = 'x'
            for _ in range(n - 1):
                pole = f'id({pole})'
            empty = f'id({pole})'
            context = '(x : *)' + ''.join(f' ({w} : {pole} -> {pole})' for w in 'abcd')
            for signature in ((empty, 'comp[a,b]', 'comp[c,d]', empty),
                              (empty, 'comp[a,b]', empty, 'comp[c,d]')):
                src, tgt, src2, tgt2 = signature
                rules = f' (p : {src} -> {tgt}) (q : {src2} -> {tgt2})'
                rules += f' (r : {empty} -> {empty}) (z : {empty} -> {empty})'
                left, right = (face.replace('(a,b,c)', '(p,q,r)') for face in faces)
                for name, last in (('Good', 'r'), ('Wrong', 'z')):
                    file = name + '.catt'
                    (folder / file).write_text('import Hex\n'
                        f'def boundary {context}{rules} : {left} -> {right} = hexcell(p,q,{last})\n')
                    for mode in modes:
                        result = run(checkout / 'target/release/catt_strict', folder, file, mode)
                        if name == 'Good':
                            accepted(result, file, ['boundary'])
                        else:
                            rejected(result, file, 'boundary')
                        count += 1
    return count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    print('Networks and reachable cubes:', *check_frontiers())
    print('Signed sections and pairs invisible at both ends:', *check_port_sections())
    print('Integral wedge columns, including zero images:', *check_cut_groups())
    if args.catt_strict:
        print('Raw and SUA literal hexagon checks:', check_typed_cubes(args.catt_strict.resolve()))
