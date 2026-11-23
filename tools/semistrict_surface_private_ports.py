"""Check restriction of marked scalar networks and padding at a simultaneous batch."""
from argparse import ArgumentParser
from itertools import combinations, permutations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import accepted, rejected, run


def subsets(items):
    items = tuple(items)
    for k in range(len(items) + 1):
        yield from map(frozenset, combinations(items, k))


class Network:
    # Nonnegative marks name wires; ~e is the singleton mark for event e.
    def __init__(self, events, wires):
        self.events = frozenset(events)
        self.wires = dict(wires)
        self.marks = frozenset(self.wires) | {~e for e in self.events}

    def retain(self, marks):
        wires = {w: ends for w, ends in self.wires.items() if w in marks}
        events = {~m for m in marks if m < 0}
        events.update(e for ends in wires.values() for e in ends if e is not None)
        return Network(events, wires)

    def live(self, cut):
        return {w for w, (a, b) in self.wires.items()
                if (a is None or a in cut) and b not in cut}

    def expand(self, event_sites, directions):
        result = []
        for carrier in event_sites:
            if carrier >= 0 or ~carrier not in directions:
                result.append(carrier)
                continue
            e = ~carrier
            end = 0 if directions[e] == 'out' else 1
            result.extend(w for w, ends in self.wires.items() if ends[end] == e)
        return tuple(result)

    def cubes(self):
        # Compute by executable single firings at cuts reached from the source.
        pending = [frozenset()]
        seen = set(pending)
        while pending:
            cut = pending.pop()
            live = self.live(cut)
            enabled = [e for e in self.events - cut
                       if all(w in live for w, (_, b) in self.wires.items() if b == e)]
            for batch in subsets(enabled):
                stationary = {w for w in live if self.wires[w][1] not in batch}
                yield cut, batch, tuple(sorted(stationary | {~e for e in batch}))
            for e in enabled:
                new = cut | {e}
                if new not in seen:
                    seen.add(new)
                    pending.append(new)

    def pad(self, batch):
        wires = dict(self.wires)
        offset = max(wires, default=-1) + 1
        for e in sorted(batch):
            wires[offset] = (None, e)
            wires[offset+1] = (e, None)
            offset += 2
        return Network(self.events, wires)


def check_restrictions():
    net = Network(range(3), enumerate([(None, 0), (0, 2), (1, 2), (None, None)]))
    cube_count = face_count = 0
    all_cubes = list(net.cubes())
    for marks in subsets(net.marks):
        small = net.retain(marks)
        reached = set(small.cubes())
        for cut, batch, sites in all_cubes:
            projected = tuple(s for s in sites if s in small.marks)
            assert (cut & small.events, batch & small.events, projected) in reached
            cube_count += 1
            for order in permutations(sites):
                for sides in product(('in', 'out'), repeat=len(batch)):
                    expand = dict(zip(sorted(batch), sides))
                    first_expand = net.expand(order, expand)
                    first_delete = tuple(s for s in order if s in small.marks)
                    assert (tuple(s for s in first_expand if s in small.wires)
                            == small.expand(first_delete, expand))
                    face_count += 1
        for smaller in subsets(marks):
            direct = net.retain(smaller)
            twice = small.retain(smaller)
            assert (direct.events, direct.wires) == (twice.events, twice.wires)
    return cube_count, face_count


def check_batches():
    networks = batches = invisible_pairs = 0
    for arcs in subsets(combinations(range(3), 2)):
        for incoming, outgoing in product(subsets(range(3)), repeat=2):
            wires = (sorted(arcs) + [(None, e) for e in sorted(incoming)]
                     + [(e, None) for e in sorted(outgoing)] + [(None, None)])
            net = Network(range(3), enumerate(wires))
            for cut, batch, sites in net.cubes():
                if not batch:
                    continue
                padded = net.pad(batch)
                assert (cut, batch, sites) in set(padded.cubes())
                reduced = padded.retain(net.marks)
                assert (reduced.events, reduced.wires) == (net.events, net.wires)
                source = padded.live(cut)
                # The selected input over every site gives an actual section.
                picked = {s: s if s >= 0 else next(w for w in source
                          if w not in net.wires and padded.wires[w][1] == ~s) for s in sites}
                for s, t in combinations(sites, 2):
                    for order in [(s, t), (t, s)]:
                        ports = padded.expand(order, {e: 'in' for e in batch})
                        assert tuple(w for w in ports if w in picked.values()) == tuple(
                            picked[x] for x in order)
                    directions = [{e: side for e in batch} for side in ('in', 'out')]
                    if all(not net.expand((s,), side) or not net.expand((t,), side)
                           for side in directions):
                        invisible_pairs += 1
                batches += 1
            networks += 1
    assert invisible_pairs
    return networks, batches, invisible_pairs


def check_typed(checkout):
    binary = checkout / 'target/release/catt_strict'
    count = 0
    with TemporaryDirectory() as directory:
        folder = Path(directory)
        (folder / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for n in (3, 4, 5):
            pole = 'x'
            for _ in range(n-1):
                pole = f'id({pole})'
            unit = f'id({pole})'
            for u, v in [(unit, 'a'), ('a', unit), (unit, unit), ('comp[a,b]', 'b')]:
                context = (f'(x : *) (a : {pole} -> {pole}) (b : {pole} -> {pole}) '
                           f'(p : {u} -> {v}) (q : {u} -> {v})')
                args = '(x,a,b,p,q)'
                (folder / 'Fit.catt').write_text('import examples/eh-common\n'
                    f'def fitted {context} : comp[{u},{unit}] -> comp[{v},{unit}] '
                    f'= comp[unitor_r({u}),p,unitor_r_inv({v})]\n')
                accepted(run(binary, folder, 'Fit.catt'), 'Fit.catt', ['fitted'])
                (folder / 'Class.catt').write_text('import Fit\n'
                    f'def returns {context} : fitted{args} -> p = id(p)\n')
                accepted(run(binary, folder, 'Class.catt', ['--sua']), 'Class.catt', ['returns'])
                (folder / 'Different.catt').write_text('import Fit\n'
                    f'def wrong {context} : fitted{args} -> q = id(q)\n')
                rejected(run(binary, folder, 'Different.catt', ['--sua']), 'Different.catt', 'wrong')
                count += 3
    return count


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    print('Restricted cubes and ordered endpoint expansions:', *check_restrictions())
    print('Networks, padded batches and pairs invisible at both original ends:', *check_batches())
    if args.catt_strict:
        print('Weak and insertion checks at actual rule boundaries:',
              check_typed(args.catt_strict.resolve()))
