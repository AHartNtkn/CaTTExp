"""Compile a guarded switch to bounded boxes and recover its constraints from the sites."""

from collections import Counter, defaultdict
from itertools import combinations, product

from homotopy_polygraph_guarded_boxes import Board, acyclic_chart


def box(lo, hi):
    return frozenset(product(*(range(a, b + 1) for a, b in zip(lo, hi))))


def route(board):
    nodes, links, arrows = {}, {}, []
    actors = set(range(board.n))
    role_sites = {}
    port_offsets = {(1, 'in'): 0, (1, 'out'): 1, (2, 'in'): 3,
                    (2, 'out'): 4, (3, 'in'): 5, (3, 'out'): 6}

    def port(i, role, direction):
        return 8 * i + port_offsets[role, direction]

    def hub(p):
        if p not in nodes:
            center = tuple(4 * v for v in p)
            nodes[p] = box(tuple(v - 1 for v in center), tuple(v + 1 for v in center))
        return p

    def connect(a, b, start, end):
        link = ('link', len(links))
        links[link] = box(tuple(map(min, zip(start, end))), tuple(map(max, zip(start, end))))
        arrows.extend([(a, link), (link, b)])

    def step(a, b):
        delta = tuple(t - s for s, t in zip(a, b))
        assert sum(map(abs, delta)) == 1
        connect(hub(a), hub(b), tuple(4 * s + d for s, d in zip(a, delta)),
                tuple(4 * t - d for t, d in zip(b, delta)))

    arcs = sorted(set(board.arcs))
    for i in actors:
        first = 32 * i
        for role, (x, y) in {1: (0, 8), 2: (8, 16), 3: (0, 24)}.items():
            role_sites[i, role] = box((first + x, 0, 0), (first + y, 0, 0))
        nodes[i] = role_sites[i, 3]
        for (role, direction), offset in port_offsets.items():
            x = 8 * i + offset
            connector = (4 * x, 0, 0), (4 * x, 3, 0)
            head = hub((x, 1, 0))
            if direction == 'out':
                connect(i, head, *connector)
            else:
                connect(head, i, *connector)
            for y in range(1, len(arcs)):
                a, b = (x, y, 0), (x, y + 1, 0)
                if direction == 'out':
                    step(a, b)
                else:
                    step(b, a)

    for y, (i, a, j, b) in enumerate(arcs, 1):
        x, t = port(i, a, 'out'), port(j, b, 'in')
        step((x, y, 0), (x, y, 1))
        step((x, y, 1), (x, y, 2))
        direction = 1 if t > x else -1
        for s in range(x, t, direction):
            step((s, y, 2), (s + direction, y, 2))
        step((t, y, 2), (t, y, 1))
        step((t, y, 1), (t, y, 0))

    # Encode the bit read by each anchored box on each middle token.
    shapes = nodes | links
    readers = defaultdict(list)
    for name, sites in shapes.items():
        for site in sites:
            readers[site].append(name)
    required_one = defaultdict(set)
    for before, after in arrows:
        site, = shapes[before] & shapes[after]
        required_one[after].add(site)

    # Recover orders from the actual two readers and their local bit templates.
    recovered = set()
    for site, names in readers.items():
        if len(names) == 1:
            continue
        a, b = names
        assert (a in nodes) != (b in nodes)
        assert (site in required_one[a]) != (site in required_one[b])
        if site in required_one[a]:
            a, b = b, a
        recovered.add((a, b))
    assert recovered == set(arrows)
    assert max(map(len, shapes.values())) == 27
    after = defaultdict(list)
    for a, b in recovered:
        after[a].append(b)

    # Eliminate interior vertices, stopping a walk on its first new actor.
    orders = defaultdict(set)
    for i in actors:
        for u in (1, 2, 3):
            seen = set()
            todo = [w for w in after[i] if role_sites[i, u] & shapes[w]]
            while todo:
                v = todo.pop()
                if v in seen:
                    continue
                seen.add(v)
                for w in after[v]:
                    if w in actors:
                        for s in (1, 2, 3):
                            if role_sites[w, s] & shapes[v]:
                                orders[i, u, w, s].add((i, w))
                    else:
                        todo.append(w)

    # The full old record flips every anchor and point. A placement of an old
    # box is pinned by its anchor; the only ambiguity is an actor's initial role.
    anchors = Counter((name in actors, name in links) for name in shapes)
    print(f'{len(shapes)} anchored boxes, {len(recovered)} contacts, '
          f'{len(readers)} occupied base sites, {anchors[True, False]} actors.')
    return orders, shapes, recovered


def audit(board):
    orders, shapes, recovered = route(board)
    passive = {v: i for i, v in enumerate(v for v in shapes if not isinstance(v, int))}
    edges = [(passive[a], passive[b]) for a, b in recovered if a in passive and b in passive]
    assert acyclic_chart(len(passive), [edges])
    pairs = tuple(combinations(range(board.n), 2))
    table = {(i, u, j, v): orders[i, u, j, v] | orders[j, v, i, u]
             for i, j in pairs for u, v in product((1, 2, 3), repeat=2)}
    for roles in product(range(4), repeat=board.n):
        simultaneous = (table[i, roles[i], j, roles[j]]
                        for i, j in pairs if roles[i] and roles[j])
        assert acyclic_chart(board.n, simultaneous) == board.guard(roles)
    print(f'Compared all {4**board.n} cubes with the original guard.')



def audit_poles():
    # A 2-by-2 board with a vertex anchor on each column and a link anchor
    # after each row. Top and bottom links impose opposite spatial orders.
    # Occurrences 0,1 are vertex anchors, 2,3 link anchors, 4..7 middle letters.
    incidences = [(x, 4 + 2*x + y) for x in range(2) for y in range(2)]
    incidences += [(4 + 2*x + y, 2 + y) for x in range(2) for y in range(2)]
    schedules = 0
    for left, right in product((1, 2, 3), repeat=2):
        # An operation consumes its unchanged read letters and flips its anchor.
        reads = [{4 + 2*x + y: x ^ y for y in range(2) if role & (1 << y)}
                 for x, role in enumerate((left, right))]
        reads += [{4 + 2*x + y: 1 ^ x ^ y for x in range(2)} for y in range(2)]
        reads += [{} for _ in range(4)]
        supports = [{i, *r} for i, r in enumerate(reads)]
        joint = set()
        for i, j in combinations(range(8), 2):
            if supports[i] & supports[j]:
                continue
            # Contract both footprints in the actual lower trace. A cycle
            # would force an exterior letter between pieces of a single slot.
            owner = {cell: slot for slot in (i, j) for cell in supports[slot]}
            edges = [(owner.get(a, a), owner.get(b, b)) for a, b in incidences]
            assert acyclic_chart(8, [[(a, b) for a, b in edges if a != b]])
            joint.add((i, j))

        def visit(mask, prefix):
            if mask == 255:
                yield prefix
                return
            for i, r in enumerate(reads):
                if not mask & (1 << i) and all((mask >> k) & 1 == bit for k, bit in r.items()):
                    yield from visit(mask | (1 << i), (*prefix, i))

        histories = set(visit(0, ()))
        schedules += len(histories)
        assert bool(histories) == (left != 3 or right != 3)
        if histories:
            todo = [histories.pop()]
            while todo:
                h = todo.pop()
                for k, (a, b) in enumerate(zip(h, h[1:])):
                    if tuple(sorted((a, b))) in joint:
                        other = (*h[:k], b, a, *h[k+2:])
                        if other in histories:
                            histories.remove(other)
                            todo.append(other)
            assert not histories
    print(f'{schedules} full histories between the two painted poles; '
          'each legal role pair has exactly one strict spatial diagram.')


if __name__ == '__main__':
    audit_poles()
    audit(Board(3, 3, [(0, 0), (1, 1), (2, 2)]))
