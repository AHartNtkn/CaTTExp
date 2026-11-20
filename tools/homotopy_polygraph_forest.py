"""Decide one-monotone-guard rings with a forest of binary links."""

from collections import defaultdict
from functools import cache
from itertools import combinations, permutations, product

from homotopy_polygraph_causal_routes import binary_users, can_relay, circle_routes
from homotopy_polygraph_transfer_complexity import control


def root_forest(neighbors):
    depth = {}
    for root in range(len(neighbors)):
        if root in depth:
            continue
        depth[root] = 0
        pending = [(root, None)]
        while pending:
            here, parent = pending.pop()
            for other in neighbors[here]:
                if other == parent:
                    continue
                if other in depth:
                    raise ValueError("binary links contain an undirected cycle")
                depth[other] = depth[here] + 1
                pending.append((other, here))
    return depth


def pack_and_hit(paths, depth):
    """A maximum packing and an equal-size transversal of tree paths."""
    paths = sorted(paths, key=lambda p: min(depth[i] for i in p), reverse=True)
    packing, hits = [], set()
    for path in paths:
        if hits.isdisjoint(path):
            packing.append(path)
            hits.add(min(path, key=depth.__getitem__))
    return packing, hits


def forest_certificates(controls, main):
    users = binary_users(controls, main)
    neighbors = [defaultdict(list) for _ in controls]
    for r, actors in users.items():
        if len(actors) == 2:
            i, j = actors
            neighbors[i][j].append(r)
            neighbors[j][i].append(r)
    depth = root_forest(neighbors)

    @cache
    def relay(actor, incoming, outgoing):
        return can_relay(controls[actor], incoming, outgoing)

    paths = []
    for start in range(len(controls)):
        # Pool feasible port names at each vertex on its unique path from start.
        pending = [((start,), {main})]
        while pending:
            path, ports = pending.pop()
            here = path[-1]
            if len(path) > 1 and any(relay(here, r, main) for r in ports):
                paths.append(path)
            for other, links in neighbors[here].items():
                if len(path) > 1 and other == path[-2]:
                    continue
                reachable = {s for s in links if any(relay(here, r, s) for r in ports)}
                if reachable:
                    pending.append(((*path, other), reachable))
    return pack_and_hit(paths, depth)


def check_packing():
    edges = list(combinations(range(4), 2))
    tested = 0
    for selected in combinations(edges, 3):
        neighbors = [set() for _ in range(4)]
        for a,b in selected:
            neighbors[a].add(b)
            neighbors[b].add(a)
        try:
            depth = root_forest(neighbors)
        except ValueError:
            continue
        paths = []
        for i in range(4):
            pending = [(i,)]
            while pending:
                path = pending.pop()
                if path[0] <= path[-1]:
                    paths.append(path)
                pending.extend((*path,j) for j in neighbors[path[-1]] if j not in path)
        for mask in range(1 << len(paths)):
            selected_paths = [p for i,p in enumerate(paths) if mask & (1 << i)]
            packing, hits = pack_and_hit(selected_paths, depth)
            assert all(hits.intersection(p) for p in selected_paths)
            assert sum(map(len,packing)) == len({v for p in packing for v in p})
            assert len(hits) == len(packing)
            tested += 1
    print(f'{tested:,} tree-path families have equal certified packing and transversal sizes.')


def check_two_chains():
    # For each row order take the largest nested-column subrelation of the
    # forbidden matrix: each column receives its longest allowed initial segment.
    for size in range(3,7):
        all_missing = sum(1 << (i*size+j) for i,j in product(range(size),repeat=2)
                          if (i-j) % size not in (0,1))
        subrelations = set()
        for order in permutations(range(size)):
            relation = 0
            for j in range(size):
                for i in order:
                    bit = 1 << (i*size+j)
                    if not (all_missing & bit):
                        break
                    relation |= bit
            subrelations.add(relation)
        assert all(a | b != all_missing for a,b in product(subrelations,repeat=2))
    print('Two ordered chains cannot cover the missing entries of induced 6-, 8-, 10- or 12-cycles.')


def check():
    check_packing()
    check_two_chains()
    g = 'main'
    for split in range(1,5):
        # Four sources and four sinks via this many independent hubs.
        # Each spoke uses parallel binary links, with one dead port alternative.
        controls = [control([(g,('in',i)),(g,('dead',i))]) for i in range(4)]
        controls += [control([(('out',i),g)]) for i in range(4)]
        for h in range(split):
            group = range(h,4,split)
            hub = control([(('in',i),('out',j)) for i in group for j in group])
            for i in group:
                hub.append((0,('P',('dead',i)),len(hub)+100))
            controls.append(hub)
        packing, hits = forest_certificates(controls,g)
        assert len(packing) == len(hits) == split
        assert bool(circle_routes(controls,g)) == (split >= 3)
        print(f'{split} hub(s), packing {len(packing)}, hitting set {sorted(hits)}.')
    controls = [control([(g,0)]), control([(0,g)]), control([(g,1)]), control([(1,g)]),
                control([(g,2)]), [(0,('P',2),1),(1,None,2),(2,('V',3),3)], control([(3,g)])]
    assert len(forest_certificates(controls,g)[0]) == 3
    controls[5] = [edge for edge in controls[5] if edge[1] is not None]
    assert len(forest_certificates(controls,g)[0]) == 2
    print('Changing reachability inside one relay changes the whole-presentation decision.')


if __name__ == '__main__':
    check()
