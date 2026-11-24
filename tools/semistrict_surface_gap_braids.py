"""Decide tracks of positioned interval and empty-word events on a graph path."""

from argparse import ArgumentParser
from itertools import combinations, combinations_with_replacement, permutations, product

from semistrict_surface_interval_braids import parse_pairs
from semistrict_surface_planar_occurrences import component_transport, switches
from semistrict_surface_shared_edge import braid_image


def sites(slots):
    """Each gap reading retains just its selected floating occurrence."""
    for lane in range(max((b for _, b in slots), default=0)):
        yield ('wire', lane), {i for i, (a, b) in enumerate(slots) if a <= lane < b}
    for index, (gap, end) in enumerate(slots):
        if gap == end:
            rods = {i for i, (a, b) in enumerate(slots) if a < gap < b}
            yield ('scalar', index), rods | {index}


def observe(slots, order, moves):
    order = list(order)
    readers = list(sites(slots))
    words = [[] for _ in readers]
    for pos, sign in moves:
        if not 0 <= pos < len(order) - 1:
            raise ValueError('exchange position outside the serial word')
        a, b = order[pos:pos+2]
        shared = [i for i, (_, members) in enumerate(readers) if a in members and b in members]
        if sign not in ((-1, 1) if shared else (0,)):
            raise ValueError('use sign +/-1 for a shared site and 0 for an independent pair')
        for i in shared:
            members = readers[i][1]
            index = 1 + sum(event in members for event in order[:pos])
            words[i].append(sign * index)
        order[pos:pos+2] = b, a
    actions = {key: braid_image(len(members), word)
               for (key, members), word in zip(readers, words)}
    return tuple(order), actions


def rules_and_words(slots):
    rules = {i: ('x' * (b-a), 'x' * (b-a)) for i, (a, b) in enumerate(slots)}
    words = {tuple((i, slots[i][0]) for i in order) for order in permutations(rules)}
    return rules, words


def check_components(slots):
    rules, words = rules_and_words(slots)
    readers = list(sites(slots))

    def signature(word):
        return tuple(tuple(i for i, _ in word if i in members) for _, members in readers)

    seen = set()
    for root, component, rigid in component_transport(words, rules):
        key = signature(root)
        assert rigid and key not in seen
        assert all(signature(word) == key for word in component)
        seen.add(key)
    return len(seen)


def check_faces(slots):
    """Use actual lower serial spellings to orient each triple or pair of pairs."""
    rules, words = rules_and_words(slots)
    serial = tuple(range(len(slots)))

    def route(moves, lower_order):
        current = list(serial)
        path = []
        for pos in moves:
            a, b = current[pos:pos+2]
            pair = ((a, slots[a][0]), (b, slots[b][0]))
            sign = 0 if list(switches(pair, rules)) else (1 if lower_order.index(a) < lower_order.index(b) else -1)
            path.append((pos, sign))
            current[pos:pos+2] = b, a
        return observe(slots, serial, path)

    routes = ((0, 1, 0), (1, 0, 1)) if len(serial) == 3 else ((0, 2), (2, 0))
    for word in words:
        lower_order = tuple(i for i, _ in word)
        assert route(routes[0], lower_order) == route(routes[1], lower_order)
    return len(words)


def audit():
    poses = tuple(combinations_with_replacement(range(3), 2))
    components = hexagons = squares = 0
    for slots in product(poses, repeat=3):
        components += check_components(slots)
        hexagons += check_faces(slots)
    # Reorder each set of footprints so every disjoint pairing is tested.
    for slots in combinations_with_replacement(poses, 4):
        for order in ((0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2)):
            squares += check_faces(tuple(slots[i] for i in order))
    print('two-wire triples: lower components, hexagon spellings:', components, hexagons)
    print('four-event disjoint-block square spellings:', squares)

    slots = [(0, 2), (1, 1), (1, 1)]
    order = (0, 1, 2)
    moves = [(0, 1), (0, 1), (1, 0), (0, -1), (0, -1), (1, 0)]
    end, action = observe(slots, order, moves)
    _, identity = observe(slots, order, ())
    assert end == order and sum(s for _, s in moves) == 0
    assert all(action['wire', i] == identity['wire', i] for i in range(2))
    assert action['scalar', 1] == braid_image(2, (1, 1)) != identity['scalar', 1]
    assert action['scalar', 2] == braid_image(2, (-1, -1)) != identity['scalar', 2]
    # Swapping two copies of one scalar changes their named endpoint alone.
    slots = [(0, 0)] * 2
    end, action = observe(slots, (0, 1), [(0, 0)])
    assert end == (1, 0) and action == observe(slots, (0, 1), ())[1]
    rules, words = rules_and_words(slots)
    assert len(words) == 2 and all(len(list(switches(w, rules))) == 2 for w in words)
    print('opposite scalar windings and equal-colour endpoint permutation detected')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--intervals', nargs='+', metavar='A,B', help='wire interval [A,B) or scalar at gap A=B')
    parser.add_argument('--moves', nargs='*', default=[], metavar='I,S', help='adjacent position and chart sign')
    args = parser.parse_args()
    if args.intervals:
        try:
            slots = parse_pairs(args.intervals)
            if any(not 0 <= a <= b for a, b in slots):
                raise ValueError('each footprint must satisfy 0 <= A <= B')
            end, actions = observe(slots, range(len(slots)), parse_pairs(args.moves))
        except ValueError as error:
            parser.error(str(error))
        print('named endpoint:', end)
        for site, action in actions.items():
            print(*site, 'Artin action:', action)
    elif args.moves:
        parser.error('--moves requires --intervals')
    else:
        audit()
