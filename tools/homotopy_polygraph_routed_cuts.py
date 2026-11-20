"""Cut actual transfer paths and check their coloured middle words and time fibres."""

from collections import defaultdict, deque
from itertools import product

from homotopy_polygraph_guarded_boxes import Board
from homotopy_polygraph_routed_switch import route
from homotopy_polygraph_semaphore import histories


def transfer_path(shapes, after, start, start_role, end, end_role):
    out = (32 * start + {1: 4, 2: 16, 3: 24}[start_role], 0, 0)
    into = (32 * end + {1: 0, 2: 12, 3: 20}[end_role], 0, 0)
    todo = deque([(start,)])
    found = []
    while todo:
        path = todo.popleft()
        for node in after[path[-1]]:
            if len(path) == 1 and out not in shapes[node]:
                continue
            if isinstance(node, int):
                if node == end and into in shapes[path[-1]]:
                    found.append(path + (end,))
            else:
                todo.append(path + (node,))
    path, = found
    return path


def exposed(actor, site, role):
    x = site[0] - 32 * actor
    return {1: x <= 8, 2: 8 <= x <= 16, 3: True}[role]


def check_cycle(shapes, arrows, cycle):
    after = defaultdict(list)
    incoming_read = set()
    for a, b in arrows:
        after[a].append(b)
        site, = shapes[a] & shapes[b]
        incoming_read.add((b, site))
    paths = [transfer_path(shapes, after, *arc) for arc in cycle]
    kept = {node for path in paths for node in path}
    assert {(a, b) for a, b in arrows if a in kept and b in kept} == {
        edge for path in paths for edge in zip(path, path[1:])}
    actors = [edge[0] for edge in cycle]
    sites = set.union(*(set(shapes[node]) for node in kept))
    readers = defaultdict(list)
    for node, region in shapes.items():
        for site in region & sites:
            readers[site].append(node)

    # Colour a middle letter by the stages of its flanking rank-four anchors
    # and its clock bit. A passive read changes its own interior rank-three
    # token. An actor read can do this only on the intersection of its old roles.
    def rewrite(node, site, letter):
        v, time, d = letter
        if node == 'clock':
            assert time == 0
            return v, 1, d
        assert time == int((node, site) in incoming_read)
        if isinstance(node, int):
            if not (exposed(node, site, 1) and exposed(node, site, 2)):
                return letter
        if isinstance(node, tuple) and node[0] == 'link':
            assert d == 0
            return v, time, 1
        assert v == 0
        return 1, time, d

    cut_words = {}
    changed_reads = 0
    for site, pair in readers.items():
        word = ([n for n in pair if (n, site) not in incoming_read] + ['clock']
                + [n for n in pair if (n, site) in incoming_read])
        current = (0, 0, 0)
        transitions = {}
        for node in word:
            target = rewrite(node, site, current)
            transitions[node] = current, target
            current = target
        kept_here = [node for node in pair if node in kept]
        selected = [node for node in word if node in kept or node == 'clock' and len(kept_here) == 2]
        first, last = transitions[selected[0]][0], transitions[selected[-1]][1]
        changed_reads += sum(transitions[n][0] != transitions[n][1] for n in kept_here)
        # The retained vertex and connector anchors match the new poles at
        # the corresponding ends of the middle letter. The other end is free.
        for n in kept_here:
            side = 2 if isinstance(n, tuple) and n[0] == 'link' else 0
            assert first[side] == transitions[n][0][side]
            assert last[side] == transitions[n][1][side]
        cut_words[site] = selected, transitions, first, last

    legal = {}
    for assignment in product((1, 2, 3), repeat=len(actors)):
        roles = dict(zip(actors, assignment))
        edges = defaultdict(set)
        for site, (selected, transitions, letter, last) in cut_words.items():
            local = []
            for node in selected:
                if node in roles and not exposed(node, site, roles[node]):
                    assert transitions[node][0] == transitions[node][1]
                    continue
                start, target = transitions[node]
                assert start == letter
                letter = target
                if node != 'clock':
                    local.append(node)
            assert letter == last
            if len(local) == 2:
                edges[local[0]].add(local[1])
        indegree = dict.fromkeys(kept, 0)
        for targets in edges.values():
            for node in targets:
                indegree[node] += 1
        ready = [n for n in kept if indegree[n] == 0]
        count = 0
        while ready:
            n = ready.pop()
            count += 1
            for t in edges[n]:
                indegree[t] -= 1
                if indegree[t] == 0:
                    ready.append(t)
        assert (count == len(kept)) == (min(assignment) < 3)
        if count == len(kept):
            pos = tuple(int(role == 2) for role in assignment)
            moving = tuple(i for i, role in enumerate(assignment) if role == 3)
            legal[pos, moving] = True

    print(f'{len(actors)} actors, {len(kept)} boxes, {changed_reads} changing reads; '
          f'{len(legal)} legal role cubes.')
    k = len(actors)
    assert histories([('change',)] * k, legal) == (1,) + (0,) * (k - 3) + (1,)


if __name__ == '__main__':
    for board in (Board(1, 1, []), Board(3, 3, [(0, 0), (1, 1), (2, 2)])):
        _, shapes, arcs = route(board)
        a, b, s, z = board.rows[-1], board.cols[0], board.s, board.z
        check_cycle(shapes, arcs, [(a, 1, s, 2), (s, 1, z, 3), (z, 3, a, 2)])
        check_cycle(shapes, arcs, [(a, 1, s, 2), (s, 1, b, 2), (b, 1, z, 3), (z, 3, a, 2)])
