"""Test independent nonincidence relays against cube legality and Dowker complexes."""

from collections import Counter
from itertools import combinations, product

from homotopy_polygraph_guarded_boxes import Board, acyclic_chart, compile_boxes, link_type, subsets


def components_collapse(rows, cols, missing):
    faces = set()
    for b in range(cols):
        facet = sum(1 << a for a in range(rows) if not missing & (1 << (cols*a + b)))
        faces.update(subsets(facet))
    vertices = {f for f in faces if f.bit_count() == 1}
    while vertices:
        component = vertices.pop()
        while True:
            more = {v for v in vertices if any(f & v and f & component for f in faces)}
            if not more:
                break
            component |= sum(more)
            vertices -= more
        betti, collapsed = link_type(tuple(sorted(f for f in faces if f & component)))
        if not collapsed:
            assert any(betti[1:]), (rows, cols, missing, betti)
            return False
    return True


def criterion(rows, cols, missing):
    edges = [(a, b) for a in range(rows) for b in range(cols) if missing & (1 << (cols*a + b))]
    if len({a for a, b in edges}) != rows or len({b for a, b in edges}) != cols:
        return True
    return not any(len({a for a, b in triple}) == 3 and len({b for a, b in triple}) == 3
                   for triple in combinations(edges, 3))


def audit_relations(rows, cols):
    all_pass = {}
    counts = Counter()
    for missing in range(1 << (rows * cols)):
        top_pass = components_collapse(rows, cols, missing)
        immediate = (missing ^ (1 << i) for i in range(rows * cols) if missing & (1 << i))
        all_pass[missing] = top_pass and all(all_pass[k] for k in immediate)
        assert all_pass[missing] == criterion(rows, cols, missing)
        counts[top_pass, all_pass[missing]] += 1
    print(f'{rows} by {cols}: {len(all_pass)} boards, {counts[True, False]} with '
          'contractible components at full activation and a failing subrelation.')


def audit_relays():
    rows = cols = 2
    # All fixed controls use the box compiler. The optional site for (a,b)
    # is at their two band centres and has tags (2,0,4,4,4).
    fixed, _ = compile_boxes(Board(rows, cols, []))
    pairs = tuple(product(range(rows), range(cols)))
    board = Board(rows, cols, pairs)
    tested = 0
    for mask in range(1 << len(pairs)):
        selected = [edge for i, edge in enumerate(pairs) if mask & (1 << i)]
        effective = Board(rows, cols, selected)
        for roles in product(range(4), repeat=board.n):
            edges = [fixed[i, roles[i], j, roles[j]] for i, j in combinations(range(board.n), 2)
                     if roles[i] and roles[j]]
            for k, (a, b) in enumerate(selected, board.n):
                j = rows + b
                low, high = 2*a, 2*j
                assert low < low + 1 < high
                # At the two end sites a moving or final row reads 0, while
                # an initial or moving column reads 1. The relay reads 1,0.
                for actor, tag, height, before in [(a, 2, low, True), (j, 0, high, False)]:
                    local = {0: (), 1: range(2), 2: range(1, 3), 3: range(4)}[roles[actor]]
                    if tag in local and low <= height <= high:
                        edges.append([(actor, k) if before else (k, actor)])
            assert acyclic_chart(board.n + len(selected), edges) == effective.guard(roles)
            tested += 1
    print(f'{tested} spatial cube comparisons across all relay selections.')


if __name__ == '__main__':
    audit_relations(3, 3)
    audit_relations(4, 3)
    audit_relays()
