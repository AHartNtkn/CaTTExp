"""Compile signed bridge contexts with shared tails and evaluate their globular rows."""

from dataclasses import dataclass
from itertools import product

from interchange_cylinders import atom, compose, face
from interchange_double_variation import between


@dataclass(frozen=True)
class Attachment:
    inner: int
    rank: int
    side: int
    prefix: bool


def bridge_contexts(p, q, right):
    """Each attachment names an earlier bridge. Both layers start with the empty context."""
    nodes = []
    rows = []
    roots = [-1, -1]
    for offset in range(q + 1):
        rank = p + offset
        reverse = right and offset % 2 == 1
        rows.append((rank, reverse, tuple(roots)))
        if offset < q:
            for layer in range(2):
                prefix = layer != int(reverse)
                nodes.append(Attachment(roots[layer], rank, int(not prefix), prefix))
                roots[layer] = len(nodes) - 1
    return rows, nodes


def hemisphere(disk, rank, side):
    while len(disk) > rank + 1:
        disk = face(disk, side)
    return disk


def verify_rows(p, q, right, check_bridge=None):
    rows, nodes = bridge_contexts(p, q, right)

    def basis(variable, fixed):
        return (fixed, variable) if right else (variable, fixed)

    layers = [atom(basis((p, side), (q, 2))) for side in range(2)]
    direct = atom(basis((p + 1, 2), (q, 2)))
    bridges = {}

    def apply(root, cell):
        path = []
        while root != -1:
            op = nodes[root]
            path.append(op)
            root = op.inner
        for op in reversed(path):
            bridge = bridges[op.rank, op.side]
            cell = compose(bridge, cell, op.rank) if op.prefix else compose(cell, bridge, op.rank)
        return cell

    for rank, reverse, roots in rows:
        offset = rank - p
        for side in range(2):
            ends = [apply(roots[i], hemisphere(layer, rank, side)) for i, layer in enumerate(layers)]
            if reverse:
                ends.reverse()
            fixed_side = side if right else side ^ (p % 2)
            fixed = (offset, 2 if offset == q else fixed_side)
            bridges[rank, side] = between(*ends, basis((p + 1, 2), fixed))
            assert ends[side] == hemisphere(direct, rank, side)
            if check_bridge is not None:
                check_bridge(rank, bridges[rank, side])
    assert bridges[p + q, 0] == bridges[p + q, 1] == direct
    return 2 * len(rows)


if __name__ == '__main__':
    count = sum(verify_rows(p, q, right)
                for p, q, right in product(range(3, 7), range(2, 10), (False, True)))
    for right in (False, True):
        rows, nodes = bridge_contexts(5, 4096, right)
        assert len(rows) == 4097 and len(nodes) == 8192
        for depth, (_, _, roots) in enumerate(rows):
            for layer, root in enumerate(roots):
                assert root == (2 * (depth - 1) + layer if depth else -1)
                if depth:
                    assert nodes[root].inner == rows[depth - 1][2][layer]
    print(f'{count} signed row endpoints matched the tensor differential. '
          'Each orientation of the 4096-stage recipe used 8192 shared attachments.')
