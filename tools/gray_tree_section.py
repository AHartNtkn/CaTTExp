"""Assemble the diagonal section on two finite Batanin trees (node-pair recursion).

A tree is a tuple of its child trees. In its complex, (address, vertex)
is the generator at a vertex on the path of objects of that subtree.
"""
import argparse
from collections import Counter
from functools import cache
from itertools import product

from gray_globe_comparison import atom, close_atoms, face
from gray_globe_section import row_map, signature, trim
from gray_path_section import path_section


def nodes(tree, address=()):
    yield address, len(tree)
    for index, child in enumerate(tree):
        yield from nodes(child, address + (index,))


def generators(tree):
    return [(u, t) for u, length in nodes(tree) for t in range(length + 1)]


def tree_boundary(basis):
    result = Counter()
    sign = 1
    for axis, (address, _) in enumerate(basis):
        if address:
            for offset, coefficient in ((0, -1), (1, 1)):
                term = address[:-1], address[-1] + offset
                result[basis[:axis] + (term,) + basis[axis + 1:]] += sign * coefficient
        sign *= (-1) ** len(address)
    return result


def reflect(entry, length):
    degree, label = entry
    return degree, length - degree - label


def project(entry, node):
    """Take a branch slice and collapse its parallel arrows onto their segment."""
    address, vertex = entry
    if address[:len(node)] == node:
        tail = address[len(node):]
        if not tail:
            return 0, vertex
        if len(tail) == 1:
            return 1, tail[0]
    return None


def slice_edge(cell, axis, label):
    return row_map(cell, 1, lambda g: g[:axis] + g[axis + 1:] if g[axis] == (1, label) else None)


def margin(y, node, first):
    def basis(g):
        p, q = g if first else g[::-1]
        if not p[0] or len(q[0]) > 1:
            return None
        outside = project((p[0][1:], p[1]), node)
        if outside is None:
            return None
        mid = (1, 0) if q[0] else (0, 1 - q[1] if first else q[1])
        if first and len(node) % 2:
            mid = reflect(mid, 1)
        return (outside, mid) if first else (mid, outside)
    return row_map(y, 1 + len(node), basis)


def mixed_slice(y, u, w, width):
    def basis(g):
        (a, p), (b, q) = g
        if a and b:
            left, right = project((a[1:], p), u), project((b[1:], q), w)
            if left is not None and right is not None:
                return left, reflect(right, width) if len(u) % 2 else right
        return None
    return row_map(y, len(u) + len(w) + 2, basis)


@cache
def path_table(r, s):
    table = {((), (), ()): ()}
    for x in path_section(r, s).values():
        x = trim(x)
        key = signature(x)
        assert key not in table or table[key] == x
        table[key] = x
    return table


def section(p, q, y):
    outer_p, outer_q = dict(nodes(p)), dict(nodes(q))
    panels = [[[], []] for _ in y[1:]]
    boxes = {}
    for u, r in outer_p.items():
        for w, s in outer_q.items():
            rank = len(u) + len(w)
            if rank >= len(panels):
                continue
            flipped = len(u) % 2
            if w:
                index = outer_q[w[:-1]] - 1 - w[-1] if flipped else w[-1]
                pm = slice_edge(boxes[u, w[:-1]], 2, index)
            else:
                pm = margin(y, u, True)
            if u:
                mq = slice_edge(boxes[u[:-1], w], 0, u[-1])
                mq = row_map(mq, 0, lambda g: (reflect(g[0], 1), reflect(g[1], s)))
            else:
                mq = margin(y, w, False)
            data = pm, mq, mixed_slice(y, u, w, s)
            box = path_table(r, s)[data]
            boxes[u, w] = box
            if box:
                for d, chain in enumerate(box[0]):
                    (l, v, t), = chain
                    if flipped:
                        v, t = reflect(v, 1), reflect(t, s)
                    panels[rank][d].append(((u, l[1]), ((), v[1]), (w, t[1])))

    def assemble(chain, panel):
        middle = [((a[1:], l), ((0,), 0), (b[1:], r))
                  for (a, l), (b, r) in chain if a and b]
        return tuple(sorted(panel + middle))
    return tuple(tuple(assemble(chain, slots) for chain, slots in zip(row, panel))
                 for row, panel in zip(y[1:], panels))


def verify(p, q):
    source_atoms = {atom(b, tree_boundary, len) for b in product(generators(p), generators(((),)), generators(q))}
    target_atoms = {atom(b, tree_boundary, len) for b in product(generators((p,)), generators((q,)))}
    corners = tuple(((((), v), ((), v)),) for v in (0, 1))

    def project_back(x):
        def chain_image(chain):
            result = []
            for (a, l), (middle, v), (b, r) in chain:
                sp, sq = ((0,) + a, l), ((0,) + b, r)
                if middle:
                    result.append((sp, sq))
                else:
                    if not b:
                        result.append((sp, ((), 1 - v)))
                    if not a:
                        result.append((((), v), sq))
            return tuple(sorted(result))
        return (corners,) + tuple(tuple(chain_image(chain) for chain in row) for row in x)

    counts = []
    for k in range(max(map(len, source_atoms))):
        source = close_atoms(source_atoms, k)
        targets = {y for y in close_atoms(target_atoms, k + 1) if y[0] == corners}
        for y in targets:
            x = section(p, q, y)
            assert x in source and project_back(x) == y
            if k:
                assert all(face(x, d) == section(p, q, face(y, d)) for d in (0, 1))
        counts.append(len(targets))
    for a, b in product(generators(p), generators(q)):
        x = atom((a, ((0,), 0), b), tree_boundary, len)
        assert section(p, q, project_back(x)) == x
    return counts


if __name__ == '__main__':
    import json

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('p', type=json.loads, help='tree as a JSON array of child trees')
    parser.add_argument('q', type=json.loads, help='tree as a JSON array of child trees')
    args = parser.parse_args()
    print('Verified diagonal cells by hom degree:', *verify(args.p, args.q))
