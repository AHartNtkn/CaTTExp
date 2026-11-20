"""Construct the extreme-hom section for two suspended trees separated by an interval."""
import argparse
import json
from collections import Counter
from functools import cache
from itertools import product

from gray_globe_comparison import atom, close_atoms, face, globe
from gray_globe_section import omit, reverse, row_map, trim
from gray_hexagon_section import HEXAGON, TOP, reverse_hex, trace, unlabelled
from gray_hexagon_tree_windows import select_outer, select_window
from gray_tree_section import generators, nodes, project, reflect, slice_edge


CORNERS = tuple(((((), v), (0, v), ((), v)),) for v in (0, 1))


def suspended(entry):
    address, label = entry
    return (0,) + address, label


def window(entry, node):
    address, label = entry
    return project((address[1:], label), node) if address else None


def collapse_tree(y, axis):
    def basis(g):
        address, vertex = g[axis]
        if len(address) > 1:
            return None
        fixed = (1, 2) if address else (0, vertex)
        return g[:axis] + (fixed,) + g[axis+1:]
    return row_map(y, 0, basis)


def tableau(rows):
    return tuple(tuple(tuple(sorted(chain)) for chain in pair) for pair in rows)


def outer_section(tree, left, y):
    axis = 0 if left else 2
    margins = {(): unlabelled()[collapse_tree(y, axis)]}
    rows = [[[], []] for _ in y[1:]]
    for node, length in nodes(tree):
        depth = len(node)
        if depth >= len(rows):
            continue

        def slot(g):
            entry = window(g[axis], node)
            if entry is None:
                return None
            if left and depth % 2:
                return entry, reverse(g[1]), reverse(g[2])
            return (entry,) + g[1:] if left else g[:2] + (entry,)

        box = select_outer(length, left, margins[node], row_map(y, depth+1, slot))
        for d, pair in enumerate(box):
            for side, chain in enumerate(pair):
                for p, h, q in chain:
                    rank, label = p if left else q
                    if rank == 0:
                        entry = node, label
                        middle = reverse_hex(h) if left and depth % 2 else h
                        rows[depth+d][side].append((entry, middle) if left else (middle, entry))
        no_point = omit(box, 2 if left else 0, 0)
        for child in range(length):
            margin = slice_edge(no_point, 0 if left else 1, child)
            if left:
                margin = row_map(margin, 0, lambda g: (reverse_hex(g[0]),))
            margins[node + (child,)] = margin
    return trim(tableau(rows))


def section(p, q, y):
    left = outer_section(p, True, collapse_tree(y, 2))
    right = outer_section(q, False, collapse_tree(y, 0))
    rows = [[[], []] for _ in y[1:]]
    boxes = {}
    widths = dict(nodes(q))
    for a, r in nodes(p):
        odd = len(a) % 2
        for b, s in widths.items():
            depth = len(a) + len(b)
            if depth >= len(rows):
                continue
            if b:
                index = widths[b[:-1]]-1-b[-1] if odd else b[-1]
                u = slice_edge(boxes[a, b[:-1]], 2, index)
            else:
                def left_slot(g):
                    entry = project(g[0], a)
                    if entry is not None:
                        return entry, reverse_hex(g[1]) if odd else g[1]
                u = row_map(left, len(a), left_slot)
            if a:
                parent = slice_edge(boxes[a[:-1], b], 0, a[-1])
                v = row_map(parent, 0, lambda g: (reverse_hex(g[0]), reflect(g[1], s)))
            else:
                def right_slot(g):
                    entry = project(g[1], b)
                    if entry is not None:
                        return g[0], entry
                v = row_map(right, len(b), right_slot)

            def mixed_slot(g):
                l, k = window(g[0], a), window(g[2], b)
                if l is not None and k is not None:
                    return (l, reverse(g[1]), reflect(k, s)) if odd else (l, g[1], k)
            w = row_map(y, depth+2, mixed_slot)
            box = boxes[a, b] = select_window(r, s, u, v, w)
            for d, pair in enumerate(box):
                for side, chain in enumerate(pair):
                    for l, h, k in chain:
                        if l[0] == k[0] == 0:
                            if odd:
                                h, k = reverse_hex(h), reflect(k, s)
                            rows[depth+d][side].append(((a, l[1]), h, (b, k[1])))
    return tableau(rows)


def image(x):
    def chain_image(chain):
        result = []
        for p, h, q in chain:
            for l, m, r in trace(h):
                if (l[0] or not p[0]) and (r[0] or not q[0]):
                    result.append((suspended(p) if l[0] else ((), l[1]), m,
                                   suspended(q) if r[0] else ((), r[1])))
        return tuple(sorted(result))
    return (CORNERS,) + tuple(tuple(chain_image(chain) for chain in pair) for pair in x)


def dimension(rank):
    return rank if isinstance(rank, int) else len(rank)


def differential(g, target):
    result = Counter()
    sign = 1
    for axis, (rank, label) in enumerate(g):
        if axis != 1 and rank:
            terms = [((rank[:-1], rank[-1]+side), 2*side-1) for side in (0, 1)]
        elif axis == 1 and not target:
            terms = HEXAGON.boundary[g[axis]].items()
        elif axis == 1 and rank:
            terms = [((0, side), 2*side-1) for side in (0, 1)]
        else:
            terms = []
        for entry, coefficient in terms:
            result[g[:axis] + (entry,) + g[axis+1:]] += sign*coefficient
        sign *= (-1)**dimension(rank)
    return result


def source_diff(g):
    return differential(g, False)


def target_diff(g):
    return differential(g, True)


def verify(p, q, through):
    source = {atom(g, source_diff, dimension)
              for g in product(generators(p), HEXAGON.boundary, generators(q))}
    target = {atom(g, target_diff, dimension)
              for g in product(generators((p,)), globe(1), generators((q,)))}

    @cache
    def check_pin(x):
        assert section(p, q, image(x)) == x
        if len(x) > 1:
            for side in (0, 1):
                check_pin(face(x, side))

    for a, b in product(generators(p), generators(q)):
        x = atom((a, TOP, b), source_diff, dimension)
        assert image(x) == atom((suspended(a), (1, 2), suspended(b)), target_diff, dimension)
        check_pin(x)
    print(f'Checked {check_pin.cache_info().currsize} mixed atoms and signed faces', flush=True)
    previous = {}
    highest = max(map(len, source))-1
    for k in range(1 + (highest if through is None else min(highest, through))):
        candidates = close_atoms(source, k)
        current = {}
        for y in close_atoms(target, k+1):
            if y[0] == CORNERS:
                x = section(p, q, y)
                assert x in candidates and image(x) == y
                if k:
                    assert all(face(x, side) == previous[face(y, side)] for side in (0, 1))
                    assert y[-1] != ((), ()) or x[-1] == ((), ())
                current[y] = x
        previous = current
        print(f'Hom degree {k}: verified {len(current)} lifts', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('p', type=json.loads, help='tree as an array of child trees')
    parser.add_argument('q', type=json.loads, help='tree as an array of child trees')
    parser.add_argument('--through', type=int, help='last hom degree to enumerate (-1 for atom pins only)')
    args = parser.parse_args()
    verify(args.p, args.q, args.through)
