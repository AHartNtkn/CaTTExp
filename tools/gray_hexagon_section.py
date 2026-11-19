"""Verify the diagonal comparison for two suspended globes with an interval between."""
import argparse
from collections import Counter, defaultdict
from functools import cache
from itertools import product

from gray_globe_comparison import (atom, boundary, close_atoms, face, globe,
                                   image as two_factor_image, strict_cells)
from gray_globe_section import omit, reverse, reverse_axes, row_map, trim, window
from gray_polygon_suspension import Polygon, TOP


HEXAGON = Polygon((3, 3), False)
ROUTES = (('CBA', 'BCA', 'BAC', 'ABC'), ('CBA', 'CAB', 'ACB', 'ABC'))
CORNERS = tuple((((0, side),) * 3,) for side in (0, 1))


@cache
def trace(h):
    degree, (route, step) = h
    if degree == 2:
        return (((1, 2),) * 3,)
    if degree == 1:
        before, after = ROUTES[route][step:step + 2]
        swap = [i for i in range(3) if before[i] != after[i]]
        return (tuple((1, 2) if before.index(axis) in swap
                      else (0, int(before.index(axis) < swap[0])) for axis in 'ABC'),)
    word = ROUTES[route][step] if route < 2 else ROUTES[0][3 * step]
    return tuple(tuple((1, 2) if letter == axis else (0, int(word.index(axis) < i))
                       for axis in 'ABC') for i, letter in enumerate(word))


def differential(basis):
    p, h, q = basis
    result = Counter()
    for (g,), n in boundary((p,)).items():
        result[g, h, q] += n
    for g, n in HEXAGON.boundary[h].items():
        result[p, g, q] += (-1)**p[0] * n
    for (g,), n in boundary((q,)).items():
        result[p, h, g] += (-1)**(p[0] + h[0]) * n
    return result


@cache
def source_atoms(a, b):
    return {g: atom(g, differential) for g in product(globe(a), HEXAGON.boundary, globe(b))}


def image(x):
    def chain(row):
        result = []
        for p, h, q in row:
            for a, mid, c in trace(h):
                if (a[0] or not p[0]) and (c[0] or not q[0]):
                    result.append(((p[0]+1, p[1]) if a[0] else a, mid,
                                   (q[0]+1, q[1]) if c[0] else c))
        return tuple(sorted(result))
    return (CORNERS,) + tuple((chain(s), chain(t)) for s, t in x)


def reverse_hex(h):
    d, (b, i) = h
    if h == TOP:
        return h
    if b == 2:
        return d, (b, 1 - i)
    return d, (1 - b, 3 - d - i)


def crossing(x, axis):
    def project(g):
        for a, b, c in trace(g[axis]):
            if a[0] and c[0]:
                return g[:axis] + (b,) + g[axis+1:]
        return None
    return row_map(x, 1, project)


def signature(x):
    return omit(x, 2, 0), omit(x, 0, 0), crossing(x, 1)


def arrow_order(x):
    """Read the actual directed path, preferring P, then hexagon, then Q."""
    terms = list(x[1][0])
    vertex, = x[0][0]
    order = []
    while terms:
        for i, g in enumerate(terms):
            start, end = atom(g, differential)[0]
            if start == (vertex,):
                terms.pop(i)
                vertex, = end
                order.append(next(d for d, entry in enumerate(g) if entry[0]))
                break
        else:
            raise ValueError('disconnected path')
    return tuple(order)


def pinned(a, b, project):
    result = {}
    def include(x):
        key = project(x)
        if key in result:
            assert result[key] == x
            return
        result[key] = x
        if len(x) > 1:
            for s in (0, 1):
                include(face(x, s))
    atoms = source_atoms(a, b)
    for p, q in product(globe(a), globe(b)):
        include(atoms[p, TOP, q])
    return result


def select(candidates, size, project, pins):
    chosen = {}
    for key in sorted(candidates, key=size):
        def fits(x):
            return (len(x) == size(key) and (key not in pins or pins[key] == x)
                    and (len(x) <= 1 or all(chosen.get(project(z)) == z
                         for z in (trim(face(x, s)) for s in (0, 1)))))
        options = [x for x in candidates[key] if fits(x)]
        assert options, key
        chosen[key] = min(options, key=lambda x: (arrow_order(x) if len(x) == 2 else (), x))
    assert all(chosen[k] == x for k, x in pins.items())
    return chosen


def all_source(a, b):
    return {trim(x) for x in close_atoms(source_atoms(a, b).values(), a+b+2)} | {()}


@cache
def local_table(a, b):
    groups = defaultdict(list)
    for x in all_source(a, b):
        groups[signature(x)].append(x)
    us, vs, ws = defaultdict(list), defaultdict(list), defaultdict(list)
    for x in all_source(a, 0):
        u = omit(x, 2, 0)
        us[omit(u, 0, 0)].append(u)
    for x in all_source(0, b):
        v = omit(x, 0, 0)
        vs[omit(v, 1, 0)].append(v)
    values = {reverse_axes(trim(x), (1, 2)) for x in strict_cells((a, 1, b), a+b+1)} | {()}
    for w in values:
        ws[omit(w, 2, 0), omit(w, 0, 0)].append(w)
    allowed = {(u, v, w) for h in us for u in us[h] for v in vs[h]
               for w in ws[crossing(u, 1), crossing(v, 0)]}
    assert groups.keys() == allowed
    def size(key):
        u, v, w = key
        return max(len(u), len(v), len(w) + int(bool(w)))
    return select(groups, size, signature, pinned(a, b, signature))


def outer_signature(x, left):
    axis = 0 if left else 2
    h = omit(omit(x, 2, 0), 0, 0)
    def active(g):
        p, middle, q = g
        for y in trace(middle):
            if y[axis][0]:
                return (p,) + y[1:] if left else y[:2] + (q,)
        return None
    return h, row_map(x, 0, active)


@cache
def outer_table(d, left):
    a, b = (d, 0) if left else (0, d)
    project = lambda x: outer_signature(x, left)
    options = defaultdict(list)
    for x in all_source(a, b):
        options[project(x)].append(x)
    hs = {omit(omit(x, 2, 0), 0, 0): project(x)[1] for x in all_source(0, 0)}
    # project(x)[1] includes a point factor on the variable side here.
    axis = 0 if left else 2
    shape = (d, 1, 1) if left else (1, 1, d)
    rs = {trim(x) for x in strict_cells(shape, sum(shape))} | {()}
    if left:
        rs = {reverse_axes(r, (1, 2)) for r in rs}
    by_margin = defaultdict(list)
    for r in rs:
        by_margin[omit(r, axis, 0)].append(r)
    allowed = {(h, r) for h, fixed in hs.items() for r in by_margin[omit(fixed, axis, 0)]}
    assert options.keys() == allowed
    return select(options, lambda key: max(map(len, key)), project, pinned(a, b, project))


@cache
def unlabelled():
    return {trim(image(x)): omit(omit(x, 2, 0), 0, 0) for x in all_source(0, 0) if x}


def collapse(y, axis):
    def basis(g):
        d, _ = g[axis]
        if d == 0:
            return g
        if d == 1:
            return g[:axis] + ((1, 2),) + g[axis+1:]
        return None
    return row_map(y, 0, basis)


@cache
def one_sided(dim, left, y):
    axis = 0 if left else 2
    # y already has the opposite outer label collapsed to an interval.
    margin = unlabelled()[collapse(y, axis)]
    rows = [[[], []] for _ in y[1:]]
    for i in range(min(dim, len(rows)-1)+1):
        def slot(g):
            label = g[axis]
            if label[0] not in (i+1, i+2):
                return None
            projected = window((label[0]-1, label[1]), i)
            if left:
                fixed = tuple(reverse(v) for v in g[1:]) if i % 2 else g[1:]
                return (projected,) + fixed
            return g[:2] + (projected,)
        r = row_map(y, i+1, slot)
        box = outer_table(int(i < dim), left)[margin, r]
        for j, pair in enumerate(box):
            for side, chain in enumerate(pair):
                for p, h, q in chain:
                    f = p if left else q
                    if f[0] == 0:
                        v = i, f[1]
                        entry = (v, reverse_hex(h) if i % 2 else h) if left else (h, v)
                        rows[i+j][side].append(entry)
        margin = omit(omit(box, 2, 0), 0, 1) if left else omit(omit(box, 0, 0), 1, 1)
        if left:
            margin = row_map(margin, 0, lambda g: (reverse_hex(g[0]),))
    return trim(tuple(tuple(tuple(sorted(c)) for c in pair) for pair in rows))


def lift(a, b, y):
    left = one_sided(a, True, collapse(y, 2))
    right = one_sided(b, False, collapse(y, 0))
    rows = [[[], []] for _ in y[1:]]
    boxes = {}
    for i in range(min(a, len(rows)-1)+1):
        for j in range(min(b, len(rows)-1-i)+1):
            if j:
                u = omit(boxes[i, j-1], 2, 1)
            else:
                def p_window(g):
                    p, h = g
                    if p[0] in (i, i+1):
                        return window(p, i), reverse_hex(h) if i % 2 else h
                u = row_map(left, i, p_window)
            if i:
                v = row_map(omit(boxes[i-1, j], 0, 1), 0,
                            lambda g: (reverse_hex(g[0]), reverse(g[1])))
            else:
                def q_window(g):
                    h, q = g
                    if q[0] in (j, j+1):
                        return h, window(q, j)
                v = row_map(right, j, q_window)

            def both(g):
                p, mid, q = g
                if p[0] in (i+1, i+2) and q[0] in (j+1, j+2):
                    l, r = window((p[0]-1, p[1]), i), window((q[0]-1, q[1]), j)
                    return (l, reverse(mid), reverse(r)) if i % 2 else (l, mid, r)
            w = row_map(y, i+j+2, both)
            box = local_table(int(i<a), int(j<b))[u, v, w]
            boxes[i, j] = box
            for d, pair in enumerate(box):
                for side, chain in enumerate(pair):
                    for p, h, q in chain:
                        if p[0] or q[0]:
                            continue
                        if i % 2:
                            h, q = reverse_hex(h), reverse(q)
                        rows[i+j+d][side].append(((i, p[1]), h, (j, q[1])))
    return tuple(tuple(tuple(sorted(chain)) for chain in pair) for pair in rows)


def check_panels():
    """Check the small source's top cells and the six maps on their entire cubes."""
    atoms = source_atoms(1, 1)
    top = atoms[(1, 2), TOP, (1, 2)]
    cells = close_atoms(atoms.values(), 4)
    assert {x for x in cells if x[-1][0]} == {top}
    cube = strict_cells((1, 1, 1), 3)
    for h in HEXAGON.boundary:
        if h[0] != 1:
            continue
        endpoints = HEXAGON.boundary[h]
        vertices = sorted(endpoints, key=endpoints.get)
        square, = trace(h)
        stationary, = (i for i in range(3) if square[i][0] == 0)
        side = square[stationary][1]
        for x in cube:
            def embed(chain):
                return tuple(sorted((p, h if mid[0] else vertices[mid[1]], q)
                                    for p, mid, q in chain))
            panel_image = image(tuple((embed(s), embed(t)) for s, t in x))
            if stationary == 1:
                # Whisker the two-factor diagonal by B on its actual side.
                ordinary = two_factor_image(x)
                rows = [CORNERS]
                for degree, pair in enumerate(ordinary[1:], 1):
                    row = []
                    for chain in pair:
                        entries = [(a, (0, side), c) for a, c in chain]
                        if degree == 1:
                            entries.append(((0, 1-side), (1, 2), (0, 1-side)))
                        row.append(tuple(sorted(entries)))
                    rows.append(tuple(row))
                assert tuple(rows) == panel_image
            else:
                # The two-coordinate tile lies at a fixed spectator endpoint.
                # The spectator globe meets it only at the common wedge vertex.
                for pair in panel_image:
                    for chain in pair:
                        for g in chain:
                            others = [v for i, v in enumerate(g) if i != stationary]
                            assert (g[stationary] == (0, side) or
                                    all(v == (0, 1-side) for v in others))
    print(f'Small source: {len(cells)} four-cells, one nonidentity; all six panels verified')


def verify(a, b):
    source = source_atoms(a, b)
    target = {g: atom(g) for g in product(globe(a+1), globe(1), globe(b+1))}
    previous = {}
    for k in range(a+b+4):
        candidates = close_atoms(source.values(), k)
        checked = {}
        for y in close_atoms(target.values(), k+1):
            if y[0] != CORNERS:
                continue
            x = lift(a, b, y)
            assert x in candidates and image(x) == y
            if k:
                assert all(face(x, s) == previous[face(y, s)] for s in (0, 1))
                assert y[-1] != ((), ()) or x[-1] == ((), ())
            checked[y] = x
        print(f'Hom degree {k}: verified {len(checked)} lifts', flush=True)
        previous = checked
    verify_pins(a, b)


def verify_pins(a, b):
    source = source_atoms(a, b)
    pins = pinned(a, b, image)
    for p, q in product(globe(a), globe(b)):
        x = source[p, TOP, q]
        y = atom(((p[0]+1, p[1]), (1, 2), (q[0]+1, q[1])))
        assert image(x) == y
    for y, x in pins.items():
        assert lift(a, b, y) == x
    print(f'Verified {len(pins)} distinct mixed atoms and signed faces')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('a', type=int)
    parser.add_argument('b', type=int)
    parser.add_argument('--pins-only', action='store_true',
                        help='check all mixed atoms and their faces without cell enumeration')
    args = parser.parse_args()
    if min(args.a, args.b) < 0:
        parser.error('globe dimensions must be nonnegative')
    for p, q in product(range(2), repeat=2):
        print(f'Local dimensions ({p}, {q}): {len(local_table(p,q))} compatible triples')
    check_panels()
    if args.pins_only:
        verify_pins(args.a, args.b)
    else:
        verify(args.a, args.b)
