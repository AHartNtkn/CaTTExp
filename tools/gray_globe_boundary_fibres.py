"""Recover the category between two signed globe-pair boundaries from its elementary moves."""
import argparse
from collections import Counter, defaultdict
from itertools import combinations, permutations, product
from pathlib import Path

from canonical_gray_two_discs import tableau_interpreter
from catt import STAR, arr, check_ctx, infer, v
from emit_agda import Emitter
from gray_globe_attachments import ordered_factors
from gray_globe_comparison import face
from gray_globe_corner_prisms import fold
from gray_globe_corner_pullback import small_schroeder
from gray_globe_factorizations import orders, profile, rank, truncate
from gray_globe_section import EMPTY_ROW, cells
from gray_globe_strip_squares import minimal_shape
from gray_path_wedge import compose


def coordinates(cell, m, n):
    """Coordinates of a degree-h object, indexed by first rank of a possible (h+1)-move."""
    h = len(cell) - 1
    row = {g[0][0]: g for g in cell[h][0]}
    bits = {i+1: g[0][1] for i, g in row.items() if i+1 in row}
    if 0 in row and h < n:
        bits[0] = row[0][1][1]
    if h in row and h < m:
        bits[h+1] = row[h][0][1]
    return bits


def trace_key(w):
    """An orientation for each adjacent pair of moves and a colour for a pure move."""
    d = len(w)-1
    row = {g[0][0]: g for g in w[-1][0]}
    # At the shared (d-1)-site the first tag on the lower-index move
    # determines which move comes first.
    order = tuple(row[i][0][1] for i in sorted(row) if i+1 in row)
    exterior = tuple(row[i][axis][1] for i, axis in ((0, 1), (d, 0)) if i in row)
    return order, exterior


def check_squares(vertices, labels, arrows, h):
    """Compose both paths around each coordinate square, including exterior colours."""
    checked = 0
    for bits, a in vertices.items():
        for i, j in combinations((k for k, bit in enumerate(bits) if not bit), 2):
            def advance(*positions):
                return vertices[tuple(int(k in positions or value) for k, value in enumerate(bits))]
            b = advance(i, j)
            def routes(mid):
                result = set()
                for first, last in product(arrows[a, mid], arrows[mid, b]):
                    result.add(compose(first, last, h))
                return result
            left, right = routes(advance(i)), routes(advance(j))
            assert left | right == arrows[a, b]
            if labels[j] == labels[i]+1:
                assert left.isdisjoint(right)
            else:
                assert left == right
            checked += 1
    return checked


def check_fibres(domain, m, n):
    levels = defaultdict(set)
    for cell in domain:
        levels[len(cell)-1].add(cell)
    count = Counter()
    for h in range(1, m+n):
        objects = defaultdict(set)
        for obj in levels[h]:
            objects[face(obj, 0), face(obj, 1)].add(obj)
        arrows = defaultdict(set)
        for w in levels[h+1]:
            a, b = face(w, 0), face(w, 1)
            arrows[a, b].add(w)
        for fibre in objects.values():
            bit_table = {obj: coordinates(obj, m, n) for obj in fibre}
            labels = tuple(sorted(next(iter(bit_table.values()))))
            assert all(tuple(sorted(bits)) == labels for bits in bit_table.values())
            vertices = {tuple(bits[i] for i in labels): obj for obj, bits in bit_table.items()}
            assert len(vertices) == len(fibre) == 2**len(labels)
            assert all(v in vertices for v in product((0, 1), repeat=len(labels)))
            for v, a in vertices.items():
                for u, b in vertices.items():
                    if v == u:
                        assert not arrows[a, b]  # the identity has lower intrinsic height
                        continue
                    moves = {i for i, x, y in zip(labels, v, u) if x != y}
                    if any(x > y for x, y in zip(v, u)):
                        assert not arrows[a, b]
                        continue
                    colours = [(0, 1) if dim > h+1 else (2,)
                               for i, dim in ((0, n), (h+1, m)) if i in moves]
                    keys = set(product(product((0, 1), repeat=sum(i+1 in moves for i in moves)),
                                       product(*colours)))
                    actual = arrows[a, b]
                    assert len(actual) == len(keys) and {trace_key(w) for w in actual} == keys
                    assert all({g[0][0] for g in w[-1][0]} == moves for w in actual)
                    if len(moves) == 1:
                        count['elementary arrows'] += len(actual)
                    count['arrows'] += len(actual)
            count['coordinate squares'] += check_squares(vertices, labels, arrows, h)
            count['fibres'] += 1
            count['objects'] += len(fibre)
        assert sum(len(v) for v in arrows.values()) == len(levels[h+1])
    print('Fixed-boundary categories:', dict(count))


def group_for(p):
    # The two central degree-five sites and their common successor form a single block.
    i, j = p
    if i >= 2 and j >= 2:
        return 1
    return 0 if i < 2 else 2


def split(w):
    ranks = profile(w)
    return ordered_factors(w, 4, {p: group_for(p) for p in ranks if sum(p) > 4})


def central(w):
    return len(w) >= 6 and {(2, 3), (3, 2)} <= set(map(rank, w[5][0]))


def chosen_blocks(w):
    exterior = {(1, 4), (4, 1)}
    if not central(w) or not exterior.intersection(map(rank, w[5][0])):
        return (w,)
    return split(w)


def check_paste(w, emitter):
    """Use parameters for the existing section's block terms, shared at their actual faces."""
    variables = {}
    context = ()

    def declare(c):
        nonlocal context
        if c not in variables:
            if len(c) == 1:
                ty = STAR
            else:
                s, t = (declare(face(c, side)) for side in (0, 1))
                ty = arr(infer(context, s), s, t)
            variables[c] = v(len(context))
            context += (ty,)
        return variables[c]

    args = [declare(c) for c in chosen_blocks(w)]
    check_ctx(context)
    term = fold(context, 4, args)
    ends = [fold(context, 4, [variables[c] for c in chosen_blocks(face(w, side))]) for side in (0, 1)]
    ty = arr(infer(context, ends[0]), *ends)
    assert infer(context, term) == ty
    values = tuple(variables)
    evaluate = tableau_interpreter(context, values.__getitem__)
    assert evaluate(term) == w and all(evaluate(t) == face(w, s) for s, t in enumerate(ends))
    if emitter:
        emitter.check_type('central-paste', context, term, ty)


def check_blocks(domain, emitter):
    counts = Counter()
    input_shapes = {}
    centres = set()
    shared_faces = set()
    for w in domain:
        if not central(w):
            continue
        ranks = profile(w)
        if ranks & {(2, 4), (4, 2)}:
            continue
        pieces = split(w)
        middle, = [c for c in pieces if central(c)]
        assert not {(1, 4), (4, 1)} & profile(middle)
        assert all((3, 3) not in profile(c) for c in pieces if c != middle)
        assert all(len(c) >= 6 for c in pieces)
        z = pieces[0]
        for c in pieces[1:]:
            height = max(len(z), len(c))
            z = compose(z + (EMPTY_ROW,)*(height-len(z)), c + (EMPTY_ROW,)*(height-len(c)), 4)
        assert z == w
        if len(w) > 6:
            for side in (0, 1):
                assert split(face(w, side)) == tuple(truncate(c, len(w)-2, side) for c in pieces)
        counts['with central generator' if (3, 3) in ranks else 'overlap'] += 1
        if len(w) == 7 and len(w[-1][0]) == 1 and (3, 3) in ranks:
            if minimal_shape(w) not in input_shapes:
                emit_here = emitter and len(chosen_blocks(w)) == 3 and pieces[1] == middle
                check_paste(w, emitter if emit_here else None)
                if emit_here:
                    emitter = None
            input_shapes[minimal_shape(w)] = minimal_shape(middle)
            centres.add(minimal_shape(middle))
            if (1, 4) in ranks or (4, 1) in ranks:
                shared_faces.update(minimal_shape(face(w, side)) for side in (0, 1))
    assert len(input_shapes) == 121 and len(centres) == 9 and len(shared_faces) == 192
    # Every disputed five-face is also incident to the native width-two section
    # in exactly the competing direction(s) predicted by the fixed-pole description.
    incident = defaultdict(set)
    for w in domain:
        if len(w) == 7 and len(w[-1][0]) == 1:
            p = rank(w[-1][0][0])
            for sign in (0, 1):
                incident[minimal_shape(face(w, sign))].add(p)
    rivals = Counter()
    conflicts = Counter()
    for z in shared_faces:
        sites = profile(z)
        expected = {p for p in ((2, 4), (4, 2))
                    if (p[0]-1, p[1]) in sites and (p[0], p[1]-1) in sites}
        assert expected and (3, 3) in incident[z]
        assert incident[z] & {(2, 4), (4, 2)} == expected
        rivals[len(expected)] += 1
        owner = {rank(g): rank(g)[0] for g in z[-1][0]}
        before = orders(z, 4, owner)
        pairs = [(i-1, i) for i, _ in expected | {(3, 3)}]
        forks = sum((i-1, i) in pairs and (i, i+1) in pairs and
                    ((i-1, i) in before) != ((i, i+1) in before) for i in (2, 3))
        legal = (w for w in permutations(owner.values()) if all(w.index(a) < w.index(b) for a, b in before))
        missed = min(sum(abs(w.index(a)-w.index(b)) != 1 for a, b in pairs) for w in legal)
        assert missed == int(bool(forks))
        conflicts[len(expected), forks] += 1
    print('Central block assembly:', dict(counts))
    print('121 shapes use', len(centres), 'central blocks; disputed five-faces by rival count:', dict(rivals))
    print('Contiguity conflicts by number of rivals and forks:', dict(sorted(conflicts.items())))


def sort_face_patches(w, face_word=None):
    """The two-step patches along the prescribed sorting of the faces of one singleton."""
    d = len(w)-1
    p = rank(w[-1][0][0])
    predecessors = {q for q in ((p[0]-1, p[1]), (p[0], p[1]-1)) if min(q) >= 0}
    cut = d-2
    owner = {q: -1 if q in predecessors or q == p else q[0]
             for q in profile(w) if sum(q) > cut}
    pieces = ordered_factors(w, cut, owner)
    core, = [c for c in pieces if len(c) == d+1]
    assert set(map(rank, core[-2][0])) == predecessors
    for side in (0, 1):
        z = face(w, side)
        parts = [part for c in pieces for part in ordered_factors(
            truncate(c, d-1, side), cut, {rank(g): rank(g)[0] for g in c[d-1][side]})]
        wanted = (face_word(z) if face_word else
                  ordered_factors(z, cut, {rank(g): rank(g)[0] for g in z[-1][0]}))
        priority = {c[-1][0][0]: i for i, c in enumerate(wanted)}
        for j in range(len(parts)):
            for i in range(len(parts)-1-j):
                a, b = parts[i:i+2]
                ga, gb = a[-1][0][0], b[-1][0][0]
                if priority[ga] < priority[gb]:
                    continue
                assert abs(rank(ga)[0]-rank(gb)[0]) >= 2
                patch = compose(a, b, cut)
                yield minimal_shape(patch)
                parts[i:i+2] = ordered_factors(patch, cut, {rank(ga): 1, rank(gb): 0})
        assert tuple(parts) == wanted


def check_local_words(domain, bound):
    """Sort the two actual faces of every elementary move, recording the exact exchange patches."""
    binary = defaultdict(set)
    short = defaultdict(set)
    used = set()
    central_patches = set()
    for w in domain:
        d = len(w)-1
        top = tuple(map(rank, w[-1][0]))
        if len(top) == 2 and top[1][0] - top[0][0] >= 2:
            binary[d, top[0][0], top[1][0]].add(minimal_shape(w))
        if d < 2 or len(top) != 1:
            continue
        (p,) = top
        predecessors = {site for site in ((p[0]-1, p[1]), (p[0], p[1]-1)) if min(site) >= 0}
        if set(map(rank, w[-2][0])) == predecessors:
            short[p].add(minimal_shape(w))
        patches = set(sort_face_patches(w))
        used.update(patches)
        if p == (3, 3):
            central_patches.update(patches)
    assert used <= set().union(*binary.values())
    def schroeder(h):
        return small_schroeder(h) if h >= 1 else 1
    # Restrict the count to degrees that fit entirely in the two given globes.
    for (d, i, j), shapes in binary.items():
        if d <= bound:
            assert len(shapes) == 2*schroeder(i)*schroeder(j-i-1)*schroeder(d-j)
    for (i, j), shapes in short.items():
        if max(i, j, i+j-2) <= bound:
            assert len(shapes) == schroeder(i-1)*schroeder(j-1)
    print('Distinct independent two-step exchanges used to order the (3,3) faces:', len(central_patches))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('m', type=int)
    parser.add_argument('n', type=int)
    parser.add_argument('--agda', type=Path, help='export a three-block assembly judgment (both dimensions >= 5)')
    args = parser.parse_args()
    if min(args.m, args.n) < 0:
        parser.error('globe dimensions must be nonnegative')
    if args.agda and min(args.m, args.n) < 5:
        parser.error('the three-block certificate requires both dimensions >= 5')
    domain = cells((args.m, args.n)) - {()}
    check_fibres(domain, args.m, args.n)
    check_local_words(domain, min(args.m, args.n))
    if min(args.m, args.n) >= 5:
        emitter = Emitter() if args.agda else None
        check_blocks(domain, emitter)
        if emitter:
            assert emitter.checks
            args.agda.write_text(emitter.module(args.agda.stem, 'Central assembly at its prescribed block faces.'))
