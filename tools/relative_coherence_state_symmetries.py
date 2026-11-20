"""Classify the twenty-cube state labels under signed isomorphism and test raw retyping."""
from argparse import ArgumentParser
from collections import Counter, defaultdict, deque
from itertools import product
from pathlib import Path

from catt import arr, chain_tree, check_ctx, comp2, disc_tree, infer, sub_from, subst_tm, subst_ty, tree_ctx, v
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_exchange_faces import head, reassociate
from relative_coherence_state_obstructions import (closure, hitting_number, inventory, mask, minimal,
                                                  priority_constraints, tableau)


def vertex(face):
    return mask(i for i, x in enumerate(face) if x == 1)


def distances(state, path):
    graph = defaultdict(set)
    for face in closure(state):
        if face.count(0) != 1:
            continue
        a = vertex(face)
        b = a | (1 << face.index(0))
        graph[a].add(b)
        graph[b].add(a)
    assert len(graph) == 42
    for p in path:
        found = {p: 0}
        pending = deque([p])
        while pending:
            a = pending.popleft()
            for b in graph[a] - found.keys():
                found[b] = found[a] + 1
                pending.append(b)
        assert found == {b: (p ^ b).bit_count() for b in graph}


def classify():
    states, carriers, _ = inventory()
    index = {s: i for i,s in enumerate(states)}
    lower = tableau((0,)*6)[:3]
    anchors = {vertex(face) for row in lower[1] for edge in row for face in closure([edge]) if 0 not in face}
    assert len(anchors) == 12
    actions = tuple(product((1,-1), repeat=2))
    def move(face, bit, axes):
        return tuple(bit*x for x in face[::axes])
    orbits = []
    for state in states:
        distances(state, anchors)
        row = tuple(sorted(state))
        whole = (*lower, (row, row))
        orbit = set()
        for bit, axes in actions:
            transformed = []
            for j, pair in enumerate(whole):
                swap = (bit < 0) ^ (axes < 0 and j % 2 == 1)
                ordered = pair[::-1] if swap else pair
                transformed.append(tuple(tuple(sorted(move(f, bit, axes) for f in side))
                                         for side in ordered))
            assert tuple(transformed[:3]) == lower
            orbit.add(index[frozenset(transformed[-1][0])])
        orbits.append(tuple(sorted(orbit)))
    classes = sorted(set(orbits))
    assert Counter(map(len, classes)) == {2: 10, 4: 32}
    positive = [mask(v for v in range(64) if (v >> i) & 1) for i in range(6)]
    _, choices = priority_constraints(carriers, positive)
    def project(m):
        return mask(i for i, group in enumerate(classes) if any(m >> j & 1 for j in group))
    projected = {project(m): seed for m, seed in choices.items()}
    constraints = sorted(minimal(projected), key=lambda c: (c.bit_count(), c))
    first = constraints[0]
    witness = hitting_number(constraints, len(classes))
    assert (len(projected), len(constraints), first.bit_count(), len(witness)) == (93, 16, 12, 2)
    assert all(mask(witness) & m for m in projected)
    assert all(any(not (m >> i & 1) for m in projected) for i in range(len(classes)))
    print('148 labels have 42 signed isomorphism classes: 10 pairs and 32 quadruples.')
    print('Seed and order', projected[first], 'require representatives',
          [c[0] for i,c in enumerate(classes) if first >> i & 1])
    print('93 projected colour selections, 16 minimal. Smallest hitting pair:', [classes[i] for i in witness])
    rows = tableau((0,)*4)
    for j, pair in enumerate(rows[:4]):
        assert tuple(sorted(move(f,-1,1) for f in pair[0])) == pair[1]
    for side in rows[3]:
        assert sum(0 not in f for f in closure(side)) == 15 and len(side) == 4
    print('The four-cube deletion has one signed class of three-faces on 15 vertices.')
    return classes, carriers, choices


def raw_retyping(output):
    base = tree_ctx(chain_tree(2))
    f = comp2(base, 0, v(2), v(4))
    a = ident(base, f)
    b = comp2(base, 1, a, a)
    old = base + (arr(infer(base, a), a, a),)
    new = base + (arr(infer(base, b), b, a),)
    check_ctx(old)
    check_ctx(new)
    z = v(len(base))
    e, d = head(base, a, b), head(base, b, a)
    base_map = tuple(map(v, range(len(base))))
    forward = base_map + (comp2(new, 2, e, z),)
    back = base_map + (comp2(old, 2, d, z),)
    for source, target, images in ((old, new, forward), (new, old, back)):
        for ty, term in zip(source, images, strict=True):
            assert infer(target, term) == subst_ty(ty, images)
    restored = subst_tm(forward[-1], back)
    cancel = comp2(base, 2, e, d)
    unit = ident(base, a)
    emitter = Emitter()
    def certify(tag, term, x, y):
        ty = arr(infer(old, x), x, y)
        assert infer(old, term) == ty
        if output:
            emitter.check_type(tag, old, term, ty)
    def unitor(n, cut, x, left, rev):
        disk = tree_ctx(disc_tree(n))
        w = v(len(disk)-1)
        pole = disk[-1][2 if left else 3]
        padded = comp2(disk, cut, ident(disk, pole), w) if left else comp2(disk, cut, w, ident(disk, pole))
        u, v_ = (w, padded) if rev else (padded, w)
        return subst_tm(head(disk, u, v_), sub_from(disk, old, {len(disk)-1: x}))
    h = None
    for rev in (False, True):
        alpha = reassociate(old, (e,d,z), not rev)
        beta = comp2(old, 2, head(base, unit, cancel) if rev else head(base, cancel, unit), z)
        gamma = unitor(3, 2, z, True, rev)
        x, y = (z, restored) if rev else (restored, z)
        route = (gamma, beta, alpha) if rev else (alpha, beta, gamma)
        correction = comp2(old, 3, comp2(old, 3, *route[:2]), route[2])
        certify('restoreBack' if rev else 'restore', correction, x, y)
        if not rev:
            h = correction
    left = comp2(old, 3, ident(old, restored), h)
    right = comp2(old, 3, h, ident(old, z))
    for rev in (False, True):
        step = comp2(old, 4, unitor(4, 3, h, not rev, False), unitor(4, 3, h, rev, True))
        certify('mateBack' if rev else 'mate', step, right if rev else left, left if rev else right)
    if output:
        output.write_text(emitter.module(output.stem, 'Retyping and identity transport at the original endpoints.'))
    print('Checked both substitutions, both generator corrections and both framed five-arrows.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    classify()
    raw_retyping(args.agda)
