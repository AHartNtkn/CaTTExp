"""Check relational certificates for cut and target exclusion on raw occurrence diagrams."""
from argparse import ArgumentParser
from collections import defaultdict
from functools import lru_cache
from itertools import combinations
from pathlib import Path

from catt import STAR, arr, comp2, infer, src, subst_tm, tdim, tgt, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite
from relative_coherence_hidden_seam import identity
from semistrict_surface_occurrence_attachments import cuts, pushout, three_edges
from semistrict_surface_occurrence_computads import maps_over, unfold


def read_map(source, target_ctx, target_term):
    """Read the unique map of the representing diagram at a literal lift."""
    shape, universal, _ = source
    images = [None] * len(shape)

    def terms(a, b):
        assert a[0] == b[0]
        if a[0] == 'v':
            i = a[1]
            if images[i] is None:
                images[i] = b
                types(shape[i], target_ctx[b[1]])
            else:
                assert images[i] == b
        else:
            assert a[1:3] == b[1:3]
            for x, y in zip(a[3], b[3], strict=True):
                terms(x, y)

    def types(a, b):
        assert a[0] == b[0]
        if a != STAR:
            types(a[1], b[1])
            terms(a[2], b[2])
            terms(a[3], b[3])

    terms(universal, target_term)
    assert None not in images
    return tuple(images)


class Signature:
    def __init__(self, base):
        self.base = base
        self.diagram = lru_cache(None)(lambda term: unfold(base, term))

    def atoms(self, shape, fold):
        atoms = []
        for i, label in enumerate(fold):
            coords = read_map(self.diagram(label), shape, v(i))
            atoms.append((label, tuple(x[1] for x in coords)))
        return atoms

    def boundary(self, source, target):
        """Pairs of generators identified at the two written common faces."""
        s_ctx, s, s_fold = source
        t_ctx, t, t_fold = target
        pairs = set()
        for face in (src, tgt):
            lower = self.diagram(subst_tm(face(s_ctx, s), s_fold))
            a = read_map(lower, s_ctx, face(s_ctx, s))
            assert subst_tm(face(t_ctx, t), t_fold) == subst_tm(lower[1], lower[2])
            b = read_map(lower, t_ctx, face(t_ctx, t))
            pairs.update((x[1], y[1]) for x, y in zip(a, b, strict=True))
        return sorted(pairs)

    def pieces(self, source, target):
        """Return each target conjunct's frontier after factoring independent existentials."""
        anchors = defaultdict(list)
        for i, j in self.boundary(source, target):
            anchors[j].append(i)
        equalities = [{min(old), i} for old in anchors.values() for i in old if i != min(old)]
        pieces = []
        for _, coords in self.atoms(target[0], target[2]):
            free = {min(anchors[i]) for i in coords if i in anchors}
            existential = {i for i in coords if i not in anchors}
            remaining = []
            for old_free, old_existential in pieces:
                if old_existential & existential:
                    existential |= old_existential
                    free |= old_free
                else:
                    remaining.append((old_free, old_existential))
            pieces = remaining + [(free, existential)]
        return equalities + [frontier for frontier, _ in pieces]

    def guarded(self, source, target):
        guards = [set(coords) for _, coords in self.atoms(source[0], source[2])]
        return all(any({i, j} <= guard for guard in guards)
                   for piece in self.pieces(source, target) for i, j in combinations(piece, 2))


def assignments(atoms, tables, size):
    """Evaluate a conjunction of relation atoms, including repeated coordinates."""
    partials = {tuple([None] * size)}
    for label, coords in atoms:
        next_rows = set()
        for row in partials:
            for fact in tables[label]:
                result = list(row)
                for i, token in zip(coords, fact, strict=True):
                    if result[i] is not None and result[i] != token:
                        break
                    result[i] = token
                else:
                    next_rows.add(tuple(result))
        partials = next_rows
    return partials


def lifted_rows(sig, diagram, ctx, fold, tables):
    atoms = sig.atoms(diagram[0], diagram[2])
    rows = assignments(atoms, tables, len(diagram[0]))
    literal = {tuple(x[1] for x in m) for m in maps_over(diagram[0], diagram[2], ctx, fold)}
    assert rows == literal
    return rows


def object_poles(ctx, term):
    result = []
    for face in (src, tgt):
        obj = term
        while infer(ctx, obj) != STAR:
            obj = face(ctx, obj)
        result.append(obj[1])
    return tuple(result)


def changing_rule():
    ctx, left, right = three_edges()
    f = v(1)
    ff = comp2(ctx, 0, f, f)
    grow, shrink = v(len(ctx)), v(len(ctx) + 1)
    ctx += (arr(infer(ctx, f), f, ff), arr(infer(ctx, f), ff, f))
    middle = comp2(ctx, 0, comp2(ctx, 0, f, comp2(ctx, 1, grow, shrink)), f)
    empty = src(ctx, left)
    birth, death = v(len(ctx)), v(len(ctx) + 1)
    ctx += (arr(infer(ctx, empty), empty, middle), arr(infer(ctx, empty), middle, empty))
    bubble = comp2(ctx, 2, birth, death)
    full = comp2(ctx, 2, right, bubble)
    p, q = v(len(ctx)), v(len(ctx) + 1)
    ctx += (arr(infer(ctx, left), left, full), arr(infer(ctx, left), full, left))
    return ctx, left, full, p, q


def test_growth(emitter):
    ctx, left, full, p, q = changing_rule()
    sig = Signature(ctx)
    source, target, pd, qd = map(sig.diagram, (left, full, p, q))
    assert sig.guarded(source, target) and sig.guarded(target, source)
    # Use the lower skeleton of p as a certificate for both rules.
    shape = tuple(ty for ty in pd[0] if tdim(ty) < 3)
    assert shape == pd[0][:-1]
    fold = pd[2][:-1]
    facts = defaultdict(set)
    for label, row in sig.atoms(shape, fold):
        facts[label].add(row)
    actual_cuts = cuts(shape)
    assert len(actual_cuts) == 2  # The temporary midpoint may lie on either side.
    for a, b in ((source, target), (target, source)):
        a_rows = lifted_rows(sig, a, shape, fold, facts)
        b_rows = lifted_rows(sig, b, shape, fold, facts)
        boundary = sig.boundary(a, b)
        assert len(a_rows) == len(b_rows) == 1
        assert all(any(all(u[i] == w[j] for i, j in boundary) for w in b_rows) for u in a_rows)
        poles = object_poles(a[0], a[1])
        for row in a_rows:
            for colours in actual_cuts:
                assert tuple(colours[row[i]] for i in poles) == (0, 1)
    rules = []
    for diagram, a, b in ((pd, source, target), (qd, target, source)):
        ty = infer(diagram[0], diagram[1])
        rules.append((diagram, read_map(a, diagram[0], ty[2]), read_map(b, diagram[0], ty[3])))
    original = comp2(ctx, 3, p, q)
    emitter.check_type('roundTrip', ctx, original, arr(infer(ctx, left), left, left))
    shape, value, fold = source
    entrance = tuple(map(v, range(len(shape))))
    counts = []
    for k in range(12):
        (r_ctx, r, r_fold), a, b = rules[k % 2]
        shape, fold, prev, new = pushout(shape, fold, r_ctx, r_fold, entrance, a)
        value = subst_tm(value, prev)
        entrance = tuple(new[x[1]] for x in b)
        counts.append(sum(ty == STAR for ty in shape))
        step = subst_tm(r, new)
        history = step if k == 0 else comp2(shape, 3, subst_tm(history, prev), step)
        if k == 1:
            direct = sig.diagram(original)
            iso = read_map(direct, shape, history)
            assert len(direct[0]) == len(shape) == len(set(iso))
            emitter.check_eq('roundTripFold', history, fold, original)
    assert counts == [5 + i // 2 for i in range(12)]
    # The chosen common cut exists in both whole declaration diagrams.
    assert cuts(pd[0]) and cuts(qd[0])
    print('The cut certificate covers both guards. Six round trips grow from 4 to 10 vertices.')


def test_alias():
    base = (STAR, arr(STAR, v(0), v(0)))
    f = v(1)
    unit = identity(base, v(0))
    collapse = v(len(base))
    base += (arr(infer(base, f), f, unit),)
    return_edge = v(len(base))
    base += (arr(infer(base, f), unit, f),)
    a = identity(base, f)
    b = comp2(base, 1, collapse, return_edge)
    sig = Signature(base)
    source, target = map(sig.diagram, (a, b))
    aliases = defaultdict(set)
    for i, j in sig.boundary(source, target):
        aliases[j].add(i)
    assert any(len(xs) == 2 for xs in aliases.values())
    assert sig.guarded(source, target)
    # A single nonloop edge lifts the source but cannot lift the matched target.
    shape, _, fold = source
    tables = defaultdict(set)
    for label, row in sig.atoms(shape, fold):
        tables[label].add(row)
    rows = lifted_rows(sig, source, shape, fold, tables)
    assert len(rows) == 1
    assert all(any(len({row[i] for i in xs}) > 1 for xs in aliases.values()) for row in rows)
    print('A glued boundary with coincident endpoints retains the required two-coordinate equality.')


def test_exclusion():
    base = (STAR,)
    wire = identity(base, v(0))
    a = v(len(base))
    base += (arr(infer(base, wire), wire, wire),)
    z, w = v(len(base)), v(len(base) + 1)
    base += (arr(infer(base, a), a, a),) * 2
    sig = Signature(base)
    source, target = map(sig.diagram, (z, w))
    shape, _, fold = source
    tables = defaultdict(set)
    for label, row in sig.atoms(shape, fold):
        tables[label].add(row)
    assert not cuts(shape)
    assert not lifted_rows(sig, target, shape, fold, tables)
    assert lifted_rows(sig, source, shape, fold, tables)
    print('The scalar seed has no cut, excludes the parallel w, and already realizes z.')


def word_rules(emitter):
    rules = [('S', 'aSb'), ('S', 'T'), ('aTb', 'T'), ('aTr', 'Hk'), ('lTb', 'Hk')]
    alphabet = sorted(set(''.join(u + w for u, w in rules)))
    letters = {c: v(i + 1) for i, c in enumerate(alphabet)}
    ctx = (STAR,) + (arr(STAR, v(0), v(0)),) * len(letters)

    def word(w):
        return composite(ctx, 0, [letters[c] for c in w])

    def arrow(s, t):
        nonlocal ctx
        i = v(len(ctx))
        assert infer(ctx, s) == infer(ctx, t)
        ctx += (arr(infer(ctx, s), s, t),)
        return i

    def attach(path, gate):
        unit = identity(ctx, path)
        birth, death = arrow(unit, gate), arrow(gate, unit)
        bubble = comp2(ctx, 2, birth, death)
        idle = identity(ctx, unit)
        return arrow(idle, bubble), arrow(bubble, idle)

    def graph(shape, fold):
        return [(src(shape, v(i))[1], tgt(shape, v(i))[1], alphabet[fold[i][1] - 1])
                for i, ty in enumerate(shape) if tdim(ty) == 0]

    def paths(graph_edges, start, finish):
        if start == finish:
            return {''}
        return {c + suffix for x, y, c in graph_edges if x == start
                for suffix in paths(graph_edges, y, finish)}

    templates = []
    for u, w in rules:
        path, alternate = word(u), word(w)
        out, back_gate = arrow(path, alternate), arrow(alternate, path)
        gate = comp2(ctx, 1, out, back_gate)
        g, back = attach(path, gate)
        diagram = unfold(ctx, g)
        seed = unfold(ctx, src(ctx, g))
        entry = read_map(seed, diagram[0], src(diagram[0], diagram[1]))
        vertices = object_poles(seed[0], seed[1])
        old = [entry[i][1] for i in vertices]
        drawn = graph(diagram[0], diagram[2])
        assert paths(drawn, old[0], old[-1]) == {u, w}, (u, w, drawn, old)
        assert len(drawn) == len(u) + len(w)
        assert sum(ty == STAR for ty in diagram[0]) == len(u) + len(w)
        assert paths(graph(seed[0], seed[2]), vertices[0], vertices[-1]) == {u}
        reverse = unfold(ctx, back)
        reverse_source = unfold(ctx, src(ctx, back))
        reverse_inc = read_map(reverse_source, reverse[0], src(reverse[0], reverse[1]))
        low_images = [reverse_inc[i] for i, ty in enumerate(reverse_source[0]) if tdim(ty) <= 0]
        assert len(low_images) == len(set(low_images)) == sum(tdim(ty) <= 0 for ty in reverse[0])
        if u == 'aTb':
            assert not Signature(ctx).guarded(seed, reverse_source)
        templates.append((seed, diagram, entry))
        if u == 'S' and w == 'aSb':
            repeat = comp2(ctx, 3, g, back)
            emitter.check_type('balancedExpansion', ctx, repeat, infer(ctx, repeat))
    h, k = letters['H'], letters['k']
    on_h, on_k = arrow(h, h), arrow(k, k)
    bad_gate = comp2(ctx, 1, comp2(ctx, 0, on_h, k), comp2(ctx, 0, h, on_k))
    bad, _ = attach(word('Hk'), bad_gate)
    bad_ctx, _, _ = unfold(ctx, bad)
    assert not cuts(bad_ctx)
    seed = identity(ctx, identity(ctx, word('lSr')))
    shape, initial, fold = unfold(ctx, seed)
    start, finish = object_poles(shape, initial)
    expected = {'lSr'}
    for step in range(5):
        # Create a fresh expansion at the innermost S-edge on the longest path.
        source, rule, inc = templates[0]
        matches = list(maps_over(source[0], source[2], shape, fold))
        def depth(m):
            x = m[object_poles(source[0], source[1])[0]][1]
            return max(map(len, paths(graph(shape, fold), start, x)))
        chosen = max(matches, key=depth)
        shape, fold, prev, _ = pushout(shape, fold, rule[0], rule[2], chosen, inc)
        start, finish = prev[start][1], prev[finish][1]
        expected.add('l' + 'a' * (step + 1) + 'S' + 'b' * (step + 1) + 'r')
        assert paths(graph(shape, fold), start, finish) == expected
    print('All five word-rule diagrams add exactly the alternate path. Five nested expansions give six balanced words.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    test_growth(emitter)
    test_alias()
    test_exclusion()
    word_rules(emitter)
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('GuardedOccurrences', __doc__).replace('open import CaTTExp.Pure',
                                                                      'open import CaTTExp.Gray.Pure')
        (args.agda_dir / 'GuardedOccurrences.agda').write_text(module)
