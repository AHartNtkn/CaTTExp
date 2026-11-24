"""Compare all raw and all published colourings along a fold of nonglobular computads."""
from argparse import ArgumentParser
from collections import Counter
from functools import cache
from itertools import product
from pathlib import Path
import re
from tempfile import TemporaryDirectory

from catt import STAR, arr, check_ctx, comp2, disc_tree, infer, maximal_vars, sub_from, subst_tm, subst_ty, tdim_tm, tree_ctx, v
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import ident
from relative_coherence_exchange_faces import head, string_tree
from semistrict_surface_boundary_tracks import inverse_terms, pattern
from semistrict_surface_chart_pullback import ChartPullback
from semistrict_surface_computad_folds import disc_head
from semistrict_surface_exact_boundary import run
from semistrict_surface_insertion_cut import Assertions


def unit_pad(ctx, a):
    return comp2(ctx, 1, ident(ctx, infer(ctx, a)[2]), a)


def contexts():
    obj = v(0)
    edge = arr(STAR, obj, obj)
    ctx = (STAR, edge)
    f = v(1)
    path = comp2(ctx, 0, f, f)
    two = arr(edge, path, path)
    a = v(2)
    ctx += (two, two)  # second variable has no colour
    aa = comp2(ctx, 1, a, a)
    three = arr(infer(ctx, aa), aa, unit_pad(ctx, aa))
    ctx += (three,)

    # Two different intermediate vertices realize the folded two-edge path.
    cover = (STAR,) * 4
    cover += tuple(arr(STAR, v(i), v(j)) for i, j in ((0, 1), (1, 3), (0, 2), (2, 3)))
    l, r = (comp2(cover, 0, v(i), v(i+1)) for i in (4, 6))
    labels = [v(0)] * 4 + [v(1)] * 4
    for lo, hi in ((l, l), (l, r), (r, l), (r, r)):
        cover += (arr(infer(cover, lo), lo, hi),)
        labels.append(a)
    for i, j in ((8, 9), (9, 10), (9, 10), (11, 11)):
        pair = comp2(cover, 1, v(i), v(j))
        cover += (arr(infer(cover, pair), pair, unit_pad(cover, pair)),)
        labels.append(v(4))
    tail = v(len(cover))
    cover += (arr(STAR, v(3), v(3)),)
    labels.append(f)
    tail_path = comp2(cover, 0, tail, tail)
    cover += (arr(infer(cover, tail_path), tail_path, tail_path),)
    labels.append(a)
    for g in (ctx, cover):
        check_ctx(g)
    for ty, t in zip(cover, labels, strict=True):
        assert subst_ty(ty, labels) == infer(ctx, t)
    return ctx, cover, tuple(labels)


class RiceFibres:
    def __init__(self, binary, directory, flags):
        self.binary = binary
        self.directory = directory
        self.flags = flags
        self.code = Assertions()

    def spelling(self, t, prefix):
        return re.sub(r'\bx(\d+)\b', prefix + r'\1', self.code.term(t))

    def telescope(self, ctx, prefix):
        def show(ty):
            return '*' if ty == STAR else ' -> '.join(self.spelling(x, prefix) for x in ty[2:])
        return ' '.join(f'({prefix}{i} : {show(ty)})' for i, ty in enumerate(ctx))

    @cache
    def normal(self, ctx, prefix, expr, allow_mismatch=False):
        decl = self.telescope(ctx, prefix)
        (self.directory/'Terms.catt').write_text('\n'.join(
            [*self.code.commands, f'normalise {expr} in {decl}']) + '\n')
        out = run(self.binary, self.directory, 'Terms.catt', self.flags)
        if allow_mismatch and 'Error:' in out and any(s in out for s in
                ('does not match', 'Mismatch between', 'mismatch', 'do not match', 'do not have')):
            return None
        if 'Error:' in out or 'Finished importing Terms.catt' not in out:
            raise ValueError(out[-3200:])
        form, = re.findall(r'Normal form:\s*(.*?)\s+has type:', out, re.S)
        return ' '.join(form.split())

    def raw_form(self, ctx, prefix, t):
        return self.normal(ctx, prefix, self.spelling(t, prefix))

    def colourings(self, ctx, fold, normal, prefix):
        # Printed maximal arguments determine the full globular labelling.
        # The generator prefix is reserved for free names, never bound paths.
        slots = list(re.finditer(r'\bbase(\d+)\b', normal))
        choices = [[j for j, val in enumerate(fold) if val == v(int(slot[1]))] for slot in slots]
        accepted = set()
        for colours in product(*choices):
            parts, start = [], 0
            for slot, i in zip(slots, colours, strict=True):
                parts.extend((normal[start:slot.start()], f'{prefix}{i}'))
                start = slot.end()
            candidate = ''.join(parts) + normal[start:]
            result = self.normal(ctx, prefix, candidate, True)
            if result is not None:
                accepted.add(result)
        return accepted


def raw_examples(ctx):
    a, missing, change = v(2), v(3), v(4)
    aa = comp2(ctx, 1, a, a)
    arity, (x, y) = pattern([2, 2])
    full = comp2(arity, 0, x, y)
    horizontal_endo = head(arity, full, full)
    label = sub_from(arity, ctx, dict(zip(maximal_vars(arity), (a, a), strict=True)))
    string, (i, j, k) = pattern([1, 1, 1])
    left = comp2(string, 0, comp2(string, 0, i, j), k)
    right = comp2(string, 0, i, comp2(string, 0, j, k))
    assoc = head(string, left, right)
    edge_label = sub_from(string, ctx, dict.fromkeys(maximal_vars(string), v(1)))
    vertical = tree_ctx(string_tree(1, [2, 2]))
    row = comp2(vertical, 1, *map(v, maximal_vars(vertical)))
    tag = head(vertical, row, row)
    at_pair = sub_from(vertical, ctx, dict.fromkeys(maximal_vars(vertical), a))
    nested = comp2(ctx, 0, comp2(ctx, 0, v(1), a), v(1))
    globe, (x,) = pattern([2])
    unpad = head(globe, unit_pad(globe, x), x)
    bridge = subst_tm(unpad, sub_from(globe, ctx, {x[1]: aa}))
    change_twice = comp2(ctx, 2, comp2(ctx, 2, change, bridge), change)
    return (subst_tm(tag, at_pair), nested, change_twice, a, missing, aa, unit_pad(ctx, aa), comp2(ctx, 1, aa, a), disc_head(ctx, aa),
            subst_tm(horizontal_endo, label), subst_tm(assoc, edge_label), change,
            comp2(ctx, 2, ident(ctx, aa), change), disc_head(ctx, ident(ctx, change)))


def sharpness(rice, ctx):
    obj, f, a = v(0), v(1), v(2)
    point = (STAR,)
    id_point = ident(point, v(0))
    point_head = head(point, id_point, id_point)
    def contains(term, part):
        return term == part or term[0] == 'coh' and any(contains(t, part) for t in term[3])
    aa = comp2(ctx, 1, a, a)
    alternatives = (
        (aa, comp2(ctx, 1, disc_head(ctx, a), a)),
        (ident(ctx, f), ident(ctx, disc_head(ctx, f))),
        (disc_head(ctx, a), a),
        (subst_tm(point_head, (obj,)), ident(ctx, ident(ctx, obj))),
    )
    for image, other in alternatives:
        rank = tdim_tm(ctx, image)
        disc = tree_ctx(disc_tree(rank))
        top, = maximal_vars(disc)
        lab = sub_from(disc, ctx, {top: image})
        assert rice.raw_form(ctx, 'base', image) == rice.raw_form(ctx, 'base', other)
        assert not contains(other, image)
        for t in inverse_terms(disc, lab)(other):
            assert rice.raw_form(disc, 'upper', t) != f'upper{top}'
    disc, (x,) = pattern([1])
    lab = sub_from(disc, point, {x[1]: id_point})
    raw = comp2(point, 0, id_point, id_point)
    lifts = inverse_terms(disc, lab)(raw)
    examples = (comp2(disc, 0, x, ident(disc, v(1))), comp2(disc, 0, ident(disc, v(0)), x))
    assert examples[0] != examples[1] and all(t in lifts for t in examples)
    assert all(rice.raw_form(disc, 'upper', t) == f'upper{x[1]}' for t in examples)
    return len(alternatives) + 1


def verify(binary, directory, flags):
    ctx, cover, fold = contexts()
    rice = RiceFibres(binary, directory, flags)
    inv = inverse_terms(cover, fold)
    counts = Counter()
    for raw in raw_examples(ctx):
        normal = rice.raw_form(ctx, 'base', raw)
        actual = rice.colourings(cover, fold, normal, 'upper')
        lifts = inv(raw)
        lifted_forms = {rice.raw_form(cover, 'upper', t) for t in lifts}
        assert len(lifted_forms) == len(lifts) and lifted_forms == actual, (normal, lifted_forms, actual)
        counts['raw fibres'] += 1
        counts['raw lifts'] += len(lifts)
        counts['empty'] += int(not lifts)

    # The second leg sends a generator to a composite and two generators to
    # the same padded 3-cell. Their top composite is only surface-typed.
    q = ctx[:3]
    y = v(2)
    decl = arr(infer(q, y), y, unit_pad(q, y))
    q += (decl, decl)
    aa = comp2(ctx, 1, v(2), v(2))
    padded = comp2(ctx, 2, ident(ctx, aa), v(4))
    beta = (v(0), v(1), aa, padded, padded)
    common = ChartPullback((cover, fold), (q, beta))
    proj_p, proj_q = common.projections
    assert all(t[0] == 'v' for t in proj_q)
    assert any(ty != STAR and any(t[0] == 'coh' for t in ty[2:]) for ty in common.ctx)
    # Enumerate all first coordinates and all candidates over the second
    # coordinate separately. Evaluate the first projection by substitution.
    weak = RiceFibres(binary, directory, ())
    assert weak.normal(q, 'base', 'comp[base3,base4]', True) is None
    for first, second in product((3, 4), repeat=2):
        written = f'comp[base{first},base{second}]'
        right = rice.normal(q, 'base', written)
        image = rice.normal(ctx, 'base', f'comp[{rice.spelling(padded,"base")},{rice.spelling(padded,"base")}]')
        target = rice.colourings(cover, fold, image, 'upper')
        lifted = rice.colourings(common.ctx, proj_q, right, 'pair')
        def project(term):
            return re.sub(r'\bpair(\d+)\b', lambda m: rice.spelling(proj_p[int(m[1])], 'upper'), term)
        projected = {rice.normal(cover, 'upper', project(t)) for t in lifted}
        assert lifted and len(projected) == len(lifted) and projected == target
        counts['surface pairs'] += len(lifted)
    counts['sharpness cases'] = sharpness(rice, ctx)
    counts['transported square lifts'] = signed_transport(rice, q)
    return counts


def signed_transport(rice, q):
    chart = tree_ctx(string_tree(1, [3, 3]))
    m, n = map(v, maximal_vars(chart))
    early, late = temporal_words(chart, m, n, 1, 2)
    square = head(chart, early, late)
    label = sub_from(chart, q, {m[1]: v(3), n[1]: v(4)})
    templates = [rice.spelling(subst_tm(t, label), 'slot') for t in (early, square, late)]
    upper = (*q, q[3], q[4])
    fold = (*map(v, range(len(q))), v(3), v(4))

    def readings(ctx, prefix, i, j, k):
        names = [prefix + str(a) for a in range(3)]
        names += [f'comp[{prefix}{i},{prefix}{j}]', prefix + str(k)]
        return tuple(rice.normal(ctx, prefix, re.sub(r'\bslot(\d+)\b', lambda m: names[int(m[1])], t))
                     for t in templates)

    downstairs = readings(q, 'base', 3, 3, 4)
    assert downstairs[0] != downstairs[2]
    all_lifts = [rice.colourings(upper, fold, t, 'upper') for t in downstairs]
    triples = [readings(upper, 'upper', i, j, k) for i, j, k in product((3, 5), (3, 5), (4, 6))]
    for col, possible in enumerate(all_lifts):
        assert {triple[col] for triple in triples} == possible and len(possible) == len(triples)
    return len(triples)


def relative_widths(binary, directory):
    ctx, _, _ = contexts()
    base = ctx[:3]
    a = v(2)
    ty = arr(infer(base, a), a, unit_pad(base, a))
    base += (ty, ty)
    cover = (*base, ty, ty)
    fold = (*map(v, range(len(base))), v(3), v(4))
    modes = [RiceFibres(binary, directory, flags) for flags in
             (('--su',), ('--insertion-width', '1'), ('--sua',))]
    # The temporal subterm already needs unit conversion in the weakest
    # mode. The spatial example then changes its bracketing at higher width.
    temporal = 'comp[comp[base3,base3],base4]'
    nested = comp2(base, 0, comp2(base, 0, v(1), v(3)), v(1))
    coloured = 0
    for low, high in zip(modes, modes[1:]):
        spatial = low.spelling(nested, 'base').replace('base3', 'comp[base3,base4]')
        changed = False
        for expr in (temporal, spatial):
            old = low.normal(base, 'base', expr)
            image = high.normal(base, 'base', old)
            changed |= old != image
            before = low.colourings(cover, fold, old, 'upper')
            after = high.colourings(cover, fold, image, 'upper')
            assert before and len(before) == len(after)
            assert {high.normal(cover, 'upper', t) for t in before} == after
            coloured += len(before)
        assert changed
    return coloured


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rice-binary', required=True, type=Path)
    args = parser.parse_args()
    with TemporaryDirectory() as temporary:
        for mode in (['--su'], ['--insertion-width', '1'], ['--sua']):
            print(mode, dict(verify(args.rice_binary.resolve(), Path(temporary), tuple(mode))), flush=True)
        print('Paired colourings across successive widths:', relative_widths(args.rice_binary.resolve(), Path(temporary)))
