"""Check nonempty string charts on both sides of top insertion."""
import argparse
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from random import Random
from tempfile import TemporaryDirectory

from catt import (STAR, arr, check_ctx, comp2, disc_tree, glue_tree, infer, ps_boundary_vars,
                  subst_tm, subst_ty, tdim, tree_ctx, v)
from ct_suspension import ident
from partial_cylinder_steiner import trees
from relative_coherence_exchange_faces import head, string_tree
from semistrict_surface_elementary_insertions import exterior, slots
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_insertion_cut import Assertions, standard, variables
from semistrict_surface_scalar_pairs import splice
from semistrict_surface_unital_reassociation import check_rice
from steiner import Complex


@dataclass(frozen=True)
class String:
    beads: tuple
    seams: tuple

    def faces(self):
        return (self.seams[0], self.seams[-1]) if self.seams else ()

    def part(self, i):
        return String(self.beads[i:i+1], self.seams[i:i+2])

    def value(self, chart):
        t = self.beads[0]
        rank = tdim(infer(chart, t))+1
        for bead in self.beads[1:]:
            t = comp2(chart, rank-1, t, bead)
        return t


def fresh(chart, rank, faces, rng):
    if not rank:
        vertex = v(len(chart))
        chart.append(STAR)
        return String((vertex,), ())
    a, b = faces
    seams = [a] + [fresh(chart, rank-1, a.faces(), rng) for _ in range(rng.randrange(3))] + [b]
    beads = []
    for source, target in zip(seams, seams[1:]):
        ctx = tuple(chart)
        s, t = source.value(ctx), target.value(ctx)
        assert infer(ctx, s) == infer(ctx, t)
        beads.append(v(len(chart)))
        chart.append(arr(infer(ctx, s), s, t))
    return String(tuple(beads), tuple(seams))


def assignment(tree, peaks):
    """Recover every coordinate, checking the entire shared seam on overlaps."""
    arity = tree_ctx(tree)
    data = [None] * len(arity)

    def put(i, label):
        if data[i] is not None:
            assert data[i] == label
            return
        data[i] = label
        for face, seam in zip(arity[i][2:], label.faces(), strict=True):
            put(face[1], seam)

    for p, i in slots(tree).items():
        put(i, peaks[p])
    assert None not in data
    return tuple(data)


def normal(tree, labels):
    """Unroll all maximal strings; coordinates on an intermediate seam stay intact."""
    peaks = {p: labels[i] for p, i in slots(tree).items()}
    for path in sorted(peaks, reverse=True):
        label = peaks[path]
        length = len(label.beads)
        if length == 1:
            continue
        d = len(path)
        tree = splice(tree, path, string_tree(d-1, [d]*length))
        parent, i = path[:-1], path[-1]
        new = {}
        for p, cell in peaks.items():
            if p == path:
                new.update((parent+(i+k,), label.part(k)) for k in range(length))
            elif p[:d-1] == parent and p[d-1] > i:
                new[parent+(p[d-1]+length-1,)+p[d:]] = cell
            else:
                new[p] = cell
        peaks = new
    return tree, assignment(tree, peaks)


def diagram_checks(limit, rng, checks):
    counts = Counter()
    for size in range(1, limit+1):
        for tree in trees(size):
            for path in slots(tree):
                d = len(path)
                for m in (2, 3):
                    joined, sigma = exterior(tree, path, string_tree(d-1, [d]*m))
                    chart, labels = [], []
                    for ty in tree_ctx(joined):
                        faces = tuple(labels[x[1]] for x in ty[2:])
                        labels.append(fresh(chart, tdim(ty)+1, faces, rng))
                    chart = tuple(chart)
                    check_ctx(chart)
                    assert Complex(chart).is_strong_steiner()
                    fragments = [labels[slots(joined)[path[:-1]+(path[-1]+k,)]]
                                 for k in range(m)]
                    seams = list(fragments[0].seams)
                    for f in fragments[1:]:
                        assert seams[-1] == f.seams[0]
                        seams.extend(f.seams[1:])
                    merged = String(tuple(b for f in fragments for b in f.beads), tuple(seams))
                    original = tuple(labels[t[1]] if t[0] == 'v' else merged for t in sigma)
                    assert normal(tree, original) == normal(joined, labels)
                    counts['complete expanded tuples'] += 1
                    if max(map(len, slots(tree))) > d:
                        counts['splits below the outer height'] += 1
                    if any(len(s.beads)>1 for s in merged.seams):
                        counts['splits with subdivided seams'] += 1
                    # A cell in a chart can be evaluated differently by the two folds.
                    raw = tuple(c.value(chart) for c in labels)
                    active = slots(tree)[path]
                    if subst_tm(sigma[active], raw) != merged.value(chart):
                        counts['distinct raw fold expressions'] += 1

                    # Check the actual generic exact-boundary correction at this arity.
                    ctx, arity = tree_ctx(joined), tree_ctx(tree)
                    outer = standard(arity, max(map(len, slots(tree))))
                    nested = subst_tm(outer, sigma)
                    target = ('coh', ctx, infer(ctx, nested), variables(ctx))
                    correction = head(ctx, nested, target)
                    checks.equal(ctx, correction, ident(ctx, nested), 'generic comparison')
    return counts


def check_old_boundaries(binary):
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder/'Fit.catt').write_text(
            'def enter = coh [ x{a}y{b}z{c}w{d}v : comp[a,b,c,d] -> comp[comp[a,b],c,d] ]\n')
        for n in range(1, 6):
            pole = 'x'
            for _ in range(n-1):
                pole = f'id({pole})'
            ctx = f'(x : *) (a : {pole} -> {pole}) (p : comp[comp[a,a],a,a] -> a)'
            ty = 'comp[a,a,a,a] -> a'
            for name, term in [('fitted', 'comp[enter(a,a,a,a),p]'), ('direct', 'p')]:
                (folder/f'{name}.catt').write_text(f'import Fit\ndef {name} {ctx} : {ty} = {term}\n')
            accepted(run(binary, folder, 'fitted.catt'), 'fitted.catt', ['fitted'])
            rejected(run(binary, folder, 'direct.catt'), 'direct.catt', 'direct')
            rejected(run(binary, folder, 'direct.catt', ['--su']), 'direct.catt', 'direct')
            accepted(run(binary, folder, 'direct.catt', ['--sua']), 'direct.catt', ['direct'])
    print('5 raw fillers at specified scalar boundaries and 15 direct-use verdicts')


def check_pruning(limit):
    counts = Counter()
    for size in range(2, limit+1):
        for tree in trees(size):
            peaks = slots(tree)
            ctx = tree_ctx(tree)
            for path, slot in peaks.items():
                d = len(path)
                for offset in (-1, 1):
                    adjacent = path[:-1]+(path[-1]+offset,)
                    if adjacent not in peaks:
                        continue
                    reduced, prune = exterior(tree, path, disc_tree(d-1))
                    merged = min(path, adjacent)
                    restored, split = exterior(reduced, merged, glue_tree(d, d-1, d))
                    assert restored == tree
                    base = tree_ctx(reduced)
                    active = slots(reduced)[merged]
                    kq = tuple(subst_tm(t, prune) for t in split)
                    assert all(t == v(i) for i, t in enumerate(kq) if i != active)
                    principal = v(active)
                    ty = infer(base, principal)
                    left, right = ((ident(base, ty[2]), principal) if offset == 1 else
                                   (principal, ident(base, ty[3])))
                    assert kq[active] == comp2(base, d-1, left, right)
                    qk = tuple(subst_tm(t, split) for t in prune)
                    seam = ctx[peaks[merged]][3][1]
                    changed = {i for i, t in enumerate(qk) if t != v(i)}
                    assert changed == {slot, peaks[adjacent], seam}
                    counts['oriented adjacent prunings'] += 1
                    if max(map(len, peaks)) == d:
                        assert all(changed.isdisjoint(ps_boundary_vars(ctx, d-1, sign))
                                   for sign in ('-', '+'))
                        ty = infer(ctx, standard(ctx, d))
                        assert subst_ty(ty, qk) == ty
                        counts['full-height signed-boundary descents'] += 1
    return counts


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--edges', type=int, default=4)
    parser.add_argument('--rice-binary', type=Path)
    args = parser.parse_args()
    checks = Assertions()
    for label, count in diagram_checks(args.edges, Random(397), checks).items():
        print(f'{count} {label}')
    for label, count in check_pruning(args.edges).items():
        print(f'{count} {label}')
    if args.rice_binary:
        binary = args.rice_binary.resolve()
        check_rice(checks, binary, '--sua')
        print(f'{sum(checks.count.values())} published comparison classes')
        check_old_boundaries(binary)
