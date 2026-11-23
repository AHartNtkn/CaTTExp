"""Check repeated arity cuts on scalar terms with weak directed labels."""
from argparse import ArgumentParser
from functools import cache
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, comp2, glue_tree, infer, maximal_vars, sub_from,
                  subst_tm, subst_ty, tdim, tree_ctx, v)
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import susp_ctx, susp_tm
from emit_agda import Emitter
from relative_coherence_cut import top_counts
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_insertion_cut import cuts
from semistrict_surface_planar_tiers import artin_step
from semistrict_surface_scalar_arrows import polygon


@cache
def depth_slots(arity, depth):
    """Keep the original indices of each subtree reached at this depth."""
    if depth == 0:
        return [(arity, tuple(range(len(arity))), ())]
    result = []
    for cut in cuts(arity):
        retained = tuple(cut.indices)
        for ctx, slots, path in depth_slots(cut.context(), depth - 1):
            result.append((ctx, tuple(retained[i] for i in slots), (cut,) + path))
    return result


class Selector:
    def __init__(self, ctx, rank, labels):
        self.ctx, self.rank, self.labels = ctx, rank, labels

    @cache
    def weight(self, term):
        ty = infer(self.ctx, term)
        while tdim(ty) + 1 > self.rank:
            term, ty = ty[2], ty[1]
        assert tdim(ty) + 1 == self.rank
        return sum(k for i, k in top_counts(self.ctx, term).items() if i in self.labels)

    @cache
    def read(self, term):
        assert self.weight(term) == 1
        if term[0] == 'v':
            return self.labels[term[1]]
        _, arity, ty, args = term
        selected = []
        for lower, slots, path in depth_slots(arity, self.rank):
            weights = {self.weight(args[i]) for i, a in zip(slots, lower) if a == STAR}
            assert len(weights) == 1
            if weights == {1}:
                selected.append((slots, path))
        (slots, path), = selected
        generic = ('coh', arity, ty, tuple(map(v, range(len(arity)))))
        for cut in path:
            generic = cut.term(generic)
        return subst_tm(generic, tuple(self.read(args[i]) for i in slots))

    def boundary(self, ty):
        if tdim(ty) + 1 == self.rank:
            return STAR
        return arr(self.boundary(ty[1]), self.read(ty[2]), self.read(ty[3]))


def shifted(ctx, labels, rank):
    lifted = labels
    unit = v(0)
    renaming = []
    for _ in range(rank):
        lifted = susp_ctx(lifted)
        renaming.extend((unit, unit))
        unit = identity((STAR,), unit)
    first = len(ctx)
    for ty in lifted[2 * rank:]:
        value = v(len(ctx))
        ctx += (subst_ty(ty, renaming),)
        renaming.append(value)
    return ctx, tuple(renaming), {first + i: v(i) for i in range(len(labels))}


def lift(term, rank, renaming):
    for _ in range(rank):
        term = susp_tm(term)
    return subst_tm(term, renaming)


def check_terms(emitter):
    labels = polygon((), 0, STAR)
    # A scalar at one vertex of the polygon has nonglobular unit faces.
    base_unit = identity(labels, v(0))
    scalar = v(len(labels))
    labels += (arr(infer(labels, base_unit), base_unit, base_unit),)
    pair = comp2(labels, 1, scalar, scalar)
    terms = [v(6), v(8), pair, identity(labels, pair)]
    count = 0
    substitutions = 0
    for rank in (2, 3, 4):
        single, left, left_labels = shifted((STAR,), labels, rank)
        both, right, right_labels = shifted(single, labels, rank)
        for pick, names in enumerate((left_labels, right_labels)):
            selector = Selector(both, rank, names)
            for i, term in enumerate(terms):
                for renaming in (left, right):
                    term_up = lift(term, rank, renaming)
                    if selector.weight(term_up):
                        assert selector.read(term_up) == term
                for cut in range(rank):
                    sides = [lift(term, rank, renaming) for renaming in (left, right)]
                    # Pad only the second copy. The two selections must
                    # detect different raw target faces at the same cut.
                    sides[1] = comp2(both, rank + tdim(infer(labels, term)), sides[1],
                                     identity(both, infer(both, sides[1])[3]))
                    mixed = comp2(both, cut, *sides)
                    read = selector.read(mixed)
                    ty = infer(both, mixed)
                    expected_type = selector.boundary(ty)
                    assert infer(labels, read) == expected_type
                    # The remaining head is the unary disc on the selected
                    # term, whose raw spelling is retained by the cut.
                    assert read[0] == 'coh' and read[3][-1] == selector.read(sides[pick])
                    if i == 1 and cut == rank - 1:
                        emitter.check_type(f'label{rank}side{pick}', labels, read, expected_type)
                    if i == 1:
                        degree = rank + 3
                        arity = tree_ctx(glue_tree(degree, cut, degree))
                        slots = maximal_vars(arity)
                        paths = temporal_words(arity, *map(v, slots), cut, degree - 1)
                        comparison = head(arity, *paths)
                        # Only the mixed argument contains the chosen tag.
                        args = [lift(term, rank, (right, left)[pick]), mixed]
                        if pick == 0:
                            args.reverse()
                        sigma = sub_from(arity, both, dict(zip(slots, args)))
                        actual = selector.read(subst_tm(comparison, sigma))
                        (lower, retained, path), = [
                            part for part in depth_slots(arity, rank) if slots[pick] in part[1]]
                        lower_sigma = tuple(selector.read(sigma[j]) for j in retained)
                        generic = comparison
                        for step in path:
                            generic = step.term(generic)
                        expected = subst_tm(generic, lower_sigma)
                        assert actual == expected
                        assert infer(labels, actual) == subst_ty(infer(lower, generic), lower_sigma)
                        if rank == 2 and cut == 0:
                            emitter.check_eq(f'nested{pick}', generic, lower_sigma, actual)
                        substitutions += 1
                    count += 1
    return count, substitutions


def check_braid(checkout):
    exe = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as folder:
        root = Path(folder)
        (root / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        for rank in (2, 3, 4):
            unit = 'x'
            for _ in range(rank - 1):
                unit = f'id({unit})'
            ctx = f'(x : *) (a : {unit} -> {unit}) (b : {unit} -> {unit}) (u : id(a) -> id(a))'
            (root / 'Mixed.catt').write_text(f"""import examples/eh
def moving {ctx} = comp[[[[eh(a,u,u)]]],b]
def still {ctx} = comp[[[[id(comp[u,u])]]],b]
def fitted {ctx} : moving(x,a,b,u) -> comp[moving(x,a,b,u),id(comp[[[comp[u,u]]],b])] = unitor_r_inv(moving(x,a,b,u))
""")
            (root / 'Bad.catt').write_text(f"""import Mixed
def collapsed {ctx} : moving(x,a,b,u) -> still(x,a,b,u) = id(moving(x,a,b,u))
""")
            for flags in ([], ['--su'], ['--sua']):
                accepted(run(exe, root, 'Mixed.catt', flags), 'Mixed.catt', ['moving', 'still', 'fitted'])
                rejected(run(exe, root, 'Bad.catt', flags), 'Bad.catt', 'collapsed')


def check_braid_labels():
    # The same braid can be spelt by either side of an Artin relation.
    # Put different noncommuting label paths on its incoming strands,
    # and compare with appending those steps at the transported outputs.
    checked = 0
    for size in range(2, 6):
        basis = tuple((i + 1,) for i in range(size))

        def braid(moves):
            action, order = basis, list(range(size))
            for i in moves:
                action = artin_step(action, i)
                order[i], order[i + 1] = order[i + 1], order[i]
            return action, order

        for i, j in product(range(size - 1), repeat=2):
            if i == j:
                action, order = braid((i, i))
                assert order == list(range(size)) and action != basis
                continue
            first, second = ((i, j, i), (j, i, j)) if abs(i - j) == 1 else ((i, j), (j, i))
            action, order = braid(first)
            assert braid(second) == (action, order)
            endpoint = []
            for word in action:
                exponents = [word.count(k) - word.count(-k) for k in range(1, size + 1)]
                assert sorted(exponents) == [0] * (size - 1) + [1]
                endpoint.append(exponents.index(1))
            for source in range(size):
                paths = [(k,) for k in range(size)]
                paths[source] += ('p', 'q')
                for move in second:
                    paths[move], paths[move + 1] = paths[move + 1], paths[move]
                after = [(k,) for k in endpoint]
                after[endpoint.index(source)] += ('p', 'q')
                assert paths == after
                assert paths[endpoint.index(source)] != (source, 'q', 'p')
                checked += 1
    return checked


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    terms, substitutions = check_terms(emitter)
    print(f'{terms} mixed terms checked at both faces; {substitutions} nested substitution equations.')
    print(f'{check_braid_labels()} strand transports across braid relations.')
    if args.agda_dir:
        name = 'WeakLabelCuts'
        (args.agda_dir / f'{name}.agda').write_text(emitter.module(name, __doc__))
    check_braid(args.checkout.resolve())
    print('Two-particle label braids checked in ranks 2, 3 and 4 in all three modes.')
