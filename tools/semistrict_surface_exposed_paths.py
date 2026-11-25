"""Classify all stacks of outer heads from a named loop at a compound attachment."""

from functools import cache
from itertools import product

from catt import (STAR, arr, chain_tree, check_ctx, coh_between, disc_tree, fv_tm, infer, maximal_vars,
                  mk_coh, subst_ty, tdim, tdim_tm, tree_ctx, ucomp, v)
from relative_coherence_hidden_seam import identity
from semistrict_surface_equal_rank import suspend
from semistrict_surface_flat_heads import flat_head, routes
from semistrict_surface_grid_tracks import temporal
from semistrict_surface_two_heads import outer_charts, two_heads


class ExposedPaths:
    def __init__(self, base, attachment, names, edges):
        check_ctx(base)
        ty = infer(base, attachment)
        rank = tdim_tm(base, attachment) + 1
        if rank < 2 or attachment[0] == 'v' or any(x[0] != 'v' for x in ty[2:]):
            raise ValueError('Expected a compound attachment with variable immediate faces')
        for t in base:
            if tdim(t) + 1 >= rank or (t != STAR and any(x[0] != 'v' for x in t[2:])):
                raise ValueError('Expected a lower globular base')
        hidden = {i for i in fv_tm(attachment) if tdim(base[i]) + 1 == rank - 1}
        if not hidden:
            raise ValueError('The attachment must use a top-dimensional lower name')
        self.edges = tuple(edges)
        if names < 1 or any(not (0 <= a < names and 0 <= b < names) for a, b in self.edges):
            raise ValueError('Invalid graph of exposed names')
        self.z = tuple(v(len(base) + i) for i in range(names))
        self.alphabet = tuple(v(len(base) + names + i) for i in range(len(edges)))
        loop = arr(ty, attachment, attachment)
        self.ctx = base + (loop,) * names + tuple(arr(loop, self.z[a], self.z[b]) for a, b in edges)
        self.rank = rank
        self.attachment = attachment
        self.hidden = hidden
        self.renaming = []
        new = []
        for i, t in enumerate(base):
            if i in hidden:
                self.renaming.append(None)
            else:
                self.renaming.append(v(len(new)))
                new.append(subst_ty(t, self.renaming))
        self.atom = v(len(new))
        new_ty = subst_ty(ty, self.renaming)
        new.append(new_ty)
        self.new_z = tuple(v(len(new) + i) for i in range(names))
        new_loop = arr(new_ty, self.atom, self.atom)
        self.collapsed = tuple(new) + (new_loop,) * names
        self.renaming.extend(self.new_z)
        check_ctx(self.ctx)
        check_ctx(self.collapsed)

    @cache
    def decode(self, term):
        if term == self.attachment:
            return self.atom
        if term[0] == 'v':
            return self.renaming[term[1]]
        values = tuple(self.decode(x) for x in term[3])
        if None in values:
            return None
        return mk_coh(term[1], term[2], values)

    @cache
    def colored_events(self, decoded):
        if decoded[0] == 'v':
            return (self.new_z.index(decoded),) if decoded in self.new_z else ()
        return tuple(c for i in maximal_vars(decoded[1])
                     if tdim_tm(decoded[1], v(i)) == self.rank
                     for c in self.colored_events(decoded[3][i]))

    def path(self, start, target, counts=None, reverse=False):
        if infer(self.ctx, target) != infer(self.ctx, self.z[start]):
            raise ValueError('Target is not parallel to the exposed name')
        if counts is not None:
            counts = tuple(counts)
            if len(counts) != len(self.edges) or any(type(n) is not int or n < 0 for n in counts):
                raise ValueError('Expected a nonnegative multiplicity per graph edge')
        decoded = self.decode(target)
        if decoded is None:
            return None
        assert infer(self.collapsed, decoded) == infer(self.collapsed, self.new_z[start])
        events = self.colored_events(decoded)
        if len(events) != 1:
            return None
        end, = events
        return routes([(end, start) if reverse else (start, end)], self.edges, counts)


def family(rank, width, folded):
    if folded:
        base = tree_ctx(disc_tree(rank - 2))
        face = v(len(base) - 1)
        u = v(len(base))
        base += (arr(infer(base, face), face, face),)
        attachment = u
        for _ in range(width - 1):
            attachment = temporal(base, attachment, u)
    else:
        base = tree_ctx(suspend(chain_tree(width), rank - 2))
        attachment = ucomp(base)
    solver = ExposedPaths(base, attachment, 4, ((0, 1), (1, 2), (2, 1), (3, 3)))
    return solver, base


def checks():
    decisions = charts = 0
    for rank, width, folded in ((2, 2, False), (2, 4, True), (3, 3, False), (5, 3, True)):
        solver, base = family(rank, width, folded)
        ctx, z, p = solver.ctx, solver.z, solver.attachment
        unit = identity(ctx, p)
        terms = [unit]
        for x in z:
            terms.extend([x, temporal(ctx, x, unit), temporal(ctx, unit, x), temporal(ctx, x, x)])
        if folded:
            # Keep the whole bracketed string in the bound type as the tips fold.
            tree = suspend(chain_tree(width), rank - 2)
            arity = tree_ctx(tree)
            letters = [v(i) for i in maximal_vars(arity)]
            total = letters[0]
            for x in letters[1:]:
                total = temporal(arity, total, x)
            kappa = coh_between(base, tree, [v(len(base) - 1)] * width, total, total)
        else:
            kappa = mk_coh(base, arr(infer(base, p), p, p), tuple(v(i) for i in range(len(base))))
        terms.extend(temporal(ctx, x, kappa) for x in z)
        graph = [infer(ctx, e)[2:] for e in solver.alphabet]
        for t in terms:
            for start, reverse, counts in product((0, 1, 3), (False, True),
                    (None, (0, 0, 0, 0), (1, 1, 0, 0), (0, 1, 1, 0), (0, 0, 0, 2))):
                a, b = (t, z[start]) if reverse else (z[start], t)
                feasible = solver.path(start, t, counts, reverse) is not None
                assert feasible == (flat_head(ctx, a, b, solver.alphabet, counts) is not None)
                decisions += 1
            if solver.path(0, t) is not None:
                for reverse in (False, True):
                    for _, _, sigma, destination, segments in outer_charts(ctx, t, rank, graph, reverse):
                        assert all(solver.decode(value) is not None for value in sigma + destination)
                        assert sum(a != b for a, b in segments) <= 1
                        charts += 1
    return decisions, charts


def derived_labels():
    solver, base = family(5, 3, False)
    p = solver.attachment
    unit = identity(base, p)
    tree = suspend(chain_tree(3), 3)
    tips = [v(i) for i in maximal_vars(base)]
    kappa = coh_between(base, tree, tips, p, p)
    tucked = temporal(solver.ctx, solver.z[1], kappa)
    fitted = 0
    for backward in (False, True):
        ends = (unit, kappa) if backward else (kappa, unit)
        inner = coh_between(base, tree, tips, *ends)
        # There is an actual named edge in each indicated direction.
        edge = solver.alphabet[2 if backward else 1]
        a, b = (solver.z[2], tucked) if backward else (tucked, solver.z[2])
        assert two_heads(solver.ctx, a, b, [inner, edge], (1, 1)) is not None
        fitted += 1
    return fitted


if __name__ == '__main__':
    cases, charts = checks()
    print(f'{cases} forward/reverse and multiplicity decisions agree with raw head construction')
    print(f'All labels stay guarded in {charts} reachable chart and endpoint choices')
    print(f'{derived_labels()} degree-six fits use a derived inner label and a directed name once each')
