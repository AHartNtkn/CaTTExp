"""Lift raw CaTT expressions on repeated loop edges to their path positions."""

from collections import Counter
from functools import cache
from itertools import product

from catt import STAR, arr, comp2, infer, subst_tm, subst_ty, tree_ctx, v
from ct_suspension import susp_ctx
from relative_coherence_cut import Cut, outer_edge
from relative_coherence_hidden_seam import identity


def attach(ctx, body, poles):
    labels = list(map(v, poles))
    for ty in susp_ctx(body)[2:]:
        labels.append(v(len(ctx)))
        ctx.append(subst_ty(ty, labels))
    return labels[2:]


@cache
def columns(arity):
    objects = [i for i, ty in enumerate(arity) if ty == STAR]
    slots = {i: j for j, i in enumerate(objects)}
    arrows = []
    for i, ty in enumerate(arity):
        if ty != STAR:
            s, t = outer_edge(ty)
            j = slots[s]
            assert t == objects[j + 1]
            slots[i] = j
            if ty[1] == STAR and j == len(arrows):
                arrows.append(i)
    return slots, arrows


def check():
    # Include a generator attached to a composite, so that lifting a variable's
    # type exercises more than the incidence maps of a globular set.
    base = tree_ctx(((), ()))
    composite = comp2(base, 0, v(2), v(4))
    body = base + (arr(infer(base, composite), composite, composite),)
    graph = [STAR]
    loops = [attach(graph, body, (0, 0)) for _ in range(2)]
    graph = tuple(graph)
    owners = {term: e for e, block in enumerate(loops) for term in block}

    @cache
    def word(term):
        if term[0] == 'v':
            return (owners[term],)
        _, arity, _, args = term
        return tuple(e for i in columns(arity)[1] for e in word(args[i]))

    counts = Counter()
    for length in range(1, 5):
        for path in product(range(2), repeat=length):
            chain = [STAR] * (length + 1)
            copies = [attach(chain, body, (i, i + 1)) for i in range(length)]
            chain = tuple(chain)
            fold = (v(0),) * (length + 1) + tuple(t for e in path for t in loops[e])
            lift_slot = [dict(zip(loops[e], block)) for e, block in zip(path, copies)]

            def lift(term, left, right):
                if term == v(0):
                    assert left == right
                    return v(left)
                assert word(term) == path[left:right]
                if term[0] == 'v':
                    assert right == left + 1
                    return lift_slot[left][term]
                _, arity, ty, args = term
                slots, arrows = columns(arity)
                ends = [left]
                for i in arrows:
                    ends.append(ends[-1] + len(word(args[i])))
                assert ends[-1] == right
                labels = []
                for i, arg in enumerate(args):
                    j = slots[i]
                    k = j if arity[i] == STAR else j + 1
                    labels.append(lift(arg, ends[j], ends[k]))
                return ('coh', arity, ty, tuple(labels))

            # On a repeated edge the fold identifies labels at different sites.
            # An identity at each seam forces an empty interval during lifting.
            cells = [block[-1] for block in copies]
            term = identity(chain, v(0))
            for i, cell in enumerate(cells):
                term = comp2(chain, 0, term, cell)
                term = comp2(chain, 0, term, identity(chain, v(i + 1)))
            for expression in (term, identity(chain, term), *infer(chain, term)[2:]):
                old = subst_tm(expression, fold)
                assert infer(graph, old) == subst_ty(infer(chain, expression), fold)
                rebuilt = lift(old, 0, length)
                assert rebuilt == expression
                for i in range(length):
                    cut = Cut(chain, range(i + 1, length + 1))
                    assert cut.context() == body
                    assert infer(body, cut.term(rebuilt)) == cut.type(infer(chain, rebuilt))
                    counts['typed projections'] += 1
                counts['unique lifts with empty subintervals'] += 1
    for label, count in counts.items():
        print(f'{count} {label}')


if __name__ == '__main__':
    check()
