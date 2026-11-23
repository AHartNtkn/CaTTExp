"""Check the square substitution, its degeneration and the scalar-cover obstruction."""

from collections import Counter
from itertools import product

from catt import STAR, arr, check_ctx, comp2, infer, ps_dim, v
from gray_globe_comparison import atom, boundary, globe
from relative_coherence_cut import Cut
from relative_coherence_hidden_seam import identity
from semistrict_surface_path_lift import attach

EDGE = (1, 2)
SQUARE = (EDGE, EDGE)
DISC = (2, 2)


def substitute(basis, collapse):
    """Classify the directed square, or the identity on an interval, at slot 0."""
    (rank, tag), rest = basis[0], basis[1:]
    if collapse:
        if rank == 2:
            return ()
        return (((EDGE if rank else (0, tag)),) + rest,)
    square = atom(SQUARE)
    replacements = square[rank][0 if rank == 2 else tag]
    return tuple(pair + rest for pair in replacements)


def map_rows(tableau, collapse):
    def row(chain):
        return tuple(sorted(y for x in chain for y in substitute(x, collapse)))
    return tuple((row(source), row(target)) for source, target in tableau)


def on_chain(chain, function):
    image = Counter()
    for cell, coefficient in chain.items():
        for target in function(cell):
            image[target] += coefficient
    return {g: v for g, v in image.items() if v}


def differential(chain):
    result = Counter()
    for cell in chain:
        result.update(boundary(cell))
    return {g: v for g, v in result.items() if v}


def lift_cell(basis, start):
    rank = sum(dimension for dimension, _ in basis)
    pos = start + sum(tag for dimension, tag in basis if dimension == 0)
    return rank, pos


def height(chain, start):
    return sum(lift_cell(cell, start)[1] for cell in chain)


def marked_boundary(basis):
    """Cover with separately named axes; retain the active set and completed bits."""
    def label(word):
        return (tuple(i for i, (rank, _) in enumerate(word) if rank),
                tuple(tag if rank == 0 else 0 for rank, tag in word))

    return on_chain(boundary(basis), lambda g: (label(g),))


def walking_piece(depth):
    """Finite ordinary skeleton of the separate-inverse walking equivalence."""
    ctx = [STAR, STAR]

    def declare(s, t):
        context = tuple(ctx)
        base = infer(context, s)
        assert infer(context, t) == base
        cell = v(len(ctx))
        ctx.append(arr(base, s, t))
        return cell

    witnesses = [declare(v(0), v(1))]
    for degree in range(1, depth + 1):
        next_witnesses = []
        for u in witnesses:
            source, target = ctx[u[1]][2:]
            left, right = declare(target, source), declare(target, source)
            if degree < depth:
                context = tuple(ctx)
                for x, y, pole in ((u, right, source), (left, u, target)):
                    composite = comp2(context, degree - 1, x, y)
                    next_witnesses.append(declare(composite, identity(context, pole)))
        witnesses = next_witnesses
    check_ctx(tuple(ctx))
    return tuple(ctx)


def check_contexts(counts):
    for d in range(3, 7):
        body = walking_piece(d - 2)
        ctx = [STAR] * d
        for i in range(d - 1):
            attach(ctx, body, (i, i + 1))
        chain = tuple(ctx)
        check_ctx(chain)
        assert ps_dim(chain) == d - 1
        for i in range(d - 1):
            assert Cut(chain, range(i + 1, d)).context() == body
        endo = [STAR]
        attach(endo, body, (0, 0))
        check_ctx(tuple(endo))
        assert ps_dim(tuple(endo)) == d - 1
        counts['typed finite chain and loop presentations'] += 2


def check():
    counts = Counter()
    for k in range(2, 10):
        tail = (EDGE,) * (k - 2)
        theta = atom((DISC,) + tail)
        actual = map_rows(theta, False)
        assert actual == atom((EDGE,) * k)
        collapsed = map_rows(theta, True)
        assert collapsed[-1] == ((), ())
        # Compare every row, including the endpoints of the lower identity.
        assert collapsed[:-1] == atom((EDGE,) * (k - 1))
        source, target = actual[-2]
        for start in (0, 1, 7):
            assert height(target, start) - height(source, start) == k % 2
            counts['lifted boundary height differences'] += 1

        for basis in product(globe(2), *(globe(1) for _ in tail)):
            for collapse in (False, True):
                assert on_chain(boundary(basis), lambda g: substitute(g, collapse)) == (
                    differential(substitute(basis, collapse)))
                counts['substitution chain equations'] += 1

        # Lift every face with its own starting vertex, including translated
        # copies. Distinct upper and lower faces can coincide after this fold.
        for basis in product(globe(1), repeat=k):
            for start in (0, 4):
                r, pos = lift_cell(basis, start)
                result = on_chain(boundary(basis), lambda g: (lift_cell(g, start),))
                expected = {(r - 1, pos + 1): 1, (r - 1, pos): -1} if r % 2 else {}
                assert result == expected
                counts['signed cover boundaries'] += 1
        # Only a facet omitting the first coordinate contributes to this height.
        labelled = marked_boundary((EDGE,) * k)
        first_position = sum(weight * pos[0] for (active, pos), weight in labelled.items()
                             if active == tuple(range(1, k)))
        assert len(labelled) == 2 * k and first_position == 1
        counts['separately labelled height differences'] += 1
        counts['total tableaux and degenerations'] += 1
    check_contexts(counts)
    for label, count in counts.items():
        print(f'{count:,} {label}')


if __name__ == '__main__':
    check()
