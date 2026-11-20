"""Locate low-dimensional star attachments and check a stationary depth-one replacement."""
from argparse import ArgumentParser
from functools import reduce
from itertools import product
from pathlib import Path

from catt import arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_based_columns import Brackets
from relative_coherence_hidden_seam import identity


def first_ranks():
    for stage in range(2, 7):
        marked = set(range(1, stage))
        facet = set(range(7)) - {stage}
        vertices = [x for x in sorted(facet) if not marked <= {x}]
        old_edges = {(x, y) for x, y in product(vertices, repeat=2) if not marked <= {x, y}}
        new_edges = set(product(vertices, repeat=2)) - old_edges
        assert len(facet - set(vertices)) == (stage == 2)
        assert len(new_edges) == (2 if stage == 3 else 0)
        if not marked <= set(vertices):
            assert stage == 2
            continue
        for length in range(1, 6):
            examples = [w for w in product(vertices, repeat=length)
                        if marked <= set(w) and all(edge in old_edges for edge in zip(w, w[1:] + w[:1]))]
            if examples:
                break
        assert examples and length == {3: 4, 4: 3, 5: 4, 6: 5}[stage]
        print(f'Stage {stage}: {len(new_edges)} new directed edges, '
              f'minimal total length of a new two-bracket boundary {length}.')


def stationary(file):
    p = Brackets(7)
    def tour(stops):
        path = [0, *stops, 0]
        edges = [p.bracket(v(a), v(b)) for a, b in zip(path, path[1:])]
        return reduce(lambda x, y: comp2(p.ctx, 0, x, y), edges)

    w = tour((1, 2, 3))
    x = identity(p.ctx, w)
    old = identity(p.ctx, x)
    fresh = p.bracket(x, x)
    left, right = p.bracket(old, fresh), p.bracket(fresh, old)
    u = comp2(p.ctx, 3, left, right)
    unit = identity(p.ctx, old)
    restored = comp2(p.ctx, 3, unit, unit)
    down, up = p.bracket(u, restored), p.bracket(restored, u)

    other = tour((4, 5, 6))
    pole = identity(p.ctx, identity(p.ctx, other))
    loop = p.bracket(pole, pole)
    ctx = p.ctx
    check_ctx(ctx)
    emitter = Emitter()
    for power in (0, 1, 3, 7):
        b = identity(ctx, pole) if power == 0 else reduce(lambda y, z: comp2(ctx, 3, y, z), [loop] * power)
        a, c = (comp2(ctx, 0, t, b) for t in (u, restored))
        for name, term, s, t in (('retract', down, a, c), ('expand', up, c, a)):
            q = comp2(ctx, 0, term, b)
            expected = arr(infer(ctx, s), s, t)
            assert infer(ctx, q) == expected
            if file:
                emitter.check_type(name + str(power), ctx, q, expected)
    if file:
        file.write_text(emitter.module(file.stem, 'Stationary high-rank replacement with an external loop.'))
    print('Rank-three replacement and reverse across an external four-loop at powers 0, 1, 3 and 7.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    first_ranks()
    stationary(args.agda)
