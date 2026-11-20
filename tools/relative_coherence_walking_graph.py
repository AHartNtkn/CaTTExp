"""Build the walking presentation over a finite complete graph and check its contraction."""
from argparse import ArgumentParser
from collections import Counter
from dataclasses import dataclass
from functools import cache
from pathlib import Path

from catt import (STAR, arr, check_ctx, comp2, disc_tree, fv_ty, infer, src, sub_from,
                  subst_ty, tdim, tgt, tree_ctx, v)
from ct_suspension import ident
from emit_agda import Emitter
from relative_coherence_cut import top_counts


@dataclass
class Template:
    ctx: tuple
    old: int
    duplicate: int
    forward: int
    # Each pair gives an inverse and its higher, forward cancellation.
    inverse_pairs: list


@cache
def template(k, height):
    ctx = tree_ctx(disc_tree(k))
    old = len(ctx)-1
    duplicate = len(ctx)
    ctx += (ctx[old],)
    def declare(a, b):
        nonlocal ctx
        term = v(len(ctx))
        ctx += (arr(infer(ctx, a), a, b),)
        return term
    first = declare(v(old), v(duplicate))
    layer = [first]
    pairs = []
    for rank in range(k+1, height+1):
        next_layer = []
        for f in layer:
            s, t = src(ctx, f), tgt(ctx, f)
            left, right = declare(t, s), declare(t, s)
            if rank < height:
                for inv, a, b in ((left, f, left), (right, right, f)):
                    product = comp2(ctx, rank-1, a, b)
                    cell = declare(product, ident(ctx, src(ctx, product)))
                    pairs.append((inv[1], cell[1]))
                    next_layer.append(cell)
        layer = next_layer
    check_ctx(ctx)
    return Template(ctx, old, duplicate, first[1], pairs)


def signed(top, bottom):
    result = Counter(top)
    result.subtract(bottom)
    return Counter({i: n for i, n in result.items() if n})


def linear(images, chain):
    result = Counter()
    for i, coeff in chain.items():
        result.update({j: coeff*n for j, n in images[i].items()})
    return result


class WalkingGraph:
    def __init__(self, vertices, height):
        self.ctx = (STAR,)
        self.h = [Counter()]
        self.edges = {}
        self.attachments = Counter()
        self.points = [v(0)]
        self.carriers = [frozenset({0})]
        def attach(k, old, carrier):
            work = template(k, height)
            disk = work.ctx[:work.old+1]
            sigma = list(sub_from(disk, self.ctx, {work.old: old}))
            begin = len(self.ctx)
            types = []
            for ty in work.ctx[work.duplicate:]:
                types.append(subst_ty(ty, sigma))
                sigma.append(v(begin+len(types)-1))
            self.ctx += tuple(types)
            self.h.extend(Counter() for _ in types)
            self.carriers.extend([frozenset(carrier)]*len(types))
            g, a = sigma[work.duplicate], sigma[work.forward]
            self.h[g[1]] = linear(self.h, top_counts(self.ctx, old))
            self.h[g[1]][a[1]] += 1
            for inv, cancel in work.inverse_pairs:
                self.h[sigma[inv][1]] = Counter({sigma[cancel][1]: -1})
            self.attachments[k] += 1
            return g, a, sigma[work.forward+1]
        for i in range(1, vertices):
            g, f, b = attach(0, v(0), {0, i})
            self.points.append(g)
            self.edges[0, i], self.edges[i, 0] = f, b
        for i in range(vertices):
            for j in range(vertices):
                if (i, j) in self.edges:
                    continue
                anchor = (ident(self.ctx, self.points[i]) if i == j
                          else comp2(self.ctx, 0, self.edges[i, 0], self.edges[0, j]))
                g, _, _ = attach(1, anchor, {0, i, j})
                self.edges[i, j] = g

    def check(self, height):
        ranks = [tdim(ty)+1 for ty in self.ctx]
        boundary = [Counter() if ty == STAR else
                    signed(top_counts(self.ctx, ty[3]), top_counts(self.ctx, ty[2])) for ty in self.ctx]
        for i, rank in enumerate(ranks):
            if rank >= height:
                continue
            dh = linear(boundary, self.h[i])
            hd = linear(self.h, boundary[i])
            expected = Counter({i: 1})
            if not rank:
                expected[0] -= 1
            assert signed(expected, dh) == hd
        for i, ty in enumerate(self.ctx):
            assert all(self.carriers[j] <= self.carriers[i] for j in fv_ty(ty))
        for (i, j), edge in self.edges.items():
            assert infer(self.ctx, edge) == arr(STAR, self.points[i], self.points[j])
        for bits in range(1 << (len(self.points)-1)):
            names = {0} | {i for i in range(1, len(self.points)) if bits & (1 << (i-1))}
            local_edges = {(i, j) for (i, j), edge in self.edges.items() if self.carriers[edge[1]] <= names}
            assert local_edges == {(i, j) for i in names for j in names}
        print(f'Walking attachments: {dict(self.attachments)}; generators by rank: '
              f'{[ranks.count(r) for r in range(height+1)]}.')
        print(f'Checked {len(self.edges)} literal edge types and dh+hd on {sum(r < height for r in ranks)} generators.')


def certificates(output):
    emitter = Emitter()
    for k in (0, 1):
        work = template(k, 4)
        for i, (inverse, cancel) in enumerate(work.inverse_pairs):
            # Check the actual inverse and its cancellation, with their dependent faces.
            for tag, j in (('inv', inverse), ('cancel', cancel)):
                emitter.check_type(f'{tag}{k}case{i}', work.ctx[:j+1], v(j), work.ctx[j])
    output.write_text(emitter.module(output.stem, 'Independent inverse and cancellation declarations.'))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--vertices', type=int, default=7)
    parser.add_argument('--height', type=int, default=5)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    if args.height < 3 or args.vertices < 1:
        parser.error('expected height at least three and at least one vertex')
    WalkingGraph(args.vertices, args.height).check(args.height)
    if args.agda:
        certificates(args.agda)
