"""Check raw associativity word pairs and the nonempty-string charts for their model."""

from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import cache
from itertools import product
from random import Random

from catt import STAR, arr, check_ctx, comp2, infer, maximal_vars, tdim, tree_ctx, v
from partial_cylinder_steiner import trees
from relative_coherence_cut import outer_edge
from relative_coherence_hidden_seam import identity
from steiner import Complex


@cache
def arities(size):
    return tuple(trees(size))


@dataclass
class Cell:
    term: tuple
    faces: tuple


def string_cell(ctx, rank, faces, rng):
    if rank == 0:
        term = v(len(ctx))
        ctx.append(STAR)
        return Cell(term, ())
    source, target = faces
    seams = [source]
    for _ in range(rng.randrange(3)):
        seams.append(string_cell(ctx, rank - 1, source.faces, rng))
    seams.append(target)
    result = None
    for a, b in zip(seams, seams[1:]):
        current = tuple(ctx)
        base = infer(current, a.term)
        assert infer(current, b.term) == base
        bead = v(len(ctx))
        ctx.append(arr(base, a.term, b.term))
        result = bead if result is None else comp2(tuple(ctx), rank - 1, result, bead)
    return Cell(result, faces)


def check_columns(chart, poles, counts):
    exits = defaultdict(list)
    higher = defaultdict(list)
    for i, ty in enumerate(chart):
        if ty == STAR:
            continue
        s, t = outer_edge(ty)
        if ty[1] == STAR:
            exits[s].append((i, t))
        else:
            higher[s, t].append(i)
    blocks = list(zip(poles, poles[1:]))
    assert set(higher).issubset(blocks)
    for start, end in blocks:
        paths, private = {}, set()
        for edge, vertex in exits[start]:
            path = [edge]
            while vertex != end:
                assert vertex not in poles and vertex not in private
                private.add(vertex)
                (edge, vertex), = exits[vertex]
                path.append(edge)
            paths[tuple(path)] = v(len(paths))
        local = [STAR] * len(paths)
        image = {}

        def lower(t):
            if infer(chart, t)[1] == STAR:
                def edges(u):
                    if u[0] == 'v':
                        return (u[1],)
                    return tuple(i for j in maximal_vars(u[1]) for i in edges(u[3][j]))
                return paths[edges(t)]
            if t[0] == 'v':
                return image[t[1]]
            a, b = [lower(t[3][j]) for j in maximal_vars(t[1])]
            return comp2(tuple(local), tdim(infer(chart, t)) - 1, a, b)

        for i in higher[start, end]:
            a, b = map(lower, chart[i][2:])
            base = infer(tuple(local), a)
            assert infer(tuple(local), b) == base
            image[i] = v(len(local))
            local.append(arr(base, a, b))
        check_ctx(tuple(local))
        assert Complex(tuple(local)).is_strong_steiner()
        counts['typed strong Steiner column homs'] += 1


def check_charts(counts):
    rng = Random(48157)
    for size in range(1, 6):
        for shape in arities(size):
            for _ in range(2):
                arity = tree_ctx(shape)
                ctx, cells = [], []
                for ty in arity:
                    faces = () if ty == STAR else tuple(cells[t[1]] for t in ty[2:])
                    cells.append(string_cell(ctx, tdim(ty) + 1, faces, rng))
                chart = tuple(ctx)
                check_ctx(chart)
                check_columns(chart, [c.term[1] for c, ty in zip(cells, arity) if ty == STAR],
                              counts)
                complex_ = Complex(chart)
                assert complex_.is_strong_steiner()
                for i, ty in enumerate(chart):
                    if ty != STAR:
                        rows = complex_.atom(i)
                        assert rows[-2] == (complex_.dm[i], complex_.dp[i])
                        assert not set(dict(complex_.dm[i])).intersection(dict(complex_.dp[i]))
                counts['typed strong Steiner charts'] += 1
                counts['generators in charts'] += len(ctx)


def check_words(counts):
    # Hold inputs at their actual generic globular variables. Generate weak
    # identity and mixed-cut words and group by literal type and flattened tree.
    for shape in ( ((), (), ()), (((), (), ()),), (((),), ((),), ((),)),
                   (((), ()), ((), ())), ((((), ()),),), (((),), (), ((),)) ):
        ctx = tree_ctx(shape)
        words = defaultdict(dict)
        for i, ty in enumerate(ctx):
            raw = v(i)
            words[1][raw] = (('v', i), ('v', i))
        for size in range(2, 7):
            current = words[size]
            for raw, (full, top) in words[size - 1].items():
                if tdim(infer(ctx, raw)) < 2:
                    current[identity(ctx, raw)] = (('id', full), ('id', top))
            for lsize in range(1, size):
                for (l, lk), (r, rk) in product(words[lsize].items(), words[size - lsize].items()):
                    lt, rt = infer(ctx, l), infer(ctx, r)
                    ld, rd = tdim(lt) + 1, tdim(rt) + 1
                    for k in reversed(range(min(ld, rd))):
                        a, b = lt, rt
                        while tdim(a) > k:
                            a = a[1]
                        while tdim(b) > k:
                            b = b[1]
                        if a[3] != b[2]:
                            continue
                        term = comp2(ctx, k, l, r)
                        rank = max(ld, rd)
                        keys = []
                        for ix, merge in ((0, True), (1, k == rank - 1)):
                            tag = ('cut', k) if merge else ('binary', k)
                            children = []
                            for child in (lk[ix], rk[ix]):
                                if merge and child[0] == tag:
                                    children.extend(child[1])
                                else:
                                    children.append(child)
                            keys.append((tag, tuple(children)))
                        current[term] = tuple(keys)
            groups = defaultdict(set)
            by_tree = defaultdict(set)
            for term, (full, top) in current.items():
                groups[full, infer(ctx, term)].add(top)
                by_tree[full].add(top)
            assert all(len(values) == 1 for values in groups.values())
            counts['typed words grouped by full associativity and raw type'] += len(current)
            counts['words beyond one per group'] += len(current) - len(groups)
            counts['flattened groups separated by raw boundaries'] += sum(
                len(values) > 1 for values in by_tree.values())
    assert counts['flattened groups separated by raw boundaries'] > 0


if __name__ == '__main__':
    counts = Counter()
    check_charts(counts)
    check_words(counts)
    for label, count in counts.items():
        print(f'{count:,} {label}')
