"""Check temporal-arity factorizations, free-category nerves, and a fitted old 5-cell."""
import argparse
from collections import Counter
from functools import cache
from itertools import combinations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, comp2, disc_tree, glue_tree, infer, maximal_vars, src, sub_from,
                  subst_tm, tdim, tree_ctx, v)
from catt_unit_ordered_exchange import temporal_words
from ct_suspension import ident
from emit_agda import Emitter
from partial_cylinder_steiner import trees
from relative_coherence_exchange_faces import head, string_tree
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_insertion_cut import Assertions
from semistrict_surface_peak_sections import columns, prune


def temporal(tree):
    while len(tree) == 1:
        tree = tree[0]
    return all(not child for child in tree)


def target_cells(rank, width, max_rank):
    """Actual hom table of the suspended ordinal, with identity padding."""
    ctx = tree_ctx(string_tree(rank-1, [rank]*width))
    cells = [[] for _ in range(max_rank+1)]
    faces = {}
    for pos, ty in enumerate(ctx):
        dim = tdim(ty)+1
        if dim > max_rank:
            continue
        cell = ('v', pos)
        cells[dim].append(cell)
        if dim:
            faces[cell] = ty[2], ty[3]
    if rank <= max_rank:
        edges = [v(i) for i in maximal_vars(ctx)]
        for i in range(width):
            for j in range(i+2, width+1):
                cell = ('path', i, j)
                cells[rank].append(cell)
                faces[cell] = faces[edges[i]][0], faces[edges[j-1]][1]
    for dim in range(1, max_rank+1):
        for cell in cells[dim-1]:
            identity = ('id', cell)
            cells[dim].append(identity)
            faces[identity] = cell, cell
    return cells, faces


def assignments(ctx, cells, faces):
    def visit(values):
        if len(values) == len(ctx):
            yield values
            return
        ty = ctx[len(values)]
        for label in cells[tdim(ty)+1]:
            if ty == STAR or faces[label] == (values[ty[2][1]], values[ty[3][1]]):
                yield from visit((*values, label))
    return visit(())


@cache
def deletions(tree):
    ctx = tree_ctx(tree)
    for_step = []
    for address, (peak, end) in columns(tree).items():
        if end != peak+1:
            continue
        kept = tuple(j for j in range(len(ctx)) if j not in (peak-1, peak))
        source = kept.index(ctx[peak][2][1])
        projection = tuple((source, int(j == peak)) if j in (peak-1, peak)
                           else (kept.index(j), 0) for j in range(len(ctx)))
        for_step.append((peak, prune(tree, address), kept, projection))
    return for_step


@cache
def normal(tree, labels):
    """Join every legal first deletion, comparing all original variable images."""
    result = None
    for peak, smaller, kept, quotient in deletions(tree):
        if labels[peak][0] != 'id':
            continue
        residual, restriction, after = normal(smaller, tuple(labels[i] for i in kept))
        composite = tuple((after[i][0], after[i][1]+pad) for i, pad in quotient)
        candidate = residual, restriction, composite
        if result is not None and result != candidate:
            raise AssertionError((tree, labels, result, candidate))
        result = candidate
    if result is None:
        assert temporal(tree)
        result = tree, labels, tuple((i, 0) for i in range(len(labels)))
    return result


def check_factorizations(edges):
    counts = Counter()
    for rank, width in product(range(1, 4), range(1, 4)):
        cells, faces = target_cells(rank, width, edges)
        for size in range(edges+1):
            for tree in trees(size):
                for labels in assignments(tree_ctx(tree), cells, faces):
                    residual, restriction, projection = normal(tree, labels)
                    for label, (i, height) in zip(labels, projection, strict=True):
                        value = restriction[i]
                        for _ in range(height):
                            value = ('id', value)
                        assert label == value
                    counts['maps'] += 1
                    counts['non-temporal sources'] += not temporal(tree)
                    counts['multiple first deletions'] += sum(
                        labels[i][0] == 'id' for i, *_ in deletions(tree)) > 1
        normal.cache_clear()
    print(dict(counts), flush=True)


def check_words(bound):
    # A loop, two parallel forward edges and a return. Vertices and edges can recur.
    graph = ((0,0), (0,1), (0,1), (1,0))
    paths = {1: [(i,) for i in range(len(graph))]}
    for n in range(2, bound+1):
        paths[n] = [(*word, i) for word in paths[n-1] for i, ends in enumerate(graph)
                    if graph[word[-1]][1] == ends[0]]
    attached = set()
    for n, words in paths.items():
        for word in words:
            for k in range(n):
                for cuts in combinations(range(1, n), k):
                    positions = (0, *cuts, n)
                    simplex = tuple(word[i:j] for i, j in zip(positions, positions[1:]))
                    assert simplex not in attached
                    attached.add(simplex)
                    for outer in (simplex[:-1], simplex[1:]):
                        assert not outer or outer in attached
    # Separate enumeration of the nerve by adding any composable nonempty path.
    def visit(last, budget, reading):
        for length in range(1, budget+1):
            for word in paths[length]:
                if last is None or graph[word[0]][0] == last:
                    new = (*reading, word)
                    yield new
                    yield from visit(graph[word[-1]][1], budget-length, new)
    assert attached == set(visit(None, bound, ()))
    print(f'{len(attached)} distinct nondegenerate simplices of the free category', flush=True)


def rank_mod_three(rows):
    pivots = {}
    for row in rows:
        while row:
            col = min(row)
            factor = row[col]
            if col not in pivots:
                pivots[col] = {j: (v*factor) % 3 for j, v in row.items()}
                break
            for j, v in pivots[col].items():
                row[j] = (row.get(j, 0)-factor*v) % 3
                if not row[j]:
                    del row[j]
    return len(pivots)


def check_local_system():
    # The two-element group acts by sign on the one-object groupoid B(Z/3).
    # Along a face flag use the first vertex as anchor. Strictly compatible
    # 1-arrows on flags are precisely the twisted cocycles below.
    cases = 0
    for dim in range(1, 5):
        whole = (1 << (dim+1))-1
        faces = range(1, whole+1)
        flags = [(a, b) for a in faces for b in faces if b != a and a & b == b]
        index = {flag: i for i, flag in enumerate(flags)}
        def equations(vertices):
            for a, b in flags:
                if a not in vertices or b not in vertices:
                    continue
                for c in vertices:
                    if (b,c) in index:
                        j = (b & -b).bit_length()-1
                        k = (c & -c).bit_length()-1
                        transport = 1 if (j-k) % 2 == 0 else 2
                        yield {index[a,c]: 1, index[b,c]: 2, index[a,b]: 3-transport}
        all_rank = rank_mod_three(equations(faces))
        for omitted in range(dim+1):
            horn = set(faces) - {whole, whole ^ (1 << omitted)}
            coords = [i for (a, b), i in index.items() if a in horn and b in horn]
            target_dimension = len(coords) - rank_mod_three(equations(horn))
            with_zero_restriction = rank_mod_three([
                *equations(faces), *({i: 1} for i in coords)])
            assert with_zero_restriction - all_rank == target_dimension
            cases += 1
    print(f'All {cases} horn restriction maps surject on twisted flag cocycles', flush=True)


def mixed_boundary(rice, agda_dir):
    rank = 3
    triple = tree_ctx(string_tree(rank-1, [rank]*3))
    a, b, c = map(v, maximal_vars(triple))
    left = comp2(triple, 2, comp2(triple, 2, a, b), c)
    right = comp2(triple, 2, a, comp2(triple, 2, b, c))
    loop = comp2(triple, 3, head(triple, left, right), head(triple, right, left))
    contract = head(triple, loop, ident(triple, left))
    point = (STAR,)
    scalar = point + (infer(point, ident(point, ident(point, v(0)))),)
    twice = comp2(scalar, 1, v(1), v(1))
    ctx = scalar + (arr(infer(scalar, twice), twice, twice),)
    scalar_case = (ctx, [v(2)]*3)
    square = tree_ctx(glue_tree(2, 0, 2))
    early, late = temporal_words(square, *map(v, maximal_vars(square)), 0, 1)
    native = head(square, late, early)
    before, after = v(len(square)), v(len(square)+1)
    extended = square + (arr(infer(square, late), late, late), arr(infer(square, early), early, early))
    cases = {}
    emit = Emitter()
    for name, (base, operands) in [('scalar', scalar_case), ('directed', (extended, [before, native, after]))]:
        sigma = sub_from(triple, base, dict(zip(maximal_vars(triple), operands, strict=True)))
        old_face = subst_tm(left, sigma)
        ctx = base + (arr(infer(base, old_face), old_face, old_face),)
        k, z = v(len(base)), v(len(ctx))
        ctx += (arr(infer(ctx, k), k, k),)
        w = comp2(ctx, 3, subst_tm(loop, sigma), k)
        correction = comp2(ctx, 3, subst_tm(contract, sigma), k)
        disk = tree_ctx(disc_tree(4))
        top = v(maximal_vars(disk)[0])
        unitor = head(disk, comp2(disk, 3, ident(disk, src(disk, top)), top), top)
        instantiated = subst_tm(unitor, sub_from(disk, ctx, {top[1]: k}))
        witness = comp2(ctx, 4, comp2(ctx, 4, correction, instantiated), z)
        expected = arr(infer(ctx, k), w, k)
        assert infer(ctx, witness) == expected
        emit.check_type(name, ctx, witness, expected)
        cases[name] = ctx, z, witness, expected
    if agda_dir:
        agda_dir.mkdir(parents=True, exist_ok=True)
        for module, kernel in [('OrdinaryTemporalLift', 'CaTTExp.Pure'),
                               ('GrayTemporalLift', 'CaTTExp.Gray.Pure')]:
            if module == 'GrayTemporalLift':
                reverse = head(square, early, late)
                emit.checks.append(f'reverse-test : infer {emit.ctx(square)} {emit.tm(reverse)} ≡ nothing\n'
                                   'reverse-test = refl\n')
            body = emit.module(module, __doc__).replace('open import CaTTExp.Pure', 'open import '+kernel)
            (agda_dir/(module+'.agda')).write_text(body)
    if rice:
        for ctx, z, witness, expected in cases.values():
            writer = Assertions()
            def show(ty):
                return '*' if ty == STAR else ' -> '.join(map(writer.term, ty[2:]))
            declarations = ' '.join(f'(x{i} : {show(ty)})' for i, ty in enumerate(ctx))
            binary = rice.resolve()
            with TemporaryDirectory() as tmp:
                work = Path(tmp)
                for name, term in [('direct', z), ('fitted', witness)]:
                    cmd = f'def {name} {declarations} : {show(expected)} = {writer.term(term)}'
                    file = name+'.catt'
                    (work/file).write_text('\n'.join([*writer.commands, cmd, '']))
                    for flags in ([], ['--su'], ['--top-assoc-from','3'], ['--top-assoc-from','4']):
                        answer = run(binary, work, file, flags)
                        if name == 'fitted' or flags == ['--top-assoc-from','3']:
                            accepted(answer, file, [name])
                        else:
                            rejected(answer, file, name)
    print('Verified scalar and directed degree-five boundaries and their fitted witnesses', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--edges', type=int, default=5)
    parser.add_argument('--rice-binary', type=Path)
    parser.add_argument('--agda-dir', type=Path)
    options = parser.parse_args()
    check_factorizations(options.edges)
    check_words(6)
    check_local_system()
    mixed_boundary(options.rice_binary, options.agda_dir)
