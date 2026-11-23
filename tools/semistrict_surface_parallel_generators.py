"""Check finite state copies for parallel generators, including simultaneous uses and higher faces."""
from argparse import ArgumentParser
from itertools import combinations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, comp2, coh_between, disc_tree, infer, subst_tm, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_scalar_cube import exchange


def check_rectangle_criterion():
    # Compute all old-to-old reachabilities after replacing a family of arcs.
    # The predicted test concerns the original reachability relation, not just
    # the existence of a generating arc between each of the chosen endpoints.
    vertices = tuple(range(3))
    edges = [(a, b) for a in vertices for b in vertices if a != b]
    subsets = [s for n in (1, 2, 3) for s in combinations(vertices, n)]

    def closure(size, arcs):
        result = set(arcs) | {(i, i) for i in range(size)}
        for k in range(size):
            result |= {(i, j) for i in range(size) for j in range(size)
                       if (i, k) in result and (k, j) in result}
        return result

    checks = 0
    for chosen in product((False, True), repeat=len(edges)):
        arcs = {edge for edge, keep in zip(edges, chosen) if keep}
        old = closure(3, arcs)
        for sources, targets in product(subsets, repeat=2):
            rectangle = set(product(sources, targets))
            new = arcs - rectangle | {(u, 3) for u in sources} | {(3, v) for v in targets} | {(3, 3)}
            restricted = closure(4, new) & set(product(vertices, repeat=2))
            assert (restricted == old) == (rectangle <= old)
            checks += 1
    return checks


def check_interleavings():
    # Keep the old region at each position while independently selecting a
    # label. Extra ticks saturate. A slot may be read before its neighbour.
    runs = 0
    distinct = 0
    for ticks in product(range(4), repeat=2):
        programs = [('enter',) + ('tick',) * n + ('leave',) for n in ticks]
        total = sum(map(len, programs))
        for left in combinations(range(total), len(programs[0])):
            state = [None, None]
            pc = [0, 0]
            outputs = {}
            for time in range(total):
                i = int(time not in left)
                op = programs[i][pc[i]]
                pc[i] += 1
                if op == 'enter':
                    assert state[i] is None
                    state[i] = (i, 0)
                elif op == 'tick':
                    src, phase = state[i]
                    state[i] = (src, min(phase + 1, 2))
                else:
                    src, phase = state[i]
                    outputs[i] = (src, 1 - i, phase)
                    state[i] = None
            assert state == [None, None]
            assert outputs == {i: (i, 1 - i, min(ticks[i], 2)) for i in range(2)}
            runs += 1
            distinct += outputs[0][-1] != outputs[1][-1]
    return runs, distinct


def globe_checks(directory):
    emitter = Emitter()
    for r in (2, 3, 4):
        tree = disc_tree(r)
        disc = tree_ctx(tree)
        original = v(len(disc) - 1)
        source = disc[-1][2]
        idle = identity(disc, source)
        for j in range(3):
            prefix = idle
            for _ in range(j):
                prefix = comp2(disc, r - 1, prefix, idle)
            value = comp2(disc, r - 1, prefix, original)
            assert value != original and infer(disc, value) == disc[-1]
            for tag, a, b in (('to', value, original), ('from', original, value)):
                t = coh_between(disc, tree, [original], a, b)
                ty = arr(disc[-1], a, b)
                assert infer(disc, t) == ty
                emitter.check_type(f'{tag}{r}state{j}', disc, t, ty)
    # Both copies of the closing project to the same declaration. Their state
    # indices select different scalars even across a directed exchange head.
    point = (STAR,)
    x = v(0)
    path_type = arr(STAR, x, x)
    unit = identity(point, x)
    old = point + (arr(path_type, unit, unit),) * 2
    encoded = point + (path_type, arr(path_type, v(1), unit))
    copies = point + (path_type, path_type, arr(path_type, v(1), unit), arr(path_type, v(2), unit))
    square = exchange(copies, v(3), v(4))
    fold = (x, v(1), v(1), v(2), v(2))
    decode = (x, unit, unit, v(1), v(2))
    same_closing = exchange(encoded, v(2), v(2))
    different_scalars = exchange(old, v(1), v(2))
    for label, target, mapping, expected in (
        ('foldSquare', encoded, fold, same_closing),
        ('readSquare', old, decode, different_scalars),
    ):
        assert subst_tm(square, mapping) == expected
        emitter.check_eq(label, square, mapping, expected)
        emitter.check_type(label, target, expected, infer(target, expected))
    emitter.check_type('copiedSquare', copies, square, infer(copies, square))
    for prefix, kernel in (('Ordinary', 'CaTTExp.Pure'), ('Gray', 'CaTTExp.Gray.Pure')):
        name = prefix + 'ParallelGeneratorFits'
        data = emitter.module(name, __doc__).replace('open import CaTTExp.Pure', 'open import ' + kernel)
        (directory / (name + '.agda')).write_text(data)


def program(enter, count, leave):
    term = enter
    for _ in range(count):
        term = f'comp[{term},tick]'
    return f'comp[{term},{leave}]'


def check_rice(checkout):
    exe = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as path:
        folder = Path(path)
        # Composite inputs and outputs, with two states per selected source.
        ctx = '(x : *) (f : x -> x) (g : x -> x) (h : x -> x)'
        ctx += ' (b : comp[f,g] -> h) (c : comp[g,f] -> h) (tick : h -> h)'
        ctx += ' (d : h -> comp[f,f]) (e : h -> comp[g,g])'
        names = []
        text = ''
        for enter, source in [('b', 'comp[f,g]'), ('c', 'comp[g,f]')]:
            for leave, target in [('d', 'comp[f,f]'), ('e', 'comp[g,g]')]:
                for i in range(3):
                    name = f'word{enter}{i}{leave}'
                    text += f'def {name} {ctx} : {source} -> {target} = {program(enter,i,leave)}\n'
                    names.append(name)
        a, b = program('b', 0, 'd'), program('b', 2, 'd')
        ctx += f' (z : {a} -> {b}) (w : {b} -> {a})'
        zig = 'comp[z,w]'
        ctx += f' (theta : {zig} -> id({a}))'
        text += f'def pasted {ctx} : {a} -> {a} = {zig}\n'
        text += f'def upper {ctx} : {zig} -> id({a}) = comp[theta,id(id({a}))]\n'
        names.extend(('pasted', 'upper'))
        (folder / 'Rectangle.catt').write_text(text)
        (folder / 'Wrong.catt').write_text(f'def wrong {ctx} : {a} -> {b} = {zig}\n')
        for mode in ([], ['--su'], ['--sua']):
            accepted(run(exe, folder, 'Rectangle.catt', mode), 'Rectangle.catt', names)
            rejected(run(exe, folder, 'Wrong.catt', mode), 'Wrong.catt', 'wrong')
    return len(names)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    parser.add_argument('--catt-strict', type=Path)
    options = parser.parse_args()
    print('Rectangle tests:', check_rectangle_criterion())
    print('Two-slot executions, including distinct selections:', *check_interleavings())
    if options.agda_dir:
        globe_checks(options.agda_dir)
    if options.catt_strict:
        print('Declarations in each Rice mode:', check_rice(options.catt_strict.resolve()))
