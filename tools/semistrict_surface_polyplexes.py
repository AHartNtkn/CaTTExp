"""Compare coloured lifts of planar rewrite histories with their port constraints."""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, comp2, glue_tree, infer, maximal_vars, sub_from, subst_tm, subst_ty, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, rejected, run


# A consumes two wires and produces two. D consumes one and produces none.
# Distinct declarations may have precisely the same attaching terms.
RULES = {
    'A': [(pair, pair[::-1]) for pair in product((0, 1), repeat=2)]
         + [((1, 1), (0, 0)), ((0, 0), (0, 0))],
    'D': [((0,), ()), ((0,), ())],
}
INPUTS = tuple(('input', i) for i in range(3))


def outputs(node):
    return tuple(('out', node, i) for i in range(2 if node[0] == 'A' else 0))


def readings():
    def visit(wires, history):
        yield history
        if len(history) == 3:
            return
        for kind, width in [('A', 2), ('D', 1)]:
            for offset in range(len(wires) - width + 1):
                node = (kind, wires[offset:offset + width])
                new_wires = wires[:offset] + outputs(node) + wires[offset + width:]
                yield from visit(new_wires, history + (node,))
    return visit(INPUTS, ())


def factor_lifts(history, initial):
    """Lift factors consecutively at their current inputs."""
    def advance(i, colours, labels):
        if i == len(history):
            yield frozenset(labels)
            return
        node = history[i]
        pattern = tuple(colours[w] for w in node[1])
        for j, (src, tgt) in enumerate(RULES[node[0]]):
            if src == pattern:
                yield from advance(i + 1, colours | dict(zip(outputs(node), tgt)), labels + [(node, j)])
    return set(advance(0, dict(zip(INPUTS, initial)), []))


def diagram_lifts(nodes, initial):
    """Choose all vertex labels first, then impose every wire equation simultaneously."""
    result = set()
    for choices in product(*(range(len(RULES[node[0]])) for node in nodes)):
        ends = defaultdict(set)
        for wire, colour in zip(INPUTS, initial):
            ends[wire].add(colour)
        for node, j in zip(nodes, choices):
            src, tgt = RULES[node[0]][j]
            for wire, colour in (*zip(node[1], src), *zip(outputs(node), tgt)):
                ends[wire].add(colour)
        if all(len(colours) == 1 for colours in ends.values()):
            result.add(frozenset(zip(nodes, choices)))
    return result


def check_diagrams():
    groups = defaultdict(list)
    for history in readings():
        assert len(set(history)) == len(history)
        groups[frozenset(history)].append(history)
    total = empty = multiple = 0
    for nodes, histories in groups.items():
        for initial in product((0, 1), repeat=len(INPUTS)):
            solutions = diagram_lifts(tuple(nodes), initial)
            for history in histories:
                assert factor_lifts(history, initial) == solutions
                total += 1
            empty += not solutions
            multiple += len(solutions) > 1
    exchanged = sum(len(group) > 1 for group in groups.values())
    assert exchanged and empty and multiple
    print(f'{total} factor lifts compared across {len(groups)} diagrams, including {exchanged} with several readings.')
    print(f'{empty} diagram/colour choices had empty fibres and {multiple} had multiple lifts.')


def crossing(ctx, left, right):
    arity = tree_ctx(glue_tree(2, 0, 2))
    i, j = maximal_vars(arity)
    a, b = v(i), v(j)
    f, g = infer(arity, a)[2:]
    h, k = infer(arity, b)[2:]
    ab = comp2(arity, 1, comp2(arity, 0, a, h), comp2(arity, 0, g, b))
    ba = comp2(arity, 1, comp2(arity, 0, f, b), comp2(arity, 0, a, k))
    change = head(arity, ba, ab)
    return subst_tm(change, sub_from(arity, ctx, {i: left, j: right}))


def check_terms(emitter):
    x, f = v(0), v(1)
    arrow = arr(STAR, x, x)
    ctx = (STAR, arrow)
    ff = comp2(ctx, 0, f, f)
    unit = identity(ctx, x)
    ctx += (arr(arrow, ff, ff), arr(arrow, f, unit))
    base = comp2(ctx, 1, v(2), crossing(ctx, v(3), v(3)))

    coloured = (STAR, arrow, arrow)
    f0, f1 = v(1), v(2)
    pair0, pair1 = (comp2(coloured, 0, w, w) for w in (f0, f1))
    end = arr(arrow, f0, unit)
    coloured += (arr(arrow, pair1, pair0), end, end)
    fold = (x, f, f, v(2), v(3), v(3))
    for i, ty in enumerate(coloured):
        assert infer(ctx, fold[i]) == subst_ty(ty, fold[:i])
    lifts = []
    for i, j in product((4, 5), repeat=2):
        lifted = comp2(coloured, 1, v(3), crossing(coloured, v(i), v(j)))
        assert subst_tm(lifted, fold) == base
        def route(first, second):
            return comp2(coloured, 1, v(3), comp2(coloured, 1, first, second))

        source = route(comp2(coloured, 0, f0, v(j)), comp2(coloured, 0, v(i), unit))
        target = route(comp2(coloured, 0, v(i), f0), comp2(coloured, 0, unit, v(j)))
        expected = arr(arr(arrow, pair1, comp2(coloured, 0, unit, unit)), source, target)
        assert infer(coloured, lifted) == expected
        emitter.check_type(f'cross{i}{j}', coloured, lifted, expected)
        emitter.check_eq(f'fold{i}{j}', lifted, fold, base)
        lifts.append(lifted)
    assert len(set(lifts)) == 4
    # The source and target have different event orders but both use the
    # same marked contraction at the same input port.
    assert all(infer(coloured, term)[2] != infer(coloured, term)[3] for term in lifts)


def check_published(checkout):
    binary = checkout / 'target/release/catt_strict'
    ctx = ('(x : *) (f : x -> x) (g : x -> x) (a : comp[f,f] -> comp[g,g]) '
           '(b : g -> id(x)) (c : g -> id(x))')
    path = 'reading(x,f,g,a,b,c)'
    with TemporaryDirectory() as directory:
        root = Path(directory)
        (root / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        (root / 'Raw.catt').write_text(f"""import examples/eh-common
def reading {ctx} : comp[f,f] -> comp[id(x),id(x)] = comp[a,swap_tgt(b,c)]
def fitted {ctx} : {path} -> comp[{path},id(comp[id(x),id(x)])] = unitor_r_inv({path})
""")
        (root / 'Padded.catt').write_text(
            f'import Raw\ndef exact {ctx} : {path} -> comp[{path},id(comp[id(x),id(x)])] = id({path})\n')
        (root / 'Wrong.catt').write_text(
            f'import Raw\ndef wrong {ctx} : {path} -> reading(x,f,g,a,c,b) = id({path})\n')
        for flags in ([], ['--su'], ['--sua']):
            accepted(run(binary, root, 'Raw.catt', flags), 'Raw.catt', ['reading', 'fitted'])
            rejected(run(binary, root, 'Wrong.catt', flags), 'Wrong.catt', 'wrong')
            checked = run(binary, root, 'Padded.catt', flags)
            if flags:
                accepted(checked, 'Padded.catt', ['exact'])
            else:
                rejected(checked, 'Padded.catt', 'exact')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    check_diagrams()
    emitter = Emitter()
    check_terms(emitter)
    if args.agda_dir:
        for prefix, kernel in [('Ordinary', 'CaTTExp.Pure'), ('Gray', 'CaTTExp.Gray.Pure')]:
            name = prefix + 'PolyplexLifts'
            code = emitter.module(name, __doc__).replace('open import CaTTExp.Pure', 'open import ' + kernel)
            (args.agda_dir / (name + '.agda')).write_text(code)
    print('Checked four raw crossing lifts through a composite-boundary rule and their fold equations.')
    check_published(args.checkout.resolve())
    print('Checked padding and incompatible occurrences in all three Rice modes.')
