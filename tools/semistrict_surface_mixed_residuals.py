"""Check which positive edges survive a simultaneous identity specialization."""
from argparse import ArgumentParser
from dataclasses import dataclass, replace
from functools import cache
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess

from catt import comp2, disc_tree, infer, maximal_vars, src, sub_from, subst_tm, subst_ty, tree_ctx, ucomp, v
from semistrict_surface_insertion_clusters import Node, component, frontier, joined_shape, reading
from semistrict_surface_insertion_cut import Assertions, variables
from semistrict_surface_lower_charts import identity


@dataclass(frozen=True)
class Operation:
    # A cut is the depth of the branching point between consecutive inputs.
    cuts: tuple
    children: tuple
    origins: frozenset


@cache
def binary_trees(start, end, rank):
    if end == start + 1:
        return (start,)
    return tuple(Operation((cut,), (left, right), frozenset({(start, end)}))
                 for mid in range(start + 1, end)
                 for left in binary_trees(start, mid, rank)
                 for right in binary_trees(mid, end, rank)
                 for cut in range(rank))


def internal_edges(node):
    for i, child in enumerate(node.children):
        if isinstance(child, Operation):
            branch = max(node.cuts[max(0, i - 1):i + 1])
            if branch <= min(child.cuts):
                yield next(iter(child.origins))
            yield from internal_edges(child)


def contract(node, join):
    if not isinstance(node, Operation):
        return node
    args, cuts, origins = [], [], node.origins
    for i, arg in enumerate(node.children):
        child = contract(arg, join)
        if i:
            cuts.append(node.cuts[i - 1])
        if isinstance(child, Operation) and join(node.origins, arg.origins):
            branch = max(node.cuts[max(0, i - 1):i + 1])
            assert branch <= min(child.cuts)
            args.extend(child.children)
            cuts.extend(child.cuts)
            origins = origins | child.origins
        else:
            args.append(child)
    return Operation(tuple(cuts), tuple(args), origins)


def restrict(node, live):
    if not isinstance(node, Operation):
        return node if node is not None and (1 << node) & live else None
    children = [(i, child) for i, arg in enumerate(node.children)
                if (child := restrict(arg, live)) is not None]
    if not children:
        return None
    if len(children) == 1:
        return children[0][1]
    cuts = tuple(min(node.cuts[i:j]) for (i, _), (j, _) in zip(children, children[1:]))
    return Operation(cuts, tuple(child for _, child in children), node.origins)


def vertices(node):
    if isinstance(node, Operation):
        yield node
        for child in node.children:
            yield from vertices(child)


def keep_marks(node, kept):
    if not isinstance(node, Operation):
        return node
    return replace(node, origins=node.origins & kept,
                   children=tuple(keep_marks(child, kept) for child in node.children))


def check_partitions():
    tests = transmitted = 0
    for tree in binary_trees(0, 4, 3):
        edges = tuple(internal_edges(tree))
        for mask in product((False, True), repeat=len(edges)):
            marked = {edge for edge, take in zip(edges, mask) if take}
            merged = contract(tree, lambda _parent, child: child <= marked)
            blocks = [node.origins for node in vertices(merged)]
            for live in range(16):
                before = restrict(tree, live)
                kept = frozenset().union(*(v.origins for v in vertices(before)))
                predicted = contract(before, lambda x, y: any(x | y <= block for block in blocks))
                after = restrict(merged, live)
                assert predicted == keep_marks(after, kept)
                for node in vertices(predicted):
                    if len(node.origins) > 1 and any(node.origins < block for block in blocks):
                        transmitted += 1
                tests += 1
    assert transmitted
    print(f'{tests} marked specializations, including {transmitted} merges across or with a collapsed vertex.')


def named_reading(node, mask, rank, ctx, args):
    if not isinstance(node, Node):
        return args[node]
    parts = []
    pattern = component(node, mask, parts)
    arity = tree_ctx(joined_shape(pattern, rank))
    slots = maximal_vars(arity)
    prototype = reading(arity, pattern, dict(zip(frontier(pattern), map(v, slots), strict=True)))
    labels = [named_reading(part, mask, rank, ctx, args) for part in parts]
    return ('coh', arity, infer(arity, prototype),
            sub_from(arity, ctx, dict(zip(slots, labels, strict=True))))


def requires_insertion(assertions, binary):
    with TemporaryDirectory() as directory:
        file = Path(directory) / 'remaining.catt'
        file.write_text('\n'.join(assertions.commands) + '\n')
        result = subprocess.run([binary, '--su', file], capture_output=True, text=True)
    assert 'not equal' in (result.stdout + result.stderr).lower(), result


def check_chain(rank, binary):
    tree = Node(0, 0, Node(1, 1, Node(rank - 1, 2, 3, 2), 1))
    smaller = Node(0, 0, Node(rank - 1, 2, 3, 2))
    generic = tree_ctx(joined_shape(tree, rank))
    residual = tree_ctx(joined_shape(smaller, rank))
    args = dict(zip(frontier(smaller), map(v, maximal_vars(residual)), strict=True))
    pole = args[2]
    for _ in range(rank - 1):
        pole = src(residual, pole)
    for dim in range(1, rank):
        pole = identity(residual, pole, dim)
    change = sub_from(generic, residual,
                      dict(zip(maximal_vars(generic), (args[0], pole, args[2], args[3]), strict=True)))
    generic_args = dict(zip(frontier(tree), map(v, maximal_vars(generic)), strict=True))
    separate = named_reading(smaller, 0, rank, residual, args)
    merged = named_reading(smaller, 2, rank, residual, args)
    unit, full = Assertions(), Assertions()
    for mask in range(4):
        term = subst_tm(named_reading(tree, mask, rank, generic, generic_args), change)
        unit.equal(residual, term, merged if mask == 3 else separate, 'unit-normal residuals')
    full.equal(residual, separate, merged, 'surviving positive contraction')
    unit.run(binary, '--su')
    full.run(binary)
    # The positive rule really is needed on the residual edge.
    requires_insertion(full, binary)
    print(f'Rank {rank}: either first contraction disappears, the two-edge contraction survives.')


def check_exposed_chart(rank, binary):
    lower, upper = disc_tree(rank - 2), disc_tree(rank - 1)
    coarse, fine = tree_ctx((lower, upper)), tree_ctx((lower, lower, upper))
    a, b, z = map(v, maximal_vars(fine))
    pole = comp2(fine, 0, a, b)
    exterior = sub_from(coarse, fine, dict(zip(maximal_vars(coarse), (pole, z), strict=True)))
    generic = ucomp(coarse)
    early = subst_tm(generic, exterior)
    late = ('coh', fine, subst_ty(infer(coarse, generic), exterior), variables(fine))
    upper_reading = comp2(fine, 0, comp2(fine, 0, identity(fine, a, rank - 1), b), z)
    unit, full = Assertions(), Assertions()
    unit.equal(fine, upper_reading, early, 'prunings to the compound lower slot')
    full.equal(fine, early, late, 'exteriors to the refined chart')
    unit.run(binary, '--su')
    full.run(binary)
    requires_insertion(full, binary)


if __name__ == '__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('catt_strict', type=Path)
    binary = p.parse_args().catt_strict.resolve()
    check_partitions()
    for rank in (3, 4):
        check_chain(rank, binary)
        check_exposed_chart(rank, binary)
