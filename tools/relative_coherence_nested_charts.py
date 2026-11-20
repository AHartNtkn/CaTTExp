"""Find common raw terms in recursively labelled charts by overlaying their top slots."""
from argparse import ArgumentParser
from collections import defaultdict
from dataclasses import dataclass
from functools import cache
from itertools import combinations, product
from pathlib import Path

from catt import (TypeError_, STAR, arr, check_ctx, comp2, disc_tree, fv_tm, fv_ty,
                  infer, maximal_vars, sub_from, subst_tm, subst_ty, tdim, tgt,
                  tree_ctx, ucomp, v)
from ct_suspension import ident
from emit_agda import Emitter
from gray_globe_branch_comparisons import cylinder
from relative_coherence_chart_joins import globular_trees, readings
from relative_coherence_exchange_faces import head, string_tree
from relative_coherence_intermediates import Chart, charts, fill_chart, position_order, shape, terms_of_rank


@dataclass(frozen=True)
class Port:
    key: object


@dataclass(frozen=True)
class Node:
    arity: tuple
    ty: tuple
    labels: tuple  # A nonterminal at each slot of the output rank.

    @property
    def lower(self):
        return tuple(None if isinstance(x, Port) else x for x in self.labels)

    @property
    def slots(self):
        return tuple(j for j, x in enumerate(self.labels) if isinstance(x, Port))


@dataclass(frozen=True)
class Parse:
    node: Node
    writing: tuple
    children: tuple

    def chart(self):
        args = list(self.node.lower)
        for j, p in zip(self.node.slots, self.children, strict=True):
            args[j] = p.evaluate()
        return Chart(self.node.arity, self.writing, tuple(args))

    def evaluate(self):
        c = self.chart()
        return subst_tm(c.term, c.labels)


def present(ambient, arity, writing, labels):
    """An explicit chart, with parsed children at its top slots."""
    ty = infer(arity, writing)
    assert full(arity, writing)
    parts = []
    args = []
    for decl, x in zip(arity, labels, strict=True):
        if tdim(decl) == tdim(ty):
            assert isinstance(x, Parse)
            parts.append(x)
            actual = x.evaluate()
        else:
            actual = x
        assert infer(ambient, actual) == subst_ty(decl, args)
        args.append(actual)
    node = Node(arity, ty, tuple(Port(x.node) if isinstance(x, Parse) else x for x in labels))
    return Parse(node, writing, tuple(parts))


def full(p, t):
    return fv_tm(t) | fv_ty(infer(p, t)) == set(range(len(p)))


def compare(ambient, a, b):
    assert a.node == b.node
    left, right = a.chart(), b.chart()
    active = [j for j in a.node.slots if left.labels[j] != right.labels[j]]
    proofs = {(left.labels[j], right.labels[j]): compare(ambient, x, y)
              for j, x, y in zip(a.node.slots, a.children, b.children, strict=True) if j in active}
    result = fill_chart(ambient, left, right, active, proofs)
    assert infer(ambient, result)[2:] == (a.evaluate(), b.evaluate())
    return result


def partitions(items):
    """Unordered partitions, with blocks ordered by first occurrence."""
    if not items:
        yield ()
        return
    first, *rest = items
    for blocks in partitions(rest):
        yield ((first,), *blocks)
        for i, block in enumerate(blocks):
            yield ((first, *block), *blocks[:i], *blocks[i+1:])


@cache
def profiles(node, actual_type):
    result = []
    s, t = actual_type[2:]
    for a, b in product(readings(node.arity, node.lower, s), readings(node.arity, node.lower, t)):
        ty = infer(node.arity, a)
        if ty == infer(node.arity, b) and subst_ty(ty, node.lower) == actual_type[1]:
            result.append(arr(ty, a, b))
    return tuple(result)


@cache
def fragment(nodes, types, holes):
    """The poles and the named holes force the entire globular support tree."""
    primitive, glob, rows = {}, [], []

    def lower(terms):
        if all(t[0] != 'v' for t in terms):
            first = terms[0]
            assert all(t[:3] == first[:3] for t in terms)
            return (*first[:3], tuple(lower(args) for args in zip(*(t[3] for t in terms), strict=True)))
        if terms not in primitive:
            index = append_position(terms)
            primitive[terms] = index
        return v(primitive[terms])

    def append_position(row):
        decls = [infer(node.arity, t) for node, t in zip(nodes, row, strict=True)]
        if decls[0] == STAR:
            decl = STAR
        else:
            a, b = (lower(tuple(ty[side] for ty in decls)) for side in (2, 3))
            assert a[0] == b[0] == 'v'
            decl = arr(glob[a[1]], a, b)
        index = len(glob)
        glob.append(decl)
        rows.append(row)
        return index

    source, target = (lower(tuple(ty[side] for ty in types)) for side in (2, 3))
    for row in holes:
        append_position(row)
    check_ctx(tuple(glob))

    incoming = [set() for _ in glob]
    for j, ty in enumerate(glob):
        if ty != STAR:
            incoming[j].add(ty[2][1])
            incoming[ty[3][1]].add(j)
    order = []
    remaining = set(range(len(glob)))
    while remaining:
        ready = [j for j in remaining if not incoming[j].intersection(remaining)]
        if len(ready) != 1:
            return None
        j, = ready
        order.append(j)
        remaining.remove(j)
    p = tree_ctx(shape([tdim(glob[j])+1 for j in order]))
    poles = {i: None if ty == STAR else (ty[2][1], ty[3][1]) for i, ty in enumerate(p)}
    canonical = position_order(poles)
    rename = [None] * len(glob)
    maps = [None] * len(glob)
    for old, new in zip(order, canonical, strict=True):
        rename[old] = v(new)
        maps[new] = rows[old]
    assert all(subst_ty(ty, rename) == p[rename[j][1]] for j, ty in enumerate(glob))
    try:
        writing = head(p, subst_tm(source, rename), subst_tm(target, rename))
    except TypeError_:
        return None
    projections = tuple(subst_tm(writing, sigma) for sigma in zip(*maps, strict=True))
    assert all(infer(node.arity, t) == ty for node, t, ty in zip(nodes, projections, types, strict=True))
    return projections


@cache
def admissible(node, ty, slots):
    holes = tuple((v(j),) for j in slots)
    return fragment((node,), (ty,), holes) is not None


def cut(nodes, group, alternatives, lookup):
    """Descend at one or more aligned slots. Other coordinates keep their arities."""
    by_node = [tuple(j for coord, j in group if coord == i) for i in range(len(nodes))]
    for switches in product(*[((None, *indices) if len(indices) == 1 else (None,)) for indices in by_node]):
        marked = [(i, j) for i, j in enumerate(switches) if j is not None]
        if not marked:
            continue
        actuals = {subst_ty(nodes[i].arity[j], nodes[i].lower) for i, j in marked}
        if len(actuals) != 1:
            continue
        actual, = actuals
        options = [(node,) if j is None else alternatives(node.labels[j].key)
                   for node, j in zip(nodes, switches, strict=True)]
        for inner in product(*options):
            if any(subst_ty(inner[i].ty, inner[i].lower) != actual for i, _ in marked):
                raise ValueError('a grammar production changes the literal type of its nonterminal')
            pending = tuple((i, k) for i, j in enumerate(switches)
                            for k in (by_node[i] if j is None else inner[i].slots))
            choices = [tuple(ty for ty in profiles(node, actual) if admissible(node, ty, by_node[i]))
                       if j is None else (inner[i].ty,)
                       for i, (node, j) in enumerate(zip(nodes, switches, strict=True))]
            for types in product(*choices):
                for terms, descendants in lookup(inner, types, pending):
                    row = list(terms)
                    entries = [dict(d) for d in descendants]
                    for i, j in marked:
                        if not full(inner[i].arity, terms[i]):
                            break
                        kids = tuple(entries[i][slot] for slot in inner[i].slots)
                        entries[i] = {j: Parse(inner[i], terms[i], kids)}
                        row[i] = v(j)
                    else:
                        yield tuple(row), entries


def region(nodes, types, pending, alternatives, lookup):
    for groups in partitions(pending):
        for cuts in product(*(cut(nodes, group, alternatives, lookup) for group in groups)):
            holes = tuple(row for row, _ in cuts)
            descendants = [{j: p for _, entries in cuts for j, p in entries[i].items()}
                           for i in range(len(nodes))]
            terms = fragment(nodes, types, holes)
            if terms is not None:
                yield terms, descendants


def intersection(*nodes, grammar=None):
    """Least fixed point on region profiles, also for cyclic alternative productions."""
    if len({subst_ty(node.ty, node.lower) for node in nodes}) != 1:
        return
    grammar = {} if grammar is None else grammar

    def root_choices(initial):
        # Unary disk writings at their slot's type compose into the next
        # writing. A variable writing reinstates the exact derivation.
        todo = [(initial, ())]
        seen = set()
        while todo:
            node, wrappers = todo.pop()
            if node in seen:
                continue
            seen.add(node)
            slots = node.slots
            if (len(slots) == 1 and node.ty == node.arity[slots[0]]
                    and node.arity == tree_ctx(disc_tree(tdim(node.ty)+1))):
                j, = slots
                key = node.labels[j].key
                todo.extend((other, (*wrappers, (node, j))) for other in grammar.get(key, (key,)))
            else:
                yield node, wrappers

    for choices in product(*(root_choices(node) for node in nodes)):
        core = tuple(dict.fromkeys(node for node, _ in choices))
        witness = common_derivation(core, grammar)
        if witness is not None:
            parses = dict(zip(core, witness, strict=True))
            result = []
            for node, wrappers in choices:
                parsed = parses[node]
                for wrapper, j in reversed(wrappers):
                    parsed = Parse(wrapper, v(j), (parsed,))
                result.append(parsed)
            assert len({p.evaluate() for p in result}) == 1
            yield tuple(result)
            return


def common_derivation(nodes, grammar):
    allowed = {}
    stack = list(nodes)
    while stack:
        node = stack.pop()
        for j in node.slots:
            key = node.labels[j].key
            if key not in allowed:
                allowed[key] = grammar.get(key, (key,))
                stack.extend(allowed[key])

    productive = set()
    while True:
        ready = {key for key, options in allowed.items()
                 if any(all(node.labels[j].key in productive for j in node.slots) for node in options)}
        if ready == productive:
            break
        productive = ready

    def viable(node):
        return all(node.labels[j].key in productive for j in node.slots)

    if not all(viable(node) for node in nodes):
        return

    def alternatives(key):
        return (node for node in allowed[key] if viable(node))

    tables = {}

    def lookup(active, types, pending):
        key = (active, types, tuple(sorted(pending)))
        witness = tables.setdefault(key, None)
        return () if witness is None else (witness,)

    pending = tuple((i, j) for i, node in enumerate(nodes) for j in node.slots)
    root = nodes, tuple(node.ty for node in nodes), pending
    lookup(*root)
    while True:
        count = len(tables)
        changed = False
        for key in tuple(tables):
            if tables[key] is not None:
                continue
            witness = next(region(*key, alternatives, lookup), None)
            if witness is None:
                continue
            tables[key] = witness
            changed = True
            if key == root:
                terms, kids = witness
                if all(full(node.arity, t) for node, t in zip(nodes, terms, strict=True)):
                    result = tuple(Parse(node, t, tuple(row[j] for j in node.slots))
                                   for node, t, row in zip(nodes, terms, kids, strict=True))
                    assert len({p.evaluate() for p in result}) == 1
                    return result
                return None
        if not changed and len(tables) == count:
            return


def anchor_comparison(ambient, start, end, extra=()):
    """Close a finite set of anchor charts under arbitrary nesting, intersection and merging."""
    ty = infer(ambient, start)
    assert infer(ambient, end) == ty
    rank = tdim(ty)+1
    assert all(tdim(decl)+1 < rank for decl in ambient)
    anchors = terms_of_rank(ambient, (start, end, *extra), rank)
    owners = defaultdict(dict)
    modes = defaultdict(list)
    for a in anchors:
        for chart in charts(ambient, a):
            if chart.term[0] == 'v':  # The opaque disk over its own anchor is redundant.
                continue
            p = chart.arity
            node = Node(p, infer(p, chart.term),
                        tuple(Port(x) if tdim(decl)+1 == rank else x
                              for decl, x in zip(p, chart.labels, strict=True)))
            if a not in owners[node]:
                owners[node][a] = chart
                modes[a].append(node)
    paths = {(a, a): ident(ambient, a) for a in anchors}

    def normalize(parsed, target, forward):
        owner, ref = next((x, c) for x, c in owners[parsed.node].items() if (x, target) in paths)
        parsed_chart = parsed.chart()
        left, right = (parsed_chart, ref) if forward else (ref, parsed_chart)
        active = [j for j in parsed.node.slots if left.labels[j] != right.labels[j]]
        proofs = {(left.labels[j], right.labels[j]): normalize(kid, ref.labels[j], forward)
                  for j, kid in zip(parsed.node.slots, parsed.children, strict=True) if j in active}
        main = fill_chart(ambient, left, right, active, proofs)
        if owner == target:
            return main
        if forward:
            return comp2(ambient, rank, main, paths[owner, target])
        return comp2(ambient, rank, paths[target, owner], main)

    def merge_once():
        grammar = {a: tuple(dict.fromkeys(node for x in anchors if (a, x) in paths for node in modes[x]))
                   for a in anchors}
        for a, b in combinations(anchors, 2):
            if (a, b) in paths or infer(ambient, a) != infer(ambient, b):
                continue
            for p, q in product(modes[a], modes[b]):
                join = next(intersection(p, q, grammar=grammar), None)
                if join is None:
                    continue
                left, right = join
                components = {x: [t for t in anchors if (t, x) in paths] for x in (a, b)}
                bridges = {(x, y): comp2(ambient, rank, normalize(first, x, False), normalize(last, y, True))
                           for x, y, first, last in ((a, b, left, right), (b, a, right, left))}
                for (x, y), bridge in bridges.items():
                    for i in components[x]:
                        prefix = bridge if i == x else comp2(ambient, rank, paths[i, x], bridge)
                        for j in components[y]:
                            paths[i, j] = prefix if j == y else comp2(ambient, rank, prefix, paths[y, j])
                return True
        return False

    while (start, end) not in paths and merge_once():
        pass
    result = paths.get((start, end))
    if result is not None:
        assert infer(ambient, result) == arr(ty, start, end)
    return result


def promoted_anchors(ambient, start, end):
    """Promote a maximal penultimate slot and read back the desired literal poles."""
    ty = infer(ambient, start)
    rank = tdim(ty)+1
    found = {}
    for t in (start, end):
        for c in charts(ambient, t):
            for j in maximal_vars(c.arity):
                if tdim(c.arity[j])+1 != rank-1:
                    continue
                wide, minus, arrows = cylinder(c.arity, {j})
                x = arrows[j]
                labels = dict(zip((y[1] for y in minus), c.labels, strict=True))
                labels[tgt(wide, x)[1]] = c.labels[j]
                labels[x[1]] = ident(ambient, c.labels[j])
                sigma = tuple(labels[i] for i in range(len(wide)))
                node = Node(wide, ty, tuple(Port(t) if tdim(decl)+1 == rank else t
                                            for decl, t in zip(wide, sigma, strict=True)))
                for profile in profiles(node, ty):
                    try:
                        generic = head(wide, *profile[2:])
                    except TypeError_:
                        continue
                    actual = subst_tm(generic, sigma)
                    assert infer(ambient, actual) == ty
                    found[actual] = None
    return tuple(found)


def check_forced_support():
    """Compare the marked-pole test with independent strict-cell enumeration."""
    count = 0
    for rank in range(1, 4):
        for cut_rank in range(rank):
            p = tree_ctx(string_tree(cut_rank, [rank, rank, rank]))
            top = tuple(j for j in range(len(p)) if tdim(p[j])+1 == rank)
            node = Node(p, STAR, tuple(map(v, range(len(p)))))

            def cells(d):
                for tree, positions in globular_trees(p, d):
                    g = tree_ctx(tree)
                    t = ucomp(g)
                    while tdim(infer(g, t))+1 < d:
                        t = ident(g, t)
                    yield subst_tm(t, tuple(map(v, positions)))

            def support(t):
                return fv_tm(t) | fv_ty(infer(p, t))

            catalogue = set()
            for t in cells(rank):
                a, b = infer(p, t)[2:]
                catalogue.add((support(a), support(b), support(t).intersection(top)))
            poles = list(cells(rank-1))
            for a, b in product(poles, repeat=2):
                if infer(p, a) != infer(p, b):
                    continue
                for k in range(len(top)+1):
                    for active in combinations(top, k):
                        ty = arr(infer(p, a), a, b)
                        expected = (support(a), support(b), frozenset(active)) in catalogue
                        assert admissible(node, ty, active) == expected
                        count += 1
    print(f'Forced support agreed with independent strict-tree enumeration on {count} profiles.')


def check_recursive_products():
    line = tree_ctx(disc_tree(1))
    f = v(2)
    p = head(line, v(0), v(1))
    left = present(line, line, ident(line, f), sub_from(line, line, {2: p}))
    fixed = tuple(map(v, range(len(line))))
    to_f = present(line, line, head(line, p, f), fixed)
    from_f = present(line, line, head(line, f, p), fixed)
    column = tree_ctx(string_tree(1, [2, 2]))
    i, j = maximal_vars(column)
    writing = comp2(column, 1, v(i), v(j))
    labels = list(sub_from(column, line, {i: to_f.evaluate(), j: from_f.evaluate()}))
    labels[i], labels[j] = to_f, from_f
    right = present(line, column, writing, labels)
    labels = list(sub_from(column, line, {i: left.evaluate(), j: left.evaluate()}))
    labels[i] = labels[j] = Port('products')
    binary = Node(column, infer(column, writing), tuple(labels))
    language = {'products': (binary, left.node)}
    assert next(intersection(binary, left.node, grammar=language), None) is not None
    assert next(intersection(binary, right.node, grammar=language), None) is None
    # Allowing the exposed operation at a leaf changes the least fixed point.
    both = {'products': (binary, left.node, right.node)}
    doubled = list(sub_from(column, line, {i: right.evaluate(), j: right.evaluate()}))
    doubled[i] = doubled[j] = right
    two_exposed = present(line, column, writing, doubled)
    assert next(intersection(binary, two_exposed.node, grammar=both), None) is not None
    print('Decided positive and negative intersections for a productive recursive binary grammar.')


def weak_globe(rank, emitter):
    line = tree_ctx(disc_tree(1))
    p = head(line, v(0), v(1))
    d = p
    for _ in range(rank-3):
        d = ident(line, d)
    l, k = ident(line, d), head(line, d, d)
    ctx = line + (line[2], arr(line[2], p, v(len(line))))
    z = v(len(ctx)-1)
    u = ident(ctx, comp2(ctx, 1, l, z))
    w = comp2(ctx, rank-1, comp2(ctx, 1, head(line, l, k), z),
              comp2(ctx, 1, head(line, k, l), z))
    identity = tuple(map(v, range(len(line))))

    def leaf(t):
        return present(ctx, line, t, identity)

    def on(shape, operation, entries):
        arity = tree_ctx(shape)
        slots = maximal_vars(arity)
        args = list(sub_from(arity, ctx, {j: x.evaluate() if isinstance(x, Parse) else x
                                         for j, x in zip(slots, entries, strict=True)}))
        for j, x in zip(slots, entries, strict=True):
            args[j] = x
        return present(ctx, arity, operation(arity, *map(v, slots)), args)

    left = on(string_tree(1, [rank-1, 2]), lambda g, a, b: ident(g, comp2(g, 1, a, b)), (l, z))
    centre = on(string_tree(1, [rank, 2]), lambda g, a, b: comp2(g, 1, a, b), (leaf(ident(line, l)), z))
    column = string_tree(rank-1, [rank, rank])
    right = on((column[0]+disc_tree(2)[0],),
               lambda g, a, b, y: comp2(g, rank-1, comp2(g, 1, a, y), comp2(g, 1, b, y)),
               (leaf(head(line, l, k)), leaf(head(line, k, l)), z))
    assert left.evaluate() == u and right.evaluate() == w
    assert next(intersection(left.node, right.node), None) is None
    a, b = next(intersection(left.node, centre.node))
    c, e = next(intersection(centre.node, right.node))
    assert a.evaluate() != c.evaluate()
    pieces = [compare(ctx, left, a), compare(ctx, b, c), compare(ctx, e, right)]
    proof = comp2(ctx, rank, comp2(ctx, rank, *pieces[:2]), pieces[2])
    assert infer(ctx, proof) == arr(infer(ctx, u), u, w)
    if emitter:
        emitter.check_type('joinedComparisons', ctx, proof, arr(infer(ctx, u), u, w))
    # A root disk with a recursive slot recognises an empty language until
    # the grammar acquires a finite exit. Simultaneously meet two other modes.
    disk = tree_ctx(disc_tree(rank))
    slot, = maximal_vars(disk)
    sigma = list(sub_from(disk, ctx, {slot: u}))
    sigma[slot] = Port('loop')
    loop = Node(disk, disk[slot], tuple(sigma))
    assert next(intersection(loop, left.node, grammar={'loop': (loop,)}), None) is None
    triple = next(intersection(loop, left.node, centre.node, grammar={'loop': (loop, left.node)}))
    assert len({p.evaluate() for p in triple}) == 1

    assert anchor_comparison(ctx, u, w) is None
    extra = promoted_anchors(ctx, u, w)
    automatic = anchor_comparison(ctx, u, w, extra)
    assert automatic is not None
    if emitter:
        emitter.check_type('fromEndpointPromotions', ctx, automatic, arr(infer(ctx, u), u, w))
    print(f'Rank {rank}: synthesized both joins, decided the cyclic intersections, '
          f'and compared the endpoints using {len(extra)} computed promotion anchors.')


if __name__ == '__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('--rank', type=int, default=4)
    cli.add_argument('--agda', type=Path)
    opt = cli.parse_args()
    if opt.rank < 3:
        cli.error('rank must be at least three')
    out = Emitter() if opt.agda else None
    check_recursive_products()
    check_forced_support()
    weak_globe(opt.rank, out)
    if out:
        opt.agda.write_text(out.module(opt.agda.stem, 'Comparisons from nested chart intersections.'))
