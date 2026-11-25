"""Evaluate the integral mixed winding on typed CaTT naturality squares."""
from argparse import ArgumentParser
from collections import Counter
from dataclasses import dataclass, field
from functools import lru_cache
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import (STAR, arr, comp2, glue_tree, infer, maximal_vars, src,
                  sub_from, subst_tm, tdim, tgt, tree_ctx, tree_of, v)
from catt_unit_ordered_exchange import temporal_words
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_exact_boundary import accepted, run
from partial_cylinder_steiner import trees
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_mixed_word_tests import point_push
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_scalar_pairs import branches, divergence, positions, splice, trunk


@dataclass
class Reading:
    mass: int = 0
    charge: int = 0
    vertices: Counter = field(default_factory=Counter)
    edges: Counter = field(default_factory=Counter)


@lru_cache(None)
def slots(arity):
    """Depth-indexed positions, and the position of each boundary variant."""
    first = {}
    at = [()]

    def visit(tree, parent, current):
        for i, child in enumerate(tree):
            pos = parent + (i,)
            target = len(at)
            first[pos] = target + 1
            at.extend((at[current], pos))
            visit(child, pos, target + 1)
            current = target

    visit(tree_of(arity), (), 0)
    return first, at


def fork(active, standing):
    return divergence(active, standing), int(active > standing)


def cone_path(root, start, end):
    """Signed edges directed from a horizontal vertex to a vertical one."""
    edges = Counter()
    for sign, vertex in ((-1, start), (1, end)):
        if vertex != root:
            assert root[0] == 0 and vertex[0] == 1
            edges[root, vertex] += sign
    return edges


def evaluate(term, labels, moving_rank=3):
    if term[0] == 'v':
        return labels[term[1]]
    _, arity, ty, sub = term
    degree = tdim(ty) + 1
    out = Reading()
    if degree < 2:
        return out
    first, at = slots(arity)
    inputs = [evaluate(value, labels, moving_rank) for value in sub]
    masses = {p: inputs[i].mass for p, i in first.items() if len(p) == 2}
    if degree == 2:
        return Reading(mass=sum(masses.values()))
    if degree < moving_rank:
        return out
    for p, i in first.items():
        if len(p) == degree:
            if degree == moving_rank:
                out.charge += inputs[i].charge
                out.vertices.update(inputs[i].vertices)
            elif degree == moving_rank + 1:
                out.edges.update(inputs[i].edges)
    assert degree in (moving_rank, moving_rank + 1)
    for active, i in first.items():
        if len(active) != moving_rank or not inputs[i].charge:
            continue
        for standing, mass in masses.items():
            weight = inputs[i].charge * mass
            if not weight or active[:2] == standing:
                continue
            root = fork(active[:2], standing)
            if degree == moving_rank:
                out.vertices[root] += weight
                continue
            # Distinguish the two generic slots even when their actual faces
            # are degenerate. Every variant at a transported slot has its tag.
            tags = [Reading(mass=int(pos == standing), charge=int(pos == active)) for pos in at]
            vertices = []
            for face in ty[2:]:
                reading = evaluate(face, tags, moving_rank)
                vertex, = reading.vertices
                assert reading.vertices[vertex] == reading.charge == 1
                vertices.append(vertex)
            for edge, coef in cone_path(root, *vertices).items():
                out.edges[edge] += weight * coef
    return out


def naturality(left_moves):
    pair = tree_ctx(glue_tree(2, 0, 2))
    swap = head(pair, *temporal_words(pair, *map(v, maximal_vars(pair)), 0, 1))
    p = tree_ctx(glue_tree(3, 0, 2) if left_moves else glue_tree(2, 0, 3))
    first, second = map(v, maximal_vars(p))
    change, fixed = (first, second) if left_moves else (second, first)
    before, after = src(p, change), tgt(p, change)

    def exchange(term):
        terms = (term, fixed) if left_moves else (fixed, term)
        return subst_tm(swap, sub_from(pair, p, dict(zip(maximal_vars(pair), terms))))

    def beside(a, b):
        return comp2(p, 0, a, b)

    if left_moves:
        early = comp2(p, 1, beside(change, src(p, fixed)), beside(tgt(p, before), fixed))
        late = comp2(p, 1, beside(src(p, before), fixed), beside(change, tgt(p, fixed)))
    else:
        early = comp2(p, 1, beside(fixed, src(p, before)), beside(tgt(p, fixed), change))
        late = comp2(p, 1, beside(src(p, fixed), change), beside(fixed, tgt(p, before)))
    return p, head(p, comp2(p, 2, early, exchange(after)), comp2(p, 2, exchange(before), late))


def origins(position, branch, width):
    """Exterior slot and optional interior slot in a spliced tree."""
    prefix = branch[:-1]
    level = len(prefix)
    if len(position) <= level:
        interior = (0,) * len(position) if branch[:len(position)] == position else None
        return position, interior
    if position[:level] != prefix:
        return position, None
    i, start = position[level], branch[-1]
    if i < start:
        return position, None
    tail = position[level + 1:]
    if i >= start + width:
        return prefix + (i - width + 1,) + tail, None
    return branch + (0,) * len(tail), (0,) * level + (i - start,) + tail


def check_mixed_splices(moving_rank=3, edge_bound=6):
    counts = Counter()
    shapes = [t for size in range(edge_bound + 1) for t in trees(size)]
    for outer in shapes:
        for branch, height in branches(outer):
            for inner in shapes:
                if trunk(inner) < len(branch) - 1 or positions(inner, height + 1):
                    continue
                node = inner
                for _ in branch[:-1]:
                    node, = node
                width = len(node)
                joined = splice(outer, branch, inner)
                for active in positions(joined, moving_rank):
                    old_a, inner_a = origins(active, branch, width)
                    assert old_a in positions(outer, moving_rank)
                    for standing in positions(joined, 2):
                        if active[:2] == standing:
                            continue
                        old_b, inner_b = origins(standing, branch, width)
                        assert old_b in positions(outer, 2)
                        if old_a[:2] != old_b:
                            inherited = fork(old_a[:2], old_b)
                            counts['exterior'] += 1
                        else:
                            assert inner_a in positions(inner, moving_rank) and inner_b in positions(inner, 2)
                            inherited = fork(inner_a[:2], inner_b)
                            counts['interior'] += 1
                        assert fork(active[:2], standing) == inherited
    assert all(counts[k] for k in ('exterior', 'interior'))
    return counts


def check_squares(emitter):
    point = (STAR,)
    line = identity(point, v(0))
    unit = identity(point, line)
    ctx = point + (arr(infer(point, line), line, line), arr(infer(point, unit), unit, unit))
    base = comp2(ctx, 1, v(2), v(1))
    emitter.check_typed('base', ctx, base)
    squares = []
    for left_moves in (True, False):
        p, square = naturality(left_moves)
        terms = (v(2), v(1)) if left_moves else (v(1), v(2))
        label = sub_from(p, ctx, dict(zip(maximal_vars(p), terms)))
        actual = subst_tm(square, label)
        emitter.check_typed(f'square{int(left_moves)}', ctx, actual)
        squares.append(actual)
    h, vtx = [(0, k) for k in (0, 1)], [(1, k) for k in (0, 1)]
    cycle = {(h[0], vtx[0]): -1, (h[0], vtx[1]): 1,
             (h[1], vtx[1]): -1, (h[1], vtx[0]): 1}
    for mass in range(4):
        for charge in range(-2, 3):
            labels = [Reading(), Reading(mass=mass), Reading(charge=charge)]
            edges = Counter()
            for side, square in enumerate(squares):
                faces = [evaluate(t, labels) for t in infer(ctx, square)[2:]]
                for j, face in enumerate(faces):
                    assert face.charge == charge
                    assert face.vertices == Counter({vtx[side ^ j]: mass * charge})
                arc = evaluate(square, labels).edges
                assert arc == Counter({(h[side], vtx[side]): -mass * charge,
                                       (h[side], vtx[1 - side]): mass * charge})
                edges.update(arc)
            assert edges == Counter({edge: mass * charge * coef for edge, coef in cycle.items()})


def winding_matrix(holes, probes, words):
    """Exponent sums indexed by the probe colour and the stationary colour."""
    coordinates = Counter()
    for probe, word in zip(probes, words, strict=True):
        for letter in word:
            if not 1 <= abs(letter) <= len(holes):
                raise ValueError('meridian outside the stationary row')
            coordinates[probe, holes[abs(letter) - 1]] += 1 if letter > 0 else -1
    return {pair: value for pair, value in coordinates.items() if value}


def check_stationary_action():
    # Use clockwise meridians so conjugation by a stationary half twist
    # agrees with the orientation of braid_image on a leftmost probe.
    def push(word):
        return point_push(tuple(-i for i in word))

    checks = 0
    for h in range(2, 7):
        for i in range(1, h):
            for braid in ((i,), (-i,), (i, i)):
                lift = tuple((1 if j > 0 else -1) * (abs(j) + 1) for j in braid)
                action = braid_image(h, braid)
                for j, image in enumerate(action, 1):
                    transported = lift + push((j,)) + inv(lift)
                    assert braid_image(h + 1, transported) == braid_image(h + 1, push(image))
                    checks += 1
            # The second meridian after a pure twist gives the exact adjacent
            # commutator relation when it is equated to its initial value.
            square = braid_image(h, (i, i))
            assert reduced(square[i] + (-(i + 1),)) == (i, i + 1, -i, -(i + 1))
            for j in range(i + 1, h + 1):
                move = tuple(range(-j + 1, -i))  # inverse twists, distant end first
                transported = braid_image(h, move)
                assert (transported[i - 1], transported[i]) == ((i,), (j,))
    return checks


def check_colour_sums():
    holes, probes = ('a', 'b', 'a'), ('u', 'u', 'v')
    words = [(1, -2, 3), (2, -1), (-3, 2, -1)]
    expected = {('u', 'a'): 1, ('v', 'a'): -2, ('v', 'b'): 1}
    assert winding_matrix(holes, probes, words) == expected
    assert winding_matrix(holes, probes, [words[1], words[0], words[2]]) == expected
    # A braid interchanging the two a positions, across the intervening b.
    coloured = braid_image(3, (1, 2, -1))
    def act(word):
        return reduced(j for i in word for j in
                       (coloured[i - 1] if i > 0 else inv(coloured[-i - 1])))
    for word in product((1, -1, 2, -2, 3, -3), repeat=4):
        assert winding_matrix(holes, ('u',), [act(word)]) == winding_matrix(holes, ('u',), [word])


def check_published(checkout):
    text = (checkout / 'examples/syllepsis-su.catt').read_text()
    defs = text[text.index('def swap ='):text.index('def left u')]
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        (folder / 'Winding.catt').write_text(defs + """
def circuit (x : *) (q : id(id(x)) -> id(id(x))) (b : id(x) -> id(x))
  : comp[[q],b] -> comp[[q],b] = comp[swapnatleft(q,b),swapnatright(b,q)]
def slide (x : *) (q : id(id(x)) -> id(id(x))) (w : id(x) -> id(x)) (s : w -> w)
  : comp[comp[[q],w],s] -> comp[s,comp[[q],w]] = swap(q,s)
def stationary (x : *) (q : id(id(x)) -> id(id(x))) (w : id(x) -> id(x))
  : swap(q,id(w)) -> id(comp[[q],w]) = id(swap(q,id(w)))
""")
        for mode in ('--su', '--sua'):
            accepted(run(checkout / 'target/release/catt_strict', folder, 'Winding.catt', [mode]),
                     'Winding.catt', ['circuit', 'slide', 'stationary'])


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    parser.add_argument('--catt-strict', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    check_squares(emitter)
    print('Two typed squares give the oriented four-cycle at all 20 signed labellings.')
    print(f'{check_stationary_action()} Artin actions agree with conjugation of the probe push.')
    check_colour_sums()
    print('Colour sums agree through 1,296 transported meridian words.')
    counts = check_mixed_splices()
    print(f"Mixed pairs after splicing: {counts['exterior']} exterior and {counts['interior']} interior.")
    if args.agda_dir:
        name = 'MixedWinding'
        (args.agda_dir / (name + '.agda')).write_text(emitter.module(name, __doc__))
    if args.catt_strict:
        check_published(args.catt_strict.resolve())
        print('Rice checked the closed circuit in strict-unit and insertion modes.')
