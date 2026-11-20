"""Turn a typed relative degree witness into chains with a common simplex face template."""
from argparse import ArgumentParser
import json
from itertools import combinations, product
from pathlib import Path

from canonical_gray_cube import build_cube
from catt import check_ctx, comp2, infer, v
from relative_coherence_based_columns import Brackets, difference
from relative_coherence_colour_degree import add_scaled, cone, immutable, relative_columns, simplex_boundary
from relative_coherence_face_transfer import Transfer, lift, reduced
from relative_coherence_hidden_seam import identity
from relative_coherence_integral_degree import integral_test, loop_example
from relative_coherence_polarized_cube import face_names, vertex_names
from relative_coherence_simplex_carrier import flags, orientation


def staircase(names):
    """Signed vertex functions: pin slot zero, difference consecutive vertices thereafter."""
    result = {}
    for bits in product((0, 1), repeat=len(names)-1):
        word = (names[0], *(names[j-e] for j, e in enumerate(bits, 1)))
        result[word] = (-1)**sum(bits)
    return result


def faces(names):
    return [(names[:i]+names[i+1:], (-1)**i) for i in range(len(names))]


def edge_tensor(edges):
    result = {}
    for bits in product((0, 1), repeat=len(edges)):
        word = tuple(edge[bit] for edge, bit in zip(edges, bits))
        add_scaled(result, {word: 1}, (-1)**bits.count(0))
    return result


def substitute_words(chain, maps):
    result = {}
    for f, a in maps.items():
        for word, b in chain.items():
            add_scaled(result, {tuple(f[i] for i in word): 1}, a*b)
    return result


def forest_maps(edges):
    """Return signed vertex maps from the star to this forest and back."""
    k = len(edges)
    vertices = sorted({v for edge in edges for v in edge})
    neighbours = {v: [] for v in vertices}
    for i, (a, b) in enumerate(edges, 1):
        neighbours[a].append((i, b, 1))
        neighbours[b].append((i, a, -1))
    children, visited = {}, set()
    sign = 1
    for root in vertices:
        if root in visited:
            continue
        visited.add(root)
        stack = [root]
        while stack:
            for i, vertex, direction in neighbours[stack.pop()]:
                if vertex not in visited:
                    visited.add(vertex)
                    stack.append(vertex)
                    children[vertex] = i
                    sign *= direction
    if len(children) != k:
        raise ValueError('the differences contain a cycle')
    to_forest = {(vertices[0], *word): a for word, a in edge_tensor(edges).items()}
    to_star = {}
    for bits in product((0, 1), repeat=k):
        f = [0] * (vertices[-1]+1)
        for vertex, i in children.items():
            if bits[i-1]:
                f[vertex] = i
        to_star[tuple(f)] = sign*(-1)**bits.count(0)
    return to_forest, to_star


def forest_check(edges):
    star = edge_tensor([(0, i+1) for i in range(len(edges))])
    tensor = edge_tensor(edges)
    forward, backward = forest_maps(edges)
    assert substitute_words(star, forward) == tensor
    assert substitute_words(tensor, backward) == star
    return tensor


def typed_forest_filling():
    p = Brackets(4)
    first, second, shortcut = (p.bracket(v(i), v(j)) for i, j in ((0, 1), (1, 2), (0, 2)))
    composite = comp2(p.ctx, 0, first, second)
    triangle = p.bracket(shortcut, composite)
    calc = SimplexChains(p, 2)
    names = (0, 1, 2)
    lower, primitive, star, _ = calc.descend({triangle[1]: 1}, names, 0, 0)
    assert lower == {second[1]: 1}
    edges = [(0, 1), (2, 3)]
    forward, backward = forest_maps(edges)

    def apply_maps(vector, maps):
        out = {}
        for f, sign in maps.items():
            add_scaled(out, calc.push(vector, f, 0), sign)
        return out

    forest = apply_maps({first[1]: 1}, edge_tensor(edges))
    transported = apply_maps(primitive, forward)
    assert calc.boundary(transported, 0) == forest
    assert calc.boundary(apply_maps(transported, backward), 0) == star
    check_ctx(p.ctx)
    print('Typed triangle filling transported to two disjoint edges and back; both boundaries checked.')


def function_check(k):
    names = tuple(range(k+1))
    funcs = staircase(names)
    for r in range(k+1):
        for subset in combinations(names, r):
            marginal = {}
            for word, a in funcs.items():
                add_scaled(marginal, {tuple(word[i] for i in subset): 1}, a)
            if subset != names[1:]:
                assert not marginal
                continue
            expected = {}
            for f, a in faces(names):
                add_scaled(expected, staircase(f), a)
            assert expected == marginal
    assert [f for f in funcs if len(set(f)) == k+1] == [names]


def suspended_triangle(k):
    cycle = simplex_boundary({(0, 1, 4): 1})
    for j in range(k-2):
        lo = 6+2*j
        cycle = {(*f, t): a*s for f, a in cycle.items() for t, s in ((lo, 1), (lo+1, -1))}
    return cycle


def five_cube_boundary():
    """Retain cube face addresses to check cancellation before bracket identifications."""
    n = 5
    seed = vertex_names(n, tuple(range(n)))
    target = suspended_triangle(n+1)
    chain = {}
    for face, a in target.items():
        for f, sign in staircase(face).items():
            add_scaled(chain, {tuple(f[j] for j in seed): 1}, a*sign)
    boundary, simplices = {}, {}
    paths = tuple(flags(range(n)))
    for word, a in chain.items():
        for axis in range(n):
            for side in (0, 1):
                key = (axis, side, face_names(word, axis, side))
                add_scaled(boundary, {key: 1}, a*(-1)**axis*(2*side-1))
        for path, sign in paths:
            names = tuple(word[i] for i in path)
            if len(set(names)) == n+1:
                add_scaled(simplices, {tuple(sorted(names)): 1}, a*sign*orientation(names))
    assert not boundary and len(target) == 48
    pairs = [(0, 1), (1, 4), (7, 6), (9, 8), (11, 10), (13, 12)]
    tensor = forest_check(pairs)
    assert {tuple(f[j] for j in seed): a for f, a in tensor.items()} == chain
    # Include a path, a branching tree and both orientations of each example.
    for edges in ([(i, i+1) for i in range(6)], [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6)], pairs):
        forest_check(edges)
        forest_check([(b, a) for a, b in reversed(edges)])
    degree = simplices[next(iter(target))] * target[next(iter(target))]
    assert abs(degree) == 1 and simplices == {f: degree*a for f, a in target.items()}
    print(f'Four suspensions: {len(chain)} labelled five-cubes, zero boundary at each facet address, '
          f'{len(simplices)} oriented five-simplices, degree multiplier {degree}.')


class SimplexChains(Transfer):
    def push(self, chain, names, m):
        result = {}
        for i, a in chain.items():
            add_scaled(result, {self.relabel(i, names)[1]: 1}, a)
        return reduced(result, m)

    def face_sum(self, chain, names, m):
        result = {}
        for f, a in faces(names):
            add_scaled(result, self.push(chain, f, m), a)
        return reduced(result, m)

    def templates(self, x, k, degree, m):
        sections = []
        for j in range(k, -1, -1):
            names = tuple(range(j+1))
            section = {}
            for f, a in staircase(names).items():
                add_scaled(section, self.push(x, f, m), a)
            section = reduced(section, m)
            h = {}
            for i, a in section.items():
                add_scaled(h, self.image(i), a)
            assert reduced(h, m) == reduced({names: degree}, m)
            sections.append(section)
            if j:
                bd = self.boundary(x, m)
                assert all(self.names(i) < set(names) for i in bd)
                opposite = {i: a for i, a in bd.items() if self.names(i) == set(names[1:])}
                x = self.push(opposite, (0, *range(j)), m)
        sections.reverse()
        for j in range(1, k+1):
            assert self.boundary(sections[j], m) == self.face_sum(sections[j-1], tuple(range(j+1)), m)
        return sections

    def single_boundary(self, chain, n, modulus):
        # Response 13 only needs to preserve the boundary at the last rank.
        pairs = []
        for i, a in chain.items():
            s, t = self.ctx[i][2:]
            pair = self.p.base_pair(s, t, v(0)) if a > 0 else self.p.base_pair(t, s, v(0))
            pairs.extend([pair]*abs(a))
        # Pairwise composition bounds the depth of the raw terms.
        while len(pairs) > 1:
            even = len(pairs) - len(pairs)%2
            layer = [tuple(comp2(self.ctx, n-2, u, vv) for u, vv in zip(pairs[j], pairs[j+1]))
                     for j in range(0, even, 2)]
            pairs = layer + pairs[even:]
        (source, target), = pairs
        assert infer(self.ctx, source) == infer(self.ctx, target)
        assert difference(self.ctx, source, target) == self.boundary(chain, 0)
        if modulus:
            for _ in range(modulus-1):
                target = comp2(self.ctx, n-2, target, source)
            source = v(0)
            for _ in range(n-1):
                source = identity(self.ctx, source)
        return self.p.bracket(source, target)[1]

    def compress(self, sections, degree, m):
        # At rank one only the two loops and the opposed edge need correcting.
        f = self.p.bracket(v(0), v(1))
        edge = reduced({f[1]:degree}, m)
        change = {}
        for i, a in sections[1].items():
            u, t = self.ctx[i][2:]
            if u == t:
                path = v(i)
            elif u == v(1) and t == v(0):
                u = v(0)
                path = comp2(self.ctx, 0, f, v(i))
            else:
                assert v(i) == f
                continue
            correction = self.p.bracket(identity(self.ctx, u), path)
            add_scaled(change, {correction[1]:1}, -a)
        delta = edge.copy()
        add_scaled(delta, sections[1], -1)
        assert self.boundary(change, m) == reduced(delta, m)

        result = [sections[0], edge]
        for n in range(2, len(sections)):
            names = tuple(range(n+1))
            chain = sections[n].copy()
            add_scaled(chain, self.face_sum(change, names, m), 1)
            chain = {i: a-m if m and 2*a > m else a for i, a in reduced(chain, m).items()}
            required = self.face_sum(result[-1], names, m)
            assert self.boundary(chain, m) == required
            if n+1 == len(sections):
                g = self.single_boundary(chain, n, m)
            else:
                g, change = self.based_representative(chain, v(0), n)
                if m:
                    g, extra = self.from_identity(g, v(0), n, m)
                    add_scaled(change, extra, 1)
            assert self.boundary({g:1}, m) == required and len(required) == n+1
            assert reduced({0:self.image(g).get(names, 0)-degree}, m) == {}
            result.append({g:1})
        return result


def run(ctx, colours, k, compress, target=None, chain=None, modulus=0):
    if k < 2:
        raise ValueError('the source degree must be at least two')
    columns, volumes = relative_columns(ctx, colours, k)
    if chain is None:
        witness = integral_test(columns, volumes)
        if 'potential' in witness:
            print('The supplied parameter has an integral degree potential.')
            return
        chain, modulus = witness['chain'], witness['modulus']
    if modulus != 0 and modulus < 2:
        raise ValueError('use zero for integers or a modulus of at least two')
    m = modulus
    bd = {}
    for i, a in chain.items():
        add_scaled(bd, columns[i], a)
    degree = sum(a*volumes[i] for i, a in chain.items())
    if reduced(bd, m) or not reduced({0:degree}, m):
        raise ValueError('the chosen chain must be relative and have nonzero degree')
    vertices = k+1
    if target:
        if any(len(f) != k or tuple(sorted(set(f))) != f or min(f) < 0 for f in target):
            raise ValueError('list each target face by k strictly increasing nonnegative names')
        if reduced(simplex_boundary(target), m):
            raise ValueError('the target must be a cycle over the chosen coefficient ring')
        vertices = max(vertices, 1+max(f[-1] for f in target))
    p = Brackets(vertices)
    labels = lift(ctx, colours, p)
    x = {}
    for i, a in chain.items():
        add_scaled(x, {labels[i][1]: 1}, a)
    calc = SimplexChains(p, k)
    sections = calc.templates(x, k, degree, m)
    print(f'Degree {degree}, modulus {m} (0 for integers): '
          f'compatible template sizes {[len(s) for s in sections]}.', flush=True)
    if compress:
        sections = calc.compress(sections, degree, m)
        print(f'One bracket per simplex from rank two through {k}; exact alternating boundaries checked.')
    if target:
        filling = cone(0, target)
        assert reduced(simplex_boundary(filling), m) == reduced(target, m)
        def realize(chain, template):
            out = {}
            for face, a in chain.items():
                add_scaled(out, calc.push(template, face, m), a)
            return reduced(out, m)
        top = realize(filling, sections[-1])
        bd = realize(target, sections[-2])
        assert calc.boundary(top, m) == bd
        projection = {}
        for i, a in bd.items():
            add_scaled(projection, calc.image(i), a)
        assert reduced(projection, m) == reduced({f: degree*a for f, a in target.items()}, m)
        print(f'Typed filling with {len(top)} cells and {len(bd)} boundary cells.')
    check_ctx(p.ctx)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, help='typed-context JSON as in Response 19')
    parser.add_argument('--compress', action='store_true', help='also build the literal single top bracket')
    args = parser.parse_args()
    for k in range(1, 9):
        function_check(k)
    print('All proper restriction identities checked through rank eight.')
    five_cube_boundary()
    typed_forest_filling()
    if args.input:
        data = json.loads(args.input.read_text())
        chain = {int(i): a for i, a in data['chain'].items()} if 'chain' in data else None
        if 'modulus' in data and chain is None:
            parser.error('supply a chain when specifying the modulus')
        target = {}
        for face, a in data.get('target', []):
            add_scaled(target, {tuple(face): 1}, a)
        run(immutable(data['context']), data['colours'], data['degree'], args.compress,
            target, chain, data.get('modulus', 0))
    else:
        colours = [3, 0, 1, 0, 2, 0, 1, 0]
        run(build_cube()[0], colours, 3, args.compress, suspended_triangle(3))
        run(loop_example(2, 4)[0], colours, 3, args.compress)
