"""Validate the fixed-edge-graph complexity classification for the ordinary join."""

import argparse
from collections import deque
from itertools import combinations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from catt import STAR, arr, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import head
from relative_coherence_hidden_seam import identity
from semistrict_surface_configuration_braids import rewrites
from semistrict_surface_exact_boundary import accepted, rejected, run
from semistrict_surface_join_bubbles import bubble


def branching_returns(edges):
    """Return a vertex and two distinct first-return paths, or None."""
    adjacency = {}
    for name, (x, y) in edges.items():
        adjacency.setdefault(x, []).append((name, y))
    for x, exits in adjacency.items():
        returns = []
        for name, start in exits:
            queue = deque([(start, name)])
            seen = {start}
            while queue:
                vertex, path = queue.popleft()
                if vertex == x:
                    returns.append(path)
                    break
                for edge, dest in adjacency.get(vertex, ()):
                    if dest not in seen:
                        seen.add(dest)
                        queue.append((dest, path + edge))
            if len(returns) == 2:
                return x, *returns
    return None


def check_graphs():
    graph_count = hard = 0
    pairs = list(product(range(3), repeat=2))
    for mask in range(1 << len(pairs)):
        edges = {chr(65 + i): edge for i, edge in enumerate(pairs) if mask & (1 << i)}
        paths = [(x, x, '') for x in range(3)]
        first = {x: set() for x in range(3)}
        for _ in range(3):  # A shortest return after a specified first edge is simple.
            paths = [(x, z, word + edge) for x, y, word in paths
                     for edge, (s, z) in edges.items() if s == y]
            for x, z, word in paths:
                if x == z:
                    first[x].add(word[0])
            paths = [p for p in paths if p[0] != p[1]]
        witness = branching_returns(edges)
        assert bool(witness) == any(len(choices) > 1 for choices in first.values())
        if witness:
            hard += 1
            x, p, q = witness
            assert p[0] != q[0]
            for path in (p, q):
                assert all(edges[e][1] != x for e in path[:-1]) and edges[path[-1]][1] == x
            for letters in product((p, q), repeat=4):
                wire = ''.join(letters)
                cuts = [0] + [i + 1 for i, edge in enumerate(wire) if edges[edge][1] == x]
                assert tuple(wire[i:j] for i, j in zip(cuts, cuts[1:])) == letters
        graph_count += 1
    assert branching_returns({'a': (0, 1), 'b': (0, 1), 'c': (1, 0)}) == (0, 'ac', 'bc')
    print(f'All {graph_count} three-vertex simple digraphs checked ({hard} with branching returns), '
          'and a parallel-edge graph')


def check_sparse_histories():
    edges = {'a': (0, 1), 'b': (1, 0), 'c': (1, 2), 'd': (2, 2)}
    candidates = [(0, '', 'abab'), (0, 'ababab', ''), (1, '', 'ba'), (1, 'baba', ''),
                  (2, '', 'dd'), (2, 'ddd', ''), (1, 'c', 'cd'), (0, 'ab', 'abab'),
                  (0, '', ''), (2, 'd', 'dd')]
    count = 0
    for n in range(5):
        for chosen in combinations(candidates, n):
            births = {x for x, source, _ in chosen if not source}
            deaths = {x for x, _, target in chosen if not target}
            rules = {str(i): rule for i, rule in enumerate(chosen)}
            # The bound accommodates the lcm construction on both actual cycles.
            assert (bubble(edges, rules, 12) is not None) == bool(births & deaths)
            count += 1
    print(f'{count} sparse-graph rule sets compared with positioned empty-to-empty search')


def error_rules(ports):
    """Forget the two wire colours and connect each ill-typed chain to the terminal one."""
    birth, death, error, halt = 'd', 'z', 'X', 'H'
    result = []
    for a, (_, right) in ports.items():
        for b, (left, _) in ports.items():
            if a == death or b == birth or right == left:
                continue
            keep = tuple(x for x in (a, error, b) if x in (birth, error, death))
            result.append(((a, b), keep))
    for gate in (*ports, error):
        if gate not in (birth, death):
            result.extend([((gate, error), (error,)), ((error, gate), (error,))])
    return result + [((birth, error, death), (birth, halt, death))]


def check_error_rules():
    ports = {'d': (None, 0), 'z': (1, None), 'L': (0, 0), 'R': (1, 1),
             'Q': (0, 1), 'H': (0, 1)}
    terminal = ('d', 'H', 'z')
    rules = error_rules(ports)
    backwards = [(v, u) for u, v in rules]
    checked = malformed = 0
    for n in range(6):
        for inner in product('LRQHX', repeat=n):
            chain = ('d', *inner, 'z')
            legal = 'X' not in chain and all(ports[a][1] == ports[b][0]
                                             for a, b in zip(chain, chain[1:]))
            moves = set(rewrites(chain, rules))
            if legal:
                assert not moves
                assert bool(list(rewrites(chain, backwards))) == (chain == terminal)
            else:
                malformed += 1
                # Take an error-producing step if needed, then project the whole actual chain.
                word = chain
                if 'X' not in word:
                    word = next(t for t in rewrites(word, rules) if 'X' in t)
                while len(word) > 3:
                    word = next(t for t in rewrites(word, rules) if len(t) < len(word))
                assert word == ('d', 'X', 'z') and terminal in set(rewrites(word, rules))
            checked += 1
    print(f'{checked} unary chains tested in both rule directions; {malformed} admit error cleanup')


def check_signed_components():
    ports = {'d': (None, 0), 'z': (1, None), 'L': (0, 0), 'R': (1, 1),
             **{q: (0, 1) for q in 'ABCH'}}
    typed = [('A', 'B'), ('B', 'A'), ('C', 'H'), ('LH', 'H'), ('HR', 'H')]
    moves = error_rules(ports) + [(tuple(a), tuple(b)) for a, b in typed]
    signed = moves + [(b, a) for a, b in moves]
    terminal = ('d', 'H', 'z')
    reached = {terminal}
    queue = deque([terminal])
    while queue:
        for dest in rewrites(queue.popleft(), signed):
            if len(dest) <= 6 and dest not in reached:
                reached.add(dest)
                queue.append(dest)
    blocked = 0
    for n in range(5):
        for inner in product('LRABCHX', repeat=n):
            chain = ('d', *inner, 'z')
            legal = 'X' not in chain and all(ports[a][1] == ports[b][0]
                                             for a, b in zip(chain, chain[1:]))
            loops = legal and any(q in inner for q in 'AB')
            assert (chain in reached) != loops
            blocked += loops
    print(f'Signed reachability from the terminal separates {len(reached)} chains '
          f'from {blocked} well-typed nonhalting chains')


def check_thick_paths():
    # Another edge can enter and leave the chosen cycle. Only the (ab) bands carry rules.
    edges = {'a': (0, 1), 'b': (1, 0), 't': (1, 1), 'u': (0, 1)}
    p = 'ab'
    tested = 0
    for n in range(8):
        thick = p * n
        vertices = [0]
        for edge in thick:
            a, b = edges[edge]
            assert vertices[-1] == a
            vertices.append(b)
        for src, tgt in [(0, 1), (1, 0), (1, 1)]:
            actual = {(pos, thick[:pos] + p * tgt + thick[pos + len(p) * src:])
                      for pos, x in enumerate(vertices) if x == 0 and thick.startswith(p * src, pos)}
            expected = {(2 * pos, p * (n - src + tgt)) for pos in range(n - src + 1)}
            assert actual == expected
            tested += len(actual)
    print(f'{tested} positioned births, deaths and unary gates checked on a subdivided cycle')


def check_point_bubbles(directory):
    point = (STAR,)
    a = b = v(0)
    emitter = Emitter()
    for m in range(2, 6):
        s = head(point, a, b)
        t = comp2(point, m - 2, s, identity(point, b))
        ctx = point + (arr(infer(point, s), s, t),)
        raised = comp2(ctx, m - 2, v(1), head(point, b, a))
        l, r = infer(ctx, raised)[2:]
        unit = identity(point, a)
        start = head(point, unit, l)
        end = head(point, r, unit)
        bubble_term = comp2(ctx, m - 1, comp2(ctx, m - 1, start, raised), end)
        expected = arr(infer(point, unit), unit, unit)
        assert infer(ctx, bubble_term) == expected
        if directory:
            emitter.check_type('bubble' + str(m), ctx, bubble_term, expected)
        a, b = s, t
    print('Point-only boundary fits checked at their prescribed identity faces in degrees 2–5')
    if directory:
        (directory / 'FixedGraphPointBubbles.agda').write_text(
            emitter.module('FixedGraphPointBubbles', 'First positive generator at a point.'))


def rice_check(binary):
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        base = '(x : *) (y : *) (a : x -> y) (b : y -> x)'
        band = 'comp[a,b]'
        sig = (f'{base} (d : id(x) -> {band}) (z : {band} -> id(x))'
               f' (l : {band} -> {band}) (r : {band} -> {band})'
               f' (bad : {band} -> {band}) (halt : {band} -> {band})')
        changes = [('middle', 'comp[r,l]', 'bad'),
                   ('birthbad', 'comp[d,r]', 'comp[d,bad]'),
                   ('deathbad', 'comp[l,z]', 'comp[bad,z]'),
                   ('closedbad', 'comp[d,z]', 'comp[comp[d,bad],z]'),
                   ('absorb', 'comp[l,bad]', 'bad'),
                   ('finish', 'comp[comp[d,bad],z]', 'comp[comp[d,halt],z]')]
        decls = []
        for name, u, v in changes:
            arrows = f' (p : {u} -> {v}) (q : {v} -> {u})'
            for suffix, s, t in [('src', 'comp[p,q]', f'id({u})'),
                                 ('tgt', 'comp[q,p]', f'id({v})')]:
                for label, left, right in [('out', s, t), ('in', t, s)]:
                    decls.append((name + suffix + label, f'{sig}{arrows} (k : {left} -> {right})',
                                  f'{left} -> {right}', 'k'))
        defs = [f'def {n} {ctx} : {ty} = {tm}' for n, ctx, ty, tm in decls]
        (folder / 'Bands.catt').write_text('\n'.join(defs) + '\n')
        accepted(run(binary, folder, 'Bands.catt'), 'Bands.catt', [d[0] for d in decls])
        # Decode the cycle by retaining its last edge. The reverse diagram needs the raw unit fits.
        padded = 'comp[id(x),f]'
        context = '(x : *) (f : x -> x) (l : f -> f) (r : f -> f) (bad : f -> f) (p : comp[r,l] -> bad)'
        body = (f'def bandfit {context} : {padded} -> {padded} = l\n'
                f'def rulefit {context} : comp[r,bandfit(x,f,l,r,bad,p)] -> bad = p\n')
        (folder / 'Return.catt').write_text(body)
        rejected(run(binary, folder, 'Return.catt'), 'Return.catt', 'bandfit')
        accepted(run(binary, folder, 'Return.catt', ('--su',)), 'Return.catt', ['bandfit', 'rulefit'])
    print(f'Rice checked {len(decls)} raw inverse comparisons on the cycle and the strict-unit return')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rice', type=Path, help='path to a built catt_strict executable')
    parser.add_argument('--agda-dir', type=Path, help='write the raw point-bubble typings here')
    args = parser.parse_args()
    check_graphs()
    check_sparse_histories()
    check_error_rules()
    check_signed_components()
    check_thick_paths()
    check_point_bubbles(args.agda_dir)
    if args.rice:
        rice_check(args.rice.resolve())
