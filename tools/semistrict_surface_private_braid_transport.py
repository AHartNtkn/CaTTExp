"""Lift positioned private degree-four trace moves while retaining every pure braid.

--faces FILE takes the same old readings as semistrict_surface_private_movies.py.
A null answer means the selected trace path could not transport a connector.
"""
from argparse import ArgumentParser
from collections import deque
from itertools import product
import json
from pathlib import Path

from semistrict_surface_acyclic_private_movies import Traces, solve as trace_test
from semistrict_surface_history_group import exchange, inv, realize, reduced
from semistrict_surface_shared_edge import braid_image


def connectors(reading):
    gaps = [()]
    for label, position in reading:
        if label == 'X':
            gaps[-1] += (position + 1,)
        else:
            gaps.append(())
    return gaps


def splice(left, right):
    return reduced(left + right)


def passive_loop(history, position, word, marks):
    legal = realize(history, history, word, marks)
    if legal is not None and all(abs(letter) not in (position, position + 1) for letter in legal):
        return legal
    return None


def isotropy_test(history, position, marks):
    """Certify every loop at this literal labelled checkpoint can pass its update."""
    tree = {history: ()}
    pending = deque(tree)
    while pending:
        h = pending.popleft()
        for j in range(1, len(h)):
            for letter in (j, -j):
                dest = exchange(h, letter, marks)
                if dest is None:
                    continue
                route = tree[h] + (letter,)
                if dest not in tree:
                    tree[dest] = route
                    pending.append(dest)
                else:
                    generator = splice(route, inv(tree[dest]))
                    if passive_loop(history, position, generator, marks) is None:
                        return False
    return True


def replay(chart, start, end, word, gaps):
    h = start
    for k, gap in enumerate(gaps):
        for letter in gap:
            h = exchange(h, letter, chart.marks)
            assert h is not None
        if k < len(word):
            expected, i, p = word[k]
            assert expected == h
            h = chart.act(h, i, p)
    assert h == end


def solve(data, certify=False):
    result = trace_test(data)
    moves = result['trace_moves']
    if moves is None:
        return result
    start = tuple(map(tuple, data['history']))
    layers = data.get('higher', []) + [{}, {}]
    chart = Traces(data['marks'], layers[0], layers[1])
    end, word = chart.read(start, data['source'])
    target = chart.read(start, data['target'])[1]
    gaps, wanted = (connectors(data[k]) for k in ('source', 'target'))
    if braid_image(len(start), sum(gaps, ())) != braid_image(len(start), sum(wanted, ())):
        return dict(result, surface_filler=False, obstruction='unequal erased braids')

    full = {}
    def transport(h, i, loop):
        if certify and (h, i) not in full:
            full[h, i] = isotropy_test(h, i, chart.marks)
        return passive_loop(h, i, loop, chart.marks)

    transports = []
    for tag in moves:
        kind, k, *rest = tag
        dest = next(w for move, w in chart.next(word) if move == tag)
        if kind in ('disjoint', 'increase'):
            edge = (rest[0],)
            gaps[k] = splice(gaps[k], edge)
            gaps[k+1] = splice(inv(edge), gaps[k+1])
        elif kind == 'commute':
            h, i, _ = word[k+1]
            loop = transport(h, i, gaps[k+1])
            if loop is None:
                return dict(result, surface_filler=None, unresolved=['commute', k])
            transports.append(('commute', k, loop))
            gaps[k+2] = splice(loop, gaps[k+2])
            gaps[k+1] = ()
        word = dest
        replay(chart, start, end, word, gaps)

    assert word == target
    for k, (h, i, _) in enumerate(target):
        difference = splice(inv(wanted[k]), gaps[k])
        loop = transport(h, i, difference)
        if loop is None:
            return dict(result, surface_filler=None, unresolved=['endpoint', k])
        transports.append(('endpoint', k, loop))
        gaps[k] = wanted[k]
        gaps[k+1] = splice(loop, gaps[k+1])
        replay(chart, start, end, word, gaps)
    assert braid_image(len(start), gaps[-1]) == braid_image(len(start), wanted[-1])
    answer = dict(result, surface_filler=True, passive_transports=transports)
    if certify:
        answer['all_checkpoint_loops_pass'] = all(full.values())
    return answer


def checks():
    # Two scalars in one gap, a private update on an anchored edge rewrite.
    # Old readings with the anchored event fixed first reduce independently
    # to a two-strand scalar power and the directed private label.
    data = dict(edges={'x':[0,0]}, scalar_at={'s':0}, initial=['x'],
                marks={'a':[['x'],['x']], 'A':[['x'],['x']], 's':[[],[]]},
                higher=[{'p':['a','A'], 'q':['a','A']}, {'r':['p','q']}],
                history=[(0,'a'),(1,'s'),(1,'s')])
    assert isotropy_test(tuple(data['history']), 0, data['marks'])
    count = 0
    for a,b,c,d in product(range(3), repeat=4):
        for p,q in product('pq',repeat=2):
            data.update(source=[('X',1)]*a+[(p,0)]+[('X',1)]*b,
                        target=[('X',1)]*c+[(q,0)]+[('X',1)]*d)
            actual = solve(data)
            assert not actual['acyclic_component']
            assert actual['surface_filler'] == (a+b == c+d and p <= q)
            count += 1

    # A commuting pair of private updates with a genuinely nonidentity
    # intervening loop on three other scalars (nonabelian isotropy).
    data['history'] = [(0,'a'), (0,'a')]+[(1,'s')]*3
    braid = [('X',2),('X',3),('X',3),('X',2)]
    data.update(source=[('p',0)]+braid+[('q',1)],
                target=[('q',1),('p',0)]+braid)
    actual = solve(data)
    assert actual['surface_filler'] and actual['passive_transports'][0][2]
    data.update(target=[('q',1),('p',0)]+list(reversed([('X',3),('X',2),('X',2),('X',3)])))
    assert solve(data)['obstruction'] == 'unequal erased braids'

    # On a wholly scalar base different orientations can give the same
    # positioned trace move. Only the lifted braid indicates which was used.
    scalars = dict(edges={}, scalar_at={'s':0,'S':0}, initial=[], start_vertex=0,
                   marks={'s':[[],[]],'S':[[],[]]}, higher=[{'p':['s','S']}],
                   history=[(0,'s'),(0,'s')],source=[('p',0),('X',0)],
                   target=[('X',0),('p',1)])
    assert solve(scalars)['surface_filler']
    assert not isotropy_test(tuple(scalars['history']), 0, scalars['marks'])
    scalars.update(source=[('X',0),('X',0),('p',0)],target=[('p',0),('X',0),('X',0)])
    assert solve(scalars)['surface_filler'] is None
    print(f'{count} cyclic scalar-power and private-label judgments, noncommuting '
          'three-scalar connectors, signed prism transport and unresolved winding checked')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--faces',type=Path)
    parser.add_argument('--certify-isotropy', action='store_true')
    args = parser.parse_args()
    if args.faces:
        print(json.dumps(solve(json.loads(args.faces.read_text()), args.certify_isotropy)))
    else:
        checks()
