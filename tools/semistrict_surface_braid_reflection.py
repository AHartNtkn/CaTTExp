"""Decide degree-four Gray reflection for braid-preserving attachments at strict faces."""
import argparse
import json
from collections import defaultdict
from itertools import product
from pathlib import Path

from catt import STAR, arr, comp2, infer, src, tgt, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head
from relative_coherence_hidden_seam import identity
from semistrict_surface_scalar_cube import cube_terms
from semistrict_surface_return_gaps import exchange_at, gap_outside_dictionary
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_three_axis_paths import Chart


def follow(history, word, rules):
    for position in word:
        if not 1 <= position < len(history):
            raise ValueError('crossing outside temporal history')
        history = exchange_at(history, position-1, rules)
        if history is None:
            raise ValueError('crossing acts on overlapping or incorrectly ordered occurrences')
    return history


def end_vertex(edges, start, path):
    vertex = start
    for c in path:
        u, v = edges[c]
        if u != vertex:
            raise ValueError('edge path is disconnected')
        vertex = v
    return vertex


def certify(data):
    """Return a missing chart, or None if every old four-boundary reflects."""
    edges = data['edges']
    if any(len(edge) != 1 for edge in edges):
        raise ValueError('edge identifiers must be single characters')
    specs = data['rules']  # generator -> [source vertex, input edge path, output edge path]
    marks = {name: (s, t) for name, (_, s, t) in specs.items()}
    poles = {}
    for name, (v, s, t) in specs.items():
        end = end_vertex(edges, v, s)
        if end != end_vertex(edges, v, t):
            raise ValueError('2-generator has nonparallel paths')
        poles[name] = v, end

    covered = defaultdict(set)
    for entry in data['attachments']:
        vertex, path, steps, l, r = entry
        end_vertex(edges, vertex, path)
        history = tuple((p, n) for p, n in steps)
        current = path
        for pos, name in history:
            s, t = marks[name]
            if (not 0 <= pos <= len(current) or not current.startswith(s, pos)
                    or end_vertex(edges, vertex, current[:pos]) != poles[name][0]):
                raise ValueError('ill-typed temporal history in declaration')
            current = current[:pos] + t + current[pos+len(s):]
        if follow(history, l, marks) != follow(history, r, marks):
            raise ValueError('nonparallel declaration faces')
        if braid_image(len(history), l) != braid_image(len(history), r):
            raise ValueError('the declaration faces represent different braids')
        if len(history) != 3 or tuple(l) != (2,1,2) or tuple(r) != (1,2,1):
            continue
        # Recover the three input segments from the unaltered prefix before
        # each descending event. Only a bare chart covers a required triple.
        (i, a), (j, b), (k, c) = history[::-1]
        ends = (i + len(marks[a][0]), j + len(marks[b][0]), k + len(marks[c][0]))
        if i == 0 and ends[0] <= j and ends[1] <= k and ends[2] == len(path):
            covered[a,b,c].add((path[ends[0]:j], path[ends[1]:k]))

    for a, b, c in product(specs, repeat=3):
        first = poles[a][1], poles[b][0]
        second = poles[b][1], poles[c][0]
        some_left, some_right = (gap_outside_dictionary(edges, *uv, set()) for uv in (first, second))
        if some_left is None or some_right is None:
            continue
        choices = covered[a,b,c]
        lefts = {left for left, _ in choices}
        missing = gap_outside_dictionary(edges, *first, lefts)
        if missing is not None:
            return (a, b, c), (missing, some_right)
        for left in sorted(lefts):
            rights = {right for gap, right in choices if gap == left}
            missing = gap_outside_dictionary(edges, *second, rights)
            if missing is not None:
                return (a, b, c), (left, missing)
    return None


def positive_moves(word):
    for i, (x,y) in enumerate(zip(word,word[1:])):
        if abs(x-y) > 1:
            yield word[:i] + (y,x) + word[i+2:]
        if i+2 < len(word) and word[i+2] == x and abs(x-y) == 1:
            yield word[:i] + (y,x,y) + word[i+3:]


def check_braids():
    readings = groups = 0
    for rules, gaps in [
        ((('a','',''),)*4, ('','','')),
        ((('a','f',''), ('b','','f'), ('a','f',''), ('b','','f')), ('','','')),
        ((('a','f','ff'),)*4, ('','f','')),
    ]:
        chart = Chart(rules,gaps)
        first = chart.reading((3,2,1,0))
        marks = {n:(s,t) for n,s,t in rules}
        level = {():first}
        for _ in range(7):
            fibres = defaultdict(set)
            for word, state in level.items():
                fibres[braid_image(4,word)].add(word)
            for fibre in fibres.values():
                rep = next(iter(fibre))
                seen = {rep}
                pending = [rep]
                while pending:
                    for w in positive_moves(pending.pop()):
                        assert w in level and level[w] == level[rep]
                        if w not in seen:
                            pending.append(w)
                            seen.add(w)
                assert seen == fibre
                groups += 1
            readings += len(level)
            level = {w+(p,): t for w,s in level.items() for p in (1,2,3)
                     if (t := exchange_at(s,p-1,marks)) is not None}
    return readings, groups


def check_presentations():
    # On a point with two scalar names each of the eight bare triples has
    # different descending history. Test every subset of the eight returns.
    words = list(product('ab',repeat=3))
    turns = [[0, '', [[0,n] for n in w[::-1]], [2,1,2], [1,2,1]] for w in words]
    for mask in range(1 << len(words)):
        chosen = {i for i in range(len(words)) if mask & (1<<i)}
        missing = certify(dict(edges={}, rules={n:[0,'',''] for n in 'ab'},
                               attachments=[turns[i] for i in sorted(chosen)]))
        if len(chosen) == len(words):
            assert missing is None
        else:
            word, gaps = missing
            assert words.index(word) not in chosen and gaps == ('','')
    # A nonempty gap may range over infinitely many paths. The reported
    # missing pair must itself be a chart outside the supplied dictionary.
    for limit in range(1,7):
        declarations = [[0,'f'*i,[[i,'a'],[0,'a'],[0,'a']],[2,1,2],[1,2,1]]
                        for i in range(limit)]
        word, gaps = certify(dict(edges={'f':[0,0]}, rules={'a':[0,'','']}, attachments=declarations))
        assert word == ('a','a','a') and (gaps[0] or len(gaps[1]) >= limit)
    # Distinct gap paths spanning an acyclic object graph, with one
    # separate generator on each active edge. Check all four possible gap pairs.
    edges = {'a':[0,1],'b':[1,2],'c':[2,3],'d':[3,4],'e':[4,5],'B':[1,2],'D':[3,4]}
    base = dict(edges=edges,rules={'u':[0,'a','a'],'v':[2,'c','c'],'w':[4,'e','e']})
    options = list(product('bB','dD'))
    for mask in range(16):
        attachments = [[0,'a'+l+'c'+r+'e',[[4,'w'],[2,'v'],[0,'u']],[2,1,2],[1,2,1]]
                       for j,(l,r) in enumerate(options) if mask & (1<<j)]
        missing = certify(dict(**base,attachments=attachments))
        assert (missing is None) == (mask == 15)
        if missing:
            assert missing[0] == ('u','v','w') and not mask & (1 << options.index(missing[1]))
    return 278


def raw_cube_contexts():
    point = (STAR,)
    id_x = identity(point, v(0))
    scalar = arr(infer(point, id_x), id_x, id_x)
    ctx = point + (scalar,) * 4
    p, q, ty = cube_terms(ctx, v(1), v(2), v(3))
    ctx += (arr(ty, q, p),)
    emitter = Emitter()
    emitter.check_type('reverse', ctx, v(5), arr(ty, q, p))
    for left in (False, True):
        pole = src(ctx, src(ctx, p)) if left else tgt(ctx, tgt(ctx, p))
        enter = head(point, pole, id_x)
        leave = head(point, id_x, pole)
        fourth = composite(ctx, 1, [enter, v(4), leave])
        def beside(term):
            return comp2(ctx, 1, fourth, term) if left else comp2(ctx, 1, term, fourth)
        expected = arr(infer(ctx, beside(q)), beside(q), beside(p))
        result = beside(v(5))
        assert infer(ctx, result) == expected
        emitter.check_type('prefix' if left else 'suffix', ctx, result, expected)
    return emitter


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--presentation', type=Path, help='JSON containing edges, rules, and attachments')
    parser.add_argument('--agda', type=Path, help='emit the raw contextual cube returns')
    args = parser.parse_args()
    if args.presentation:
        try:
            missing = certify(json.loads(args.presentation.read_text()))
        except (ValueError, KeyError) as error:
            parser.error(str(error))
        print('all old 4-types reflect' if missing is None else f'missing bare cube {missing}')
        return
    emitter = raw_cube_contexts()
    if args.agda:
        module = emitter.module(args.agda.stem, 'Literal contextual cube reverses.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n', 'open import CaTTExp.Gray.Pure\n'))
    readings, fibres = check_braids()
    print(f'{readings:,} typed crossing words, {fibres:,} independently compared positive braid classes.')
    print(f'{check_presentations()} finite attachment dictionaries checked.')


if __name__ == '__main__':
    main()
