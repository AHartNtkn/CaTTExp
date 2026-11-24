"""Obstruct degree-five surface fillers by following individual polygon occurrences."""
from argparse import ArgumentParser
from collections import Counter, deque
from itertools import permutations, product
import json
from pathlib import Path

from semistrict_surface_polygon_cabling import rectangle
from semistrict_surface_raw_movie_graph import raw_updates, read, steps
from semistrict_surface_signed_width_two import Movies, Presentation, Rule


def exchange(word, nxt, windows):
    """Return the polygon ordinal and sign of a strict polygon/polygon swap."""
    ordinal = 0
    for k, (p, i) in enumerate(word[:-1]):
        if p == 'swap':
            continue
        q, j = word[k + 1]
        if q != 'swap':
            a, b = windows[k]
            c, d = windows[k + 1]
            if j + c <= i:
                pair, sign = ((q, j), (p, i + d - c)), -1
            elif j >= i + b:
                pair, sign = ((q, j + a - b), (p, i)), 1
            else:
                pair, sign = (), 0
            if sign and word[:k] + pair + word[k + 2:] == nxt:
                return ordinal, sign
        ordinal += 1
    return None


def signature(model, source, face):
    if not face:
        raise ValueError('a schedule requires an initial reading')
    word = face[0]
    _, end = model.parse(source, word)
    names = list(range(sum(p != 'swap' for p, _ in word)))
    counts = Counter()
    for nxt in face[1:]:
        histories, windows = read(model, source, word)
        if nxt not in raw_updates(model, word, histories, windows, len(names)):
            raise ValueError('schedule contains a non-native step')
        moved = exchange(word, nxt, windows)
        if moved is not None:
            k, sign = moved
            pair = tuple(sorted(names[k:k + 2]))
            counts[pair] += sign
            names[k:k + 2] = reversed(names[k:k + 2])
        word = nxt
    if model.parse(source, word)[1] != end:
        raise ValueError('schedule changed the terminal history')
    return names, counts


def compare(model, source, faces):
    if model.attachments or len(faces) != 2:
        raise ValueError('supply two schedules over a positive 3-computad')
    a, b = [[tuple(map(tuple, w)) for w in face] for face in faces]
    if not a or not b or a[0] != b[0] or a[-1] != b[-1]:
        raise ValueError('schedules require common literal initial and terminal readings')
    x, u = signature(model, source, a)
    y, v = signature(model, source, b)
    if x != y:
        return dict(surface=False, terminal_matchings=[x, y])
    delta = [(*pair, v[pair] - u[pair]) for pair in sorted(u.keys() | v.keys())
             if u[pair] != v[pair]]
    obstructed = any(d < 0 or d % 2 for _, _, d in delta)
    return dict(surface=False if obstructed else True if a == b else None,
                terminal_matching=x, pair_differences=delta)


def native_face(model, source, first, last, sign):
    """Find a literal prism route using the chosen corner of a block rectangle."""
    start = first, False
    todo = deque([start])
    parent = {start: None}
    while todo:
        word, crossed = state = todo.popleft()
        if crossed and word == last:
            path = []
            while state is not None:
                path.append(state[0])
                state = parent[state]
            return path[::-1]
        h, w = read(model, source, word)
        slots = [i for p, i in word if p != 'swap']
        for nxt in raw_updates(model, word, h, w, 2):
            move = exchange(word, nxt, w)
            if move is not None and (crossed or move[1] != sign):
                continue
            if move is None:
                # Q then P initially, P then Q after the commutation.
                # In the negative corner Q moves first; in the positive P does.
                fixed = 1 if sign < 0 else 0
                if [i for p, i in nxt if p != 'swap'][fixed] != slots[fixed]:
                    continue
            key = nxt, crossed or move is not None
            if key not in parent:
                parent[key] = state
                todo.append(key)
    raise AssertionError('missing rectangle face')


def instance(a, b, c, d, repeat=False):
    s = ((0, 's'),)
    rules = [Rule('', s*a, s*b), Rule('', s*c, s*d)]
    if repeat:
        assert (a, b) == (c, d)
        rules = rules[:1]
    q = len(rules)-1
    model = Movies(Presentation({}, {'s': ('', '')}, rules, {'s': 0}), '')
    source = s*(a+c)
    first = ((q, 0),) + steps(rectangle(0, d, a)) + ((0, 0),)
    last = ((0, c),) + steps(rectangle(0, c, b)) + ((q, b),)
    faces = [native_face(model, source, first, last, sign) for sign in (-1, 1)]
    return model, source, faces


def transport_checks():
    # Six serializations of three disjoint boxes, with a split and a merge.
    # Check the cocycle at all triples against literal raw exchanges.
    s = ((0, 's'),)
    sizes = ((1, 2), (2, 1), (1, 1))
    rules = [Rule('', s*a, s*b) for a, b in sizes]
    model = Movies(Presentation({}, {'s': ('', '')}, rules, {'s': 0}), '')
    source = s*4
    orders = list(permutations(range(3)))

    def word(order):
        widths = [a for a, _ in sizes]
        reading = []
        for box in order:
            reading.append((box, sum(widths[:box])))
            widths[box] = sizes[box][1]
        return tuple(reading)

    def path(order, end):
        order = list(order)
        route = [word(order)]
        for pos, box in enumerate(end):
            j = order.index(box)
            while j > pos:
                order[j-1:j+1] = reversed(order[j-1:j+1])
                route.append(word(order))
                j -= 1
        return route

    for start, middle, end in product(orders, repeat=3):
        direct = path(start, end)
        via = path(start, middle) + path(middle, end)[1:]
        assert compare(model, source, [direct, via])['pair_differences'] == []
    return len(orders)**3


def checks():
    cases = list(product((1, 2), repeat=4)) + [(3, 1, 1, 3), (1, 3, 3, 1), (3, 2, 2, 1)]
    sizes = []
    for repeat, arities in ([(False, arities) for arities in cases] +
                            [(True, (a, b, a, b)) for a, b in product((1, 2), repeat=2)]):
        model, source, faces = instance(*arities, repeat=repeat)
        for pad in (0, 2):
            inp = ((0, 's'),)*pad + source
            paths = [[tuple((p, i+pad) for p, i in w) for w in face] for face in faces]
            assert compare(model, inp, paths) == dict(surface=None, terminal_matching=[1, 0],
                                                       pair_differences=[(0, 1, 2)])
            assert compare(model, inp, paths[::-1])['surface'] is False
            sizes.extend(len(path)-1 for path in paths)
    model, source, (neg, pos) = instance(1, 1, 1, 1, repeat=True)
    def paste(x, y):
        return [w + y[0] for w in x] + [x[-1] + w for w in y[1:]]
    x, y = paste(neg, pos), paste(pos, neg)
    for faces in ((x, y), (y, x)):
        result = compare(model, source, faces)
        assert result['surface'] is False
        assert sorted(n for _, _, n in result['pair_differences']) == [-2, 2]
    return dict(native_queries=len(sizes), literal_steps=sum(sizes),
                opposite_signed_pairs=2, serialization_triangles=transport_checks(),
                maximum_face_length=max(sizes))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--query', type=Path)
    args = parser.parse_args()
    if args.query:
        q = json.loads(args.query.read_text())
        if q.get('attachments'):
            raise ValueError('expected a 3-computad')
        rules = [Rule(r['path'], tuple(map(tuple, r['source'])), tuple(map(tuple, r['target'])))
                 for r in q['rules']]
        model = Movies(Presentation(q['edges'], q['marks'], rules, q.get('mark_roots')), q['start'])
        source = tuple(map(tuple, q['source']))
        model.pres.walk(model.start, source, q.get('vertex'))
        result = compare(model, source, q['four_faces'])
    else:
        result = checks()
    print(json.dumps(result))
