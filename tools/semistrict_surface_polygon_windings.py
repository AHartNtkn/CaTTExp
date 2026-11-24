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
    tags = [[] for _ in names]
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
        else:
            gain = prism(word, nxt)
            if gain is not None:
                ordinal, tag = gain
                tags[names[ordinal]].append(tag)
        word = nxt
    if model.parse(source, word)[1] != end:
        raise ValueError('schedule changed the terminal history')
    return names, counts, [''.join(w) for w in tags]


def prism(word, nxt):
    """A prism increases one polygon's slot. The input crosses before or after it."""
    old = [(j, i) for j, (p, i) in enumerate(word) if p != 'swap']
    new = [(j, i) for j, (p, i) in enumerate(nxt) if p != 'swap']
    for ordinal, ((j, i), (k, t)) in enumerate(zip(old, new)):
        if i != t:
            if t != i + 1 or k == j:
                raise ValueError('invalid polygon transfer')
            return ordinal, 'L' if k < j else 'R'
    return None


def transfer_leq(u, v):
    """The prefix counts characterize exactly the directed swaps LR to RL."""
    if len(u) != len(v) or u.count('R') != v.count('R'):
        return False
    balance = 0
    for x, y in zip(u, v):
        balance += (y == 'R') - (x == 'R')
        if balance < 0:
            return False
    return True


def compare(model, source, faces):
    if model.attachments or len(faces) != 2:
        raise ValueError('supply two schedules over a positive 3-computad')
    a, b = [[tuple(map(tuple, w)) for w in face] for face in faces]
    if not a or not b or a[0] != b[0] or a[-1] != b[-1]:
        raise ValueError('schedules require common literal initial and terminal readings')
    x, u, left_tags = signature(model, source, a)
    y, v, right_tags = signature(model, source, b)
    if x != y:
        return dict(surface=False, terminal_matchings=[x, y])
    delta = [(*pair, v[pair] - u[pair]) for pair in sorted(u.keys() | v.keys())
             if u[pair] != v[pair]]
    obstructed = any(d < 0 or d % 2 for _, _, d in delta)
    paired = {i for p, q, d in delta if d > 0 for i in (p, q)}
    blocked = [i for i in range(len(x))
               if i not in paired and not transfer_leq(left_tags[i], right_tags[i])]
    return dict(surface=False if obstructed or blocked else True if a == b else None,
                terminal_matching=x, pair_differences=delta,
                transfer_words=list(zip(left_tags, right_tags)), blocked_transfers=blocked)


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


def middle_faces(a, b, left, right):
    # Three disjoint spatial windows; the middle polygon can split or merge.
    marks = {x: (x, x) for x in 'fgh'}
    mid = ((0, 'g'),)
    model = Movies(Presentation({x: (i, i+1) for i, x in enumerate('fgh')}, marks,
                                [Rule('g', mid*a, mid*b)]), 'fgh')
    source = ((2, 'h'),)*right + ((1, 'g'),)*a + ((0, 'f'),)*left

    def cross(i, x, y):
        return steps(rectangle(i, x, y))

    first = cross(0, right, a) + ((0, 0),) + cross(b, right, left) + cross(0, b, left)
    last = cross(right, a, left) + cross(0, right, left) + ((0, left+right),) + cross(left, right, b)
    faces = []
    for negative in (True, False):
        pattern = 'L'*right + 'R'*left if negative else 'R'*left + 'L'*right
        todo = deque([first])
        parent = {first: None}
        while todo:
            word = todo.popleft()
            if word == last:
                route = []
                while word is not None:
                    route.append(word)
                    word = parent[word]
                faces.append(route[::-1])
                break
            h, windows = read(model, source, word)
            k, slot = next((k, i) for k, (p, i) in enumerate(word) if p != 'swap')
            for nxt in raw_updates(model, word, h, windows, 1):
                if nxt in parent:
                    continue
                gain = prism(word, nxt)
                if gain and gain[1] != pattern[slot]:
                    continue
                # The middle tensor has cubes on the target phase in its
                # negative face and on the source phase in its positive face.
                if gain is None and len(word) == len(nxt):
                    changes = [j for j in range(len(word)) if word[j] != nxt[j]]
                    if len(changes) == 3 and (changes[0] > k) != negative:
                        continue
                parent[nxt] = word
                todo.append(nxt)
        else:
            raise AssertionError('missing three-factor face')
    return model, source, faces


def middle_checks():
    cases = list(product((1, 2), (1, 2), (1,), (1,)))
    cases += [(3, 1, 1, 1), (1, 3, 1, 1), (1, 1, 2, 1), (1, 1, 1, 2)]
    nsteps = 0
    for a, b, left, right in cases:
        model, source, faces = middle_faces(a, b, left, right)
        u, v = 'L'*right + 'R'*left, 'R'*left + 'L'*right
        fwd, rev = (compare(model, source, fs) for fs in (faces, faces[::-1]))
        assert fwd['surface'] is None and fwd['pair_differences'] == []
        assert fwd['transfer_words'] == [(u, v)]
        assert rev['surface'] is False and rev['blocked_transfers'] == [0]
        nsteps += sum(len(path)-1 for path in faces)
    # A rectangle may change its two incident words. It cannot cover a
    # backwards middle move on a third occurrence of the very same polygon.
    model, src, (negative, positive) = instance(1, 1, 1, 1, repeat=True)
    _, _, (lr, rl) = middle_faces(1, 1, 1, 1)
    def joint(x, y):
        return [w + y[0] for w in x] + [x[-1] + w for w in y[1:]]
    mixed = compare(model, src + src[:1], [joint(negative, rl), joint(positive, lr)])
    assert mixed['pair_differences'] == [(0, 1, 2)] and mixed['blocked_transfers'] == [2]
    assert mixed['surface'] is False
    shuffle_queries = 0
    for n in range(7):
        words = [''.join(w) for w in product('LR', repeat=n)]
        for start in words:
            reached = {start}
            stack = [start]
            while stack:
                w = stack.pop()
                for k in range(n-1):
                    if w[k:k+2] == 'LR':
                        t = w[:k]+'RL'+w[k+2:]
                        if t not in reached:
                            reached.add(t)
                            stack.append(t)
            for target in words:
                assert transfer_leq(start, target) == (target in reached)
                shuffle_queries += 1
    return dict(middle_queries=2*len(cases), middle_literal_steps=nsteps,
                shuffle_order_checks=shuffle_queries, mixed_rectangle_middle=1)


def checks():
    cases = list(product((1, 2), repeat=4)) + [(3, 1, 1, 3), (1, 3, 3, 1), (3, 2, 2, 1)]
    sizes = []
    for repeat, arities in ([(False, arities) for arities in cases] +
                            [(True, (a, b, a, b)) for a, b in product((1, 2), repeat=2)]):
        model, source, faces = instance(*arities, repeat=repeat)
        for pad in (0, 2):
            inp = ((0, 's'),)*pad + source
            paths = [[tuple((p, i+pad) for p, i in w) for w in face] for face in faces]
            forward = compare(model, inp, paths)
            assert forward['surface'] is None and forward['terminal_matching'] == [1, 0]
            assert forward['pair_differences'] == [(0, 1, 2)]
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
                maximum_face_length=max(sizes), **middle_checks())


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
