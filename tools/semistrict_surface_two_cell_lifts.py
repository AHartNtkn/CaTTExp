"""Compute exact images at a two-cell of a one-object finite presentation.

Edge names are single characters and their images are nonempty words. The
proof in the note also allows multiple objects and finite empty-edge fibres.
"""
from collections import defaultdict
from functools import cache


def ident(word):
    return ('id', word)


def atom(name):
    return ('atom', name)


def horizontal(parts):
    entries = []
    for term in parts:
        tag, data = term
        if tag == 'h':
            entries.extend(data)
        elif tag == 'id':
            entries.extend(ident(letter) for letter in data)
        else:
            entries.append(term)
    if all(t[0] == 'id' for t in entries):
        return ident(''.join(t[1] for t in entries))
    return entries[0] if len(entries) == 1 else ('h', tuple(entries))


def vertical(parts, empty_path):
    entries = []
    for term in parts:
        if term[0] == 'v':
            entries.extend(term[1])
        elif term[0] != 'id':
            entries.append(term)
    if not entries:
        return ident(empty_path)
    return entries[0] if len(entries) == 1 else ('v', tuple(entries))


def lift_relation(goal, upper_atoms, edge_map, lower_atoms):
    """Return all lower path pairs realizing exactly the specified upper value."""
    if any(len(e) != 1 or not image for e, image in edge_map.items()):
        raise ValueError('Require single lower edge names with nonempty images')

    def project(path):
        return ''.join(edge_map[e] for e in path)

    @cache
    def ends(t):
        tag, data = t
        if tag == 'id':
            return data, data
        if tag == 'atom':
            return upper_atoms[data]
        paths = [ends(child) for child in data]
        if tag == 'h':
            return tuple(''.join(pair[i] for pair in paths) for i in (0, 1))
        if tag != 'v' or any(a[1] != b[0] for a, b in zip(paths, paths[1:])):
            raise ValueError(f'Invalid vertical product {t}')
        return paths[0][0], paths[-1][1]

    def cuts(t):
        if t[0] == 'id':
            word = t[1]
            for i in range(len(word)+1):
                yield 'h', ident(word[:i]), ident(word[i:])
            yield 'v', t, t
            return
        rows = t[1] if t[0] == 'h' else (t,)
        for i in range(len(rows)+1):
            yield 'h', horizontal(rows[:i]), horizontal(rows[i:])
        steps = t[1] if t[0] == 'v' else (t,)
        source, target = ends(t)
        for i in range(len(steps)+1):
            yield 'v', vertical(steps[:i], source), vertical(steps[i:], target)

    @cache
    def colour(word):
        if not word:
            return ('',)
        return tuple(e+rest for e, image in edge_map.items() if word.startswith(image)
                     for rest in colour(word[len(image):]))

    work = [goal]
    split = {}
    while work:
        term = work.pop()
        if term not in split:
            split[term] = tuple(cuts(term))
            work.extend(child for _, l, r in split[term] for child in (l, r))

    relation = defaultdict(set)
    for term in split:
        if term[0] == 'id':
            relation[term].update((p,p) for p in colour(term[1]))
    for left, right, term in lower_atoms:
        if (project(left), project(right)) != ends(term):
            raise ValueError('Generator assignment does not preserve its boundary')
        if term in split:
            relation[term].add((left,right))

    changed = True
    while changed:
        changed = False
        for value, options in split.items():
            additions = set()
            for op, left, right in options:
                for a, b in relation[left]:
                    for c, d in relation[right]:
                        if op == 'h':
                            additions.add((a+c, b+d))
                        elif b == c:
                            additions.add((a,d))
            if additions - relation[value]:
                relation[value].update(additions)
                changed = True
    return relation[goal]


def check():
    from itertools import product
    letters = {'x':'f', 'y':'f', 'd':'ff'}
    upper = {'A':('f','ff'), 'B':('ff','f'), 'C':('f','f')}
    a,b,c = map(atom, 'ABC')
    erased = [('x','y',ident('f')), ('xx','d',ident('ff'))]
    live = [('y','xx',a), ('d','x',b), ('y','y',c)]
    # Independent contextual reachability for an erased upper 2-cell.
    tested = 0
    for size in range(7):
        word = 'f'*size
        result = lift_relation(ident(word), upper, letters, erased+live)
        paths = {''.join(path) for n in range(size+1) for path in product(letters,repeat=n)
                 if ''.join(letters[e] for e in path) == word}
        expected = set()
        for source in paths:
            todo = [source]
            seen = {source}
            while todo:
                curr = todo.pop()
                for left, right, _ in erased:
                    for i in range(len(curr)-len(left)+1):
                        if curr.startswith(left, i):
                            step = curr[:i] + right + curr[i+len(left):]
                            if step not in seen:
                                seen.add(step)
                                todo.append(step)
            expected.update((source, target) for target in seen)
        assert result == expected
        tested += len(paths)**2
    first, last = horizontal([a,c]), horizontal([b,c])
    goal = vertical([first,last], 'ff')
    answer = lift_relation(goal, upper, letters, erased+live)
    assert ('xx','xy') in answer and ('d','xy') not in answer
    with_macro = lift_relation(goal, upper, letters, erased+live+[('d','xxy',first)])
    assert ('d','xy') in with_macro
    print(f'{tested} identity-fibre path pairs cross-checked; '
          'a mixed horizontal/vertical class separates a composite generator assignment')


if __name__ == '__main__':
    check()
