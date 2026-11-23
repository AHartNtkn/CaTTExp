"""Classify and solve contextual path rules for a specified bare Gray triple."""
from argparse import ArgumentParser
from collections import Counter
from itertools import product

from semistrict_surface_three_axis import successors
from semistrict_surface_three_axis_paths import Chart, check_chart


class PathProblem:
    def __init__(self, chart):
        self.chart = chart
        graph, self.count = check_chart(chart)
        self.graph = {u: dict(edges) for u, edges in graph.items()}
        self.start = chart.reading((2, 1, 0))
        self.end = chart.reading((0, 1, 2))
        reach = {}
        for u in graph:
            found = {u}
            pending = [u]
            while pending:
                for v in self.graph[pending.pop()].values():
                    if v not in found:
                        found.add(v)
                        pending.append(v)
            reach[u] = found
        components = {frozenset(v for v in reach[u] if u in reach[v]) for u in graph}
        cyclic = [part for part in components if any(v in part for u in part for v in self.graph[u].values())]
        self.start_cycle = self.end_cycle = self.internal = ()
        if not cyclic:
            assert self.count == 2
            self.kind = 'finite'
        elif any(sum(v in part for v in self.graph[u].values()) != 1 for part in cyclic for u in part):
            assert len(cyclic) == 1 and set(cyclic[0]) == set(graph)
            assert all(set(edges) == {1, 2} for edges in self.graph.values())
            self.kind = 'word'
        elif len(cyclic) == 1:
            self.kind = 'one counter'
            part, = cyclic
            assert self.start not in part and self.end not in part
            self.anchor = min(part)
            self.internal = self.cycle(self.anchor, part)
        else:
            self.kind = 'two counters'
            assert len(cyclic) == 2
            a, = [part for part in cyclic if self.start in part]
            b, = [part for part in cyclic if self.end in part]
            assert a != b
            self.start_cycle = self.cycle(self.start, a)
            self.end_cycle = self.cycle(self.end, b)

    def cycle(self, base, component):
        u = base
        word = []
        while True:
            (letter, u), = [(p, v) for p, v in self.graph[u].items() if v in component]
            word.append(letter)
            if u == base:
                return tuple(word)

    def states(self, u, word):
        states = [u]
        for letter in word:
            u = self.graph[u][letter]
            states.append(u)
        return states

    def contexts(self, u, v):
        """Minimal context paths after erasing cycles allowed in arbitrary contexts."""
        def walk(state, seen, word):
            if state == v:
                yield word
            for letter, dest in self.graph[state].items():
                if dest not in seen:
                    yield from walk(dest, seen | {dest}, word + (letter,))

        if not self.internal:
            yield from walk(u, {u}, ())
            return

        # Removing the anchor leaves an acyclic graph. Visit it at most once.
        def through_anchor(state, used, word):
            if state == v:
                yield word
            for letter, dest in self.graph[state].items():
                if dest != self.anchor or not used:
                    yield from through_anchor(dest, used or dest == self.anchor, word + (letter,))
        yield from through_anchor(u, u == self.anchor, ())

    def encode(self, word):
        if self.internal:
            visits = [i for i, u in enumerate(self.states(self.start, word)) if u == self.anchor]
            if not visits:
                return word, 0
            return word[:visits[0]] + word[visits[-1]:], len(visits) - 1
        left = right = 0
        while self.start_cycle and word[:len(self.start_cycle)] == self.start_cycle:
            word = word[len(self.start_cycle):]
            left += 1
        while self.end_cycle and word[-len(self.end_cycle):] == self.end_cycle:
            word = word[:-len(self.end_cycle)]
            right += 1
        return word, (left, right)

    def whisker(self, attachment, edges, pole):
        """All corridor placements of one declared atom at its strict source history."""
        origin, window, slots, left, right = attachment
        marks = {n: (s, t) for n, s, t in self.chart.rules}
        placements = set()
        for state in self.graph:
            path = self.chart.start_word()
            for i in range(len(state) + 1):
                if i + len(slots) > len(state):
                    break
                for offset in range(len(path) - len(window) + 1):
                    vertex = pole if offset == 0 else edges[path[offset-1]][1]
                    if vertex != origin or not path.startswith(window, offset):
                        continue
                    if state[i:i+len(slots)] != tuple((p+offset, n) for p, n in slots):
                        continue
                    l = tuple(x+i for x in left)
                    r = tuple(x+i for x in right)
                    try:
                        ldest = self.states(state, l)[-1]
                        rdest = self.states(state, r)[-1]
                    except KeyError:
                        # An old face outside the retained graph cannot be a subpath
                        # of a whole path at the specified boundary.
                        continue
                    if ldest != rdest:
                        raise ValueError('attachment has different target histories')
                    placements.add((state, l, r))
                if i < len(state):
                    pos, name = state[i]
                    before, after = marks[name]
                    path = path[:pos] + after + path[pos+len(before):]
        return placements

    def compile(self, rules):
        compiled = set()
        for state, l, r in rules:
            dest = self.states(state, l)[-1]
            if dest != self.states(state, r)[-1]:
                raise ValueError('the two faces must be parallel')
            for prefix in self.contexts(self.start, state):
                for suffix in self.contexts(dest, self.end):
                    exact = bool(self.internal and self.anchor not in self.states(self.start, prefix)
                                 and self.anchor not in self.states(dest, suffix))
                    compiled.add((self.encode(prefix + l + suffix), self.encode(prefix + r + suffix), exact))
        return compiled

    def decide(self, rules):
        if self.kind == 'word':
            raise ValueError('unrestricted attachments at this triple give the undecidable word case')
        p, q = (1, 2, 1), (2, 1, 2)
        compiled = self.compile([*rules, (self.start, p, q)])
        if self.internal:
            return one_counter(self.encode(q), self.encode(p), compiled)
        if self.kind == 'finite':
            return (self.encode(q), self.encode(p), False) in compiled
        from semistrict_surface_two_cut import controlled_reachable
        return controlled_reachable(self.encode(q), self.encode(p), {(l, r) for l, r, _ in compiled})


def one_counter(start, goal, transitions):
    """Balanced push/pop reachability, with exact threshold checks at stack height zero."""
    states = {start[0], goal[0]} | {q for (u, _), (v, _), _ in transitions for q in (u, v)}
    initial, final = object(), object()
    neutral, push, pop, zero = set(), set(), set(), set()

    def chain(u, guards, v):
        for edge in guards:
            middle = object()
            edge.add((u, middle))
            u = middle
        neutral.add((u, v))

    chain(initial, [push]*start[1], start[0])
    chain(goal[0], [pop]*goal[1], final)
    for (src, before), (dst, after), exact in transitions:
        chain(src, [pop]*before + ([zero] if exact else []) + [push]*after, dst)
    for edges in (neutral, push, pop, zero):
        states.update(q for edge in edges for q in edge)

    def close(edges):
        # Transitive closure by intermediate vertex, including empty walks.
        for v in states:
            ends = {t for s, t in edges if s == v}
            starts = {s for s, t in edges if t == v}
            edges.update((s, t) for s in starts for t in ends)

    balanced = neutral | {(u, u) for u in states}
    while True:
        close(balanced)
        nested = {(u, v) for u, a in push for b, v in pop if (a, b) in balanced}
        if nested <= balanced:
            break
        balanced.update(nested)
    balanced.update(zero)
    close(balanced)
    return (initial, final) in balanced


def bounded_paths(problem, start, limit):
    pending = [(start, ())]
    for _ in range(limit + 1):
        yield from pending
        pending = [(v, w + (p,)) for u, w in pending for p, v in problem.graph[u].items()]


def check_compilation(problem):
    wholes = [w for u, w in bounded_paths(problem, problem.start, 6) if u == problem.end]
    checks = 0
    for state in problem.graph:
        pieces = list(bounded_paths(problem, state, 2))
        for dest, l in pieces:
            for v, r in pieces:
                if dest != v or l == r:
                    continue
                compiled = problem.compile([(state, l, r)])
                for w in wholes:
                    actual = {problem.encode(w[:n] + r + w[n+len(l):])
                              for n, u in enumerate(problem.states(problem.start, w))
                              if u == state and w[n:n+len(l)] == l}
                    control, value = problem.encode(w)
                    output = set()
                    for (source, need), (target, give), exact in compiled:
                        if source != control:
                            continue
                        if problem.internal:
                            if value >= need and (not exact or value == need):
                                output.add((target, value - need + give))
                        else:
                            if all(i >= a for i, a in zip(value, need)):
                                output.add((target, tuple(i-a+b for i,a,b in zip(value,need,give))))
                    assert output == actual
                    checks += 1
    return checks


def shape_check():
    counts = Counter()
    examples = {}
    rewrites = 0
    for types in product(range(4), repeat=3):
        for names in ('000', '001', '010', '011', '012'):
            if any(names[i] == names[j] and types[i] != types[j] for i in range(3) for j in range(i)):
                continue
            for gaps in product(('', 'g'), repeat=2):
                rules = tuple((n, 's'*(b//2), 't'*(b%2)) for n, b in zip(names, types))
                chart = Chart(rules, gaps)
                problem = PathProblem(chart)
                assert (problem.kind == 'word') == (types == (0, 0, 0) and gaps == ('', ''))
                counts[problem.kind] += 1
                examples.setdefault(problem.kind, problem)
                if problem.kind in ('one counter', 'two counters'):
                    rewrites += check_compilation(problem)
                # Distinct, nonuniform positive lengths for each input/output block
                # (but repeated names have the same rule). Compare the full rooted
                # labelled graph via deterministic paired traversal.
                stretched = tuple((n, s*(2+int(n)), t*(5-int(n))) for n,s,t in rules)
                changed = PathProblem(Chart(stretched, (gaps[0]*3, gaps[1]*7)))
                mapping = {problem.start: changed.start}
                pending = [problem.start]
                while pending:
                    u = pending.pop()
                    a, b = problem.graph[u], changed.graph[mapping[u]]
                    assert a.keys() == b.keys()
                    for e, v in a.items():
                        if v in mapping:
                            assert mapping[v] == b[e]
                        else:
                            mapping[v] = b[e]
                            pending.append(v)
                assert len(mapping) == len(set(mapping.values())) == len(changed.graph)
                assert mapping[problem.end] == changed.end
    assert sum(counts.values()) == 464
    print(', '.join(f'{n} {k}' for k,n in sorted(counts.items())))
    print(f'{rewrites:,} contextual successor comparisons at cyclic decidable charts.')
    return examples


def check_arithmetic():
    # At the exact guard the return is enabled only at zero after consumption.
    for value, target, exact in product(range(5), range(5), (False, True)):
        rules = {(('a', 2), ('b', 1), exact)}
        assert one_counter(('a', value), ('b', target), rules) == (
            value >= 2 and (not exact or value == 2) and target == value-1)
    rules = {(('a', 1), ('a', 3), False), (('a', 15), ('b', 0), True)}
    assert one_counter(('a', 1), ('b', 0), rules)
    assert not one_counter(('a', 2), ('b', 0), rules)


def check_coloured_code():
    # Even runs induce the identity permutation. The odd-run trailer induces
    # the reversal while keeping the body free of both alternating triples.
    def block(i):
        return '11' + '2'*(2*i) + '11'
    def encode(word):
        return ''.join(block(i) for i in word)
    def marked(w):
        return block(4) + encode(w) + block(5) + '111222111'

    def act(order, word):
        order = list(order)
        for x in word:
            i = int(x)-1
            order[i], order[i+1] = order[i+1], order[i]
        return tuple(order)
    tests = 0
    words = [w for n in range(1,4) for w in product((2,3), repeat=n)]
    for w in words:
        assert act((0,1,2), marked(w)) == (2,1,0)
        assert '121' not in marked(w) and '212' not in marked(w)
        for l,r in product(words,repeat=2):
            possible = set(successors(marked(w), [(encode(l),encode(r))]))
            expected = {marked(w[:i]+r+w[i+len(l):]) for i in range(len(w)-len(l)+1) if w[i:i+len(l)] == l}
            assert possible == expected
            tests += 1
    print(f'{tests} permutation-preserving encodings checked.')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--chart', nargs=3, metavar='NAME:SOURCE:TARGET')
    parser.add_argument('--gaps', nargs=2, default=('', ''))
    parser.add_argument('--edge', action='append', default=[], metavar='LETTER:FROM:TO',
                        help='endpoints of a spatial edge (default: one object x)')
    parser.add_argument('--pole', default='x', help='initial object of the bare chart')
    parser.add_argument('--attach', action='append', default=[], metavar='OBJECT:PATH:SLOTS:LEFT:RIGHT',
                        help='strict faces; SLOTS is a comma-separated list such as 0@a,0@b,0@a')
    parser.add_argument('--rule', action='append', default=[], metavar='FROM:LEFT:RIGHT',
                        help='contextual rule; FROM is a crossing path from the descending history to its start')
    args = parser.parse_args()
    if args.chart:
        try:
            chart = Chart(tuple(tuple(word.split(':')) for word in args.chart), tuple(args.gaps))
            problem = PathProblem(chart)
            print(problem.kind)
            rules = set()
            edge_data = [spec.split(':') for spec in args.edge]
            edges = {c: (v, w) for c, v, w in edge_data}
            if not edge_data:
                alphabet = set(chart.start_word()) | {c for _, _, t in chart.rules for c in t}
                edges = {c: (args.pole, args.pole) for c in alphabet}
            for entry in args.attach:
                origin, window, slots, l, r = entry.split(':')
                slot_list = tuple((int(p), n) for p, n in
                                  (slot.split('@') for slot in slots.split(',') if slot))
                left, right = tuple(map(int, l)), tuple(map(int, r))
                if any(i < 1 or i >= len(slot_list) for i in left + right):
                    raise ValueError('crossing position outside the declared temporal width')
                rules.update(problem.whisker((origin, window, slot_list, left, right), edges, args.pole))
            for entry in args.rule:
                path, l, r = (tuple(map(int, w)) for w in entry.split(':'))
                rules.add((problem.states(problem.start, path)[-1], l, r))
            print('raw return exists' if problem.decide(rules) else 'raw return absent')
        except (KeyError, ValueError) as err:
            parser.error(str(err))
        return
    examples = shape_check()
    check_arithmetic()
    check_coloured_code()
    inside = PathProblem(Chart((('a', '', ''), ('b', '', 'f'), ('a', '', '')), ('', '')))
    # The second swap enters the internal loop. Add two turns there, then match
    # the WHOLE return path at a required number of turns, with no exterior slack.
    grow = (inside.states(inside.start, (2,))[-1], (1,), (1,1,1))
    for n in (4,5,8,9):
        exit_rule = (inside.start, (2,) + (1,)*n + (2,), (1,2,1))
        declarations = [("x", "", grow[0], grow[1], grow[2]),
                        ("x", "", *exit_rule)]
        anchored = set().union(*(inside.whisker(z, {'f': ('x','x')}, 'x') for z in declarations))
        assert anchored == {grow, exit_rule}
        assert inside.decide(anchored) == (n % 2 == 1)
    # The identity path remembers its vertex even when it has no edge name.
    separated = PathProblem(Chart((('a', '', ''), ('b', '', ''), ('b', '', '')), ('f','')))
    at_right = ('y', '', ((0,'b'), (0,'b')), (1,), ())
    assert separated.whisker(at_right, {'f': ('x','y')}, 'x')
    assert not separated.whisker(('x', *at_right[1:]), {'f': ('x','y')}, 'x')
    p, q = (1,2,1), (2,1,2)
    for kind, problem in examples.items():
        if kind != 'word':
            assert not problem.decide([])
            assert problem.decide([(problem.start, q, p)])


if __name__ == '__main__':
    main()
