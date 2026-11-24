"""Decide supported lifts of a specified rank-two insertion normal form.

The one-object backend accepts single-letter contextual rules for generators
with identity image. Every other generator may project to a composite.
"""
from collections import defaultdict
from functools import cache
from itertools import product

from semistrict_surface_two_cell_lifts import atom, factor_operations, horizontal, ident, vertical


class Language:
    """A finite labelled graph with chosen starts and ends. None denotes epsilon."""

    def __init__(self, starts, finals, edges):
        self.starts, self.finals = frozenset(starts), frozenset(finals)
        self.edges = frozenset(edges)
        self.next = defaultdict(set)
        self.states = set(self.starts | self.finals)
        for p, a, q in self.edges:
            self.next[p, a].add(q)
            self.states.update((p, q))

    def read(self, starts, word):
        states = set(starts)
        for a in word:
            states = {q for p in states for q in self.next[p, a]}
        return states

    def reverse_determinize(self):
        """Subset construction on the reversed graph, including epsilon closure."""
        incoming = defaultdict(lambda: defaultdict(set))
        for p, a, q in self.edges:
            incoming[q][a].add(p)

        def closure(states):
            seen, todo = set(states), list(states)
            while todo:
                for p in incoming[todo.pop()].get(None, ()):
                    if p not in seen:
                        seen.add(p)
                        todo.append(p)
            return frozenset(seen)

        start = closure(self.finals)
        ids, todo, finals, edges = {start: 0}, [start], set(), []
        while todo:
            states = todo.pop()
            if states & self.starts:
                finals.add(ids[states])
            moves = defaultdict(set)
            for q in states:
                for a, ps in incoming[q].items():
                    if a is not None:
                        moves[a].update(ps)
            for a, ps in moves.items():
                succ = closure(ps)
                if succ not in ids:
                    ids[succ] = len(ids)
                    todo.append(succ)
                edges.append((ids[states], a, ids[succ]))
        return Language([0], finals, edges)

    def compact(self):
        return self.reverse_determinize().reverse_determinize()

    def between(self, starts, finals):
        return Language(starts, finals, self.edges).compact()

    def accepts(self, word):
        return bool(self.read(self.starts, word) & self.finals)


def singleton(word):
    return Language([0], [len(word)], [(i, a, i+1) for i, a in enumerate(word)])


def alternatives(products):
    starts, finals, edges = set(), set(), []
    offset = 0
    for factors in products:
        previous = set()
        for i, machine in enumerate(factors):
            renaming = {p: offset+j for j, p in enumerate(machine.states)}
            offset += len(renaming)
            initial = {renaming[p] for p in machine.starts}
            if i == 0:
                starts.update(initial)
            edges.extend((p, None, q) for p in previous for q in initial)
            edges.extend((renaming[p], a, renaming[q]) for p, a, q in machine.edges)
            previous = {renaming[q] for q in machine.finals}
        finals.update(previous)
    return Language(starts, finals, edges).compact()


def project_filter(machine, images, word):
    states = [(p, i) for p in machine.states for i in range(len(word)+1)]
    edges = [((p,i), a, (q,i+len(images[a]))) for p, i in states for a in images
             if word.startswith(images[a], i) for q in machine.next[p,a]]
    return Language([(p,0) for p in machine.starts],
                    [(q,len(word)) for q in machine.finals], edges).compact()


def erased_pre(machine, rules):
    """Saturate inverse images under contextual a -> word (including empty)."""
    graph = Language(machine.starts, machine.finals, machine.edges)
    edges = set(machine.edges)
    while True:
        additions = {(p, a, q) for a, word in rules for p in graph.states
                     for q in graph.read([p], word)} - edges
        if not additions:
            return graph.compact()
        edges.update(additions)
        graph = Language(machine.starts, machine.finals, edges)


def predecessors(goal, upper_atoms, images, lower_atoms, target):
    """Return a DFA for all source paths lifting goal into the target DFA."""
    ends, cuts = factor_operations(upper_atoms)
    rules = []
    macros = defaultdict(list)
    for left, right, value in lower_atoms:
        boundary = tuple(''.join(images[a] for a in w) for w in (left, right))
        if boundary != ends(value):
            raise ValueError('Mismatched projected boundary')
        if value[0] == 'id':
            if len(left) != 1:
                raise ValueError('Erased rules require single-letter left sides')
            rules.append((left, right))
        else:
            macros[value].append((left,right))

    @cache
    def compile_value(value):
        if value[0] == 'id':
            return ('identity', value[1])
        branches = [('macro', l, r) for l, r in macros[value]]
        for op, l, r in cuts(value):
            if value not in (l,r):
                branches.append((op, compile_value(l), compile_value(r)))
        core = ('union', tuple(branches))
        silent = ('silent',)
        return ('sandwich', ('h', silent, ('h', core, silent)))

    def pre(expr, machine):
        if not machine.finals:
            return machine
        tag, *args = expr
        if tag == 'identity':
            return project_filter(erased_pre(machine, rules), images, args[0])
        if tag == 'silent':
            return project_filter(machine, images, '')
        if tag == 'macro':
            return singleton(args[0]) if machine.accepts(args[1]) else alternatives([])
        if tag == 'union':
            return alternatives((pre(branch, machine),) for branch in args[0])
        if tag == 'v':
            return pre(args[0], pre(args[1], machine))
        if tag == 'h':
            choices = []
            for i in machine.states:
                l = pre(args[0], machine.between(machine.starts, [i]))
                if l.finals:
                    r = pre(args[1], machine.between([i], machine.finals))
                    if r.finals:
                        choices.append((l, r))
            return alternatives(choices)
        assert tag == 'sandwich'
        return erased_pre(pre(args[0], erased_pre(machine, rules)), rules)

    return pre(compile_value(goal), target.compact())


def check():
    from semistrict_surface_two_cell_lifts import lift_relation

    # Infinite erased fibre: S derives a^n b^n, so no rational relation
    # represents this environment. The inverse image of each regular test is regular.
    images = {x:'' for x in 'Sab'}
    growth = [('S','aSb',ident('')), ('S','',ident(''))]
    checked = 0
    for i, j in product(range(8),repeat=2):
        target = 'a'*i+'b'*j
        assert predecessors(ident(''), {}, images, growth, singleton(target)).accepts('S') == (i==j)
        checked += 1
    regular = Language([0], [1], [(0,'a',1), (1,'b',0)])
    pre = predecessors(ident(''), {}, images, growth, regular)
    assert pre.accepts('Sa') and not pre.accepts('S')

    # A visible edge can carry arbitrary erased padding. Two independent
    # actions must have the requested horizontal class, with a vertical seam above it.
    x,y,z = map(atom, 'XYZ')
    images = images | {'f':'u','g':'v','h':'w'}
    upper = {'X':('u','v'), 'Y':('u','v'), 'Z':('v','w')}
    live = [('af','g',x), ('fb','g',y), ('g','h',z)]
    first = horizontal([x,y])
    goal = vertical([first,horizontal([z,z])], 'uu')
    path = predecessors(goal,upper,images,growth+live,singleton('bhha'))
    assert path.accepts('ba'+'ff'+'ba')
    assert not path.accepts('bffa')
    macro = predecessors(goal,upper,images,growth+live+[('ff','gg',first)],singleton('bhha'))
    assert macro.accepts('bffa')
    opposite = vertical([horizontal([y,x]),horizontal([z,z])], 'uu')
    assert not predecessors(opposite,upper,images,growth+live,singleton('bhha')).accepts('baffba')

    # Compare every queried endpoint against independent finite-fibre saturation.
    images = {'f':'u','p':'u','g':'v','h':'w'}
    live = [('p','g',x), ('f','g',y), ('g','h',z), ('pf','gg',first)]
    rules = [('f','p',ident('u'))] + live
    checked_pairs = 0
    for t, srcs, dests in [(first, 'fp','g'), (goal,'fp','h'), (opposite,'fp','h')]:
        reference = lift_relation(t, upper, images, rules)
        for right in map(''.join,product(dests,repeat=2)):
            result = predecessors(t,upper,images,rules,singleton(right))
            for left in map(''.join,product(srcs,repeat=2)):
                assert result.accepts(left) == ((left,right) in reference)
                checked_pairs += 1
    # Compare infinite path fibres at fixed endpoints by a different finite
    # calculation: here all silent rules preserve length, and all live rules
    # consume exactly one letter per upper atomic occurrence.
    from collections import deque
    images = {'a':'','b':'','f':'u','g':'v'}
    flip = [('a','b',ident(''))]
    edges = [('af','bg',x), ('fb','ga',y)]
    goal = horizontal([x,y])
    size = 5
    # Every lower path in a witness has the same length, because all four
    # endpoint words of the available rules have matching lengths.
    words = [''.join(w) for w in product(images, repeat=size)]
    def project(w):
        return ''.join(images[e] for e in w)
    sources = [w for w in words if project(w)=='uu']
    targets = [w for w in words if project(w)=='vv']

    def outgoing(word, positions, applied):
        for i, e in enumerate(word):
            if e == 'a':
                yield word[:i]+'b'+word[i+1:], applied
        for j, (left, right, _) in enumerate(edges):
            if j in applied:
                continue
            pos = positions[j] - left.index('f')
            if pos >= 0 and word.startswith(left, pos):
                yield word[:pos]+right+word[pos+len(left):], applied | {j}

    # The two visible steps must have disjoint redex intervals at a common
    # horizontal cut. Once a source's f positions are fixed, each live redex
    # occupies a fixed interval; overlapping live redexes can never certify H.
    answers = set()
    for w in sources:
        positions = [i for i,e in enumerate(w) if e=='f']
        if positions[0] == 0 or positions[1] == size-1:
            continue
        initial = (w, frozenset())
        queue, seen = deque([initial]), {initial}
        while queue:
            word, applied = queue.popleft()
            if len(applied) == 2:
                answers.add((w,word))
            for nxt in outgoing(word,positions,applied):
                if nxt not in seen:
                    seen.add(nxt)
                    queue.append(nxt)
    for w in targets:
        language = predecessors(goal,upper,images,flip+edges,singleton(w))
        assert {s for s in sources if language.accepts(s)} == {s for s,t in answers if t==w}
    assert answers
    print(f'{len(sources)*len(targets)} infinite-fibre endpoints checked by positioned rewriting')
    print(f'{checked} balanced-word targets, a regular target, infinite-fibre mixed classes, '
          f'and {checked_pairs} independent finite-fibre endpoint comparisons passed')


def raw_example(binary):
    from pathlib import Path
    from tempfile import TemporaryDirectory
    from semistrict_surface_local_generators import Checker, FULL, WIDTH_ONE

    row, args = '[[a],[b],[c],[d]]', '(a,b,c,d)'
    extra = """
def both [[a],[b],[c],[d]] = h(h(a,b),h(c,d))
def third = coh [ [[a],[b],[c],[d]] : initial(a,b,c,d) -> both(a,b,c,d) ]
def third_back = coh [ [[a],[b],[c],[d]] : both(a,b,c,d) -> initial(a,b,c,d) ]
def zz [[a],[b],[c],[d]] = comp[third(a,b,c,d),third_back(a,b,c,d)]
def grow = coh [ [[a],[b],[c],[d]] : xx(a,b,c,d) -> comp[yy(a,b,c,d),xx(a,b,c,d),zz(a,b,c,d)] ]
def stop = coh [ [[a],[b],[c],[d]] : xx(a,b,c,d) -> id(initial(a,b,c,d)) ]
"""
    with TemporaryDirectory() as temp:
        root = Path(temp)
        checker = Checker(binary.resolve(), root)
        (root/'Grammar.catt').write_text('import RawRules\n'+extra)
        x, a, b = [name+args for name in ('xx','yy','zz')]
        unit = f'id(initial{args})'
        for mode in ((), WIDTH_ONE):
            checker.definitions(f'def growth {row} : {x} -> comp[{a},{x},{b}] = grow{args}\n'
                                f'def terminate {row} : {x} -> {unit} = stop{args}', mode, 'Grammar')
        for first, second in [(x,a), (a,b), (x,b), (x,unit)]:
            checker.equality(first,second,row,WIDTH_ONE,False,'Grammar')
        for name in ('grow','stop'):
            checker.equality(name+args, f'id({unit})', row, FULL, True, 'Grammar')
    print('Rice verified raw production types, distinct width-one paths and full erasure')


if __name__ == '__main__':
    from argparse import ArgumentParser
    from pathlib import Path

    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--rice', type=Path)
    options = parser.parse_args()
    check()
    if options.rice:
        raw_example(options.rice)
