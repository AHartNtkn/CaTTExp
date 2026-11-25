"""Replay pooled Petri-net cycles as positioned rewrites at a non-hub vertex."""
from collections import Counter
from dataclasses import dataclass
from itertools import product


# P,U go from x to the hub; R,S return to x. The other two edges loop at the hub.
lefts, rights = 'PU', 'RS'
returns = {'a', 'b'} | {r + l for r, l in product(rights, lefts)}
swaps = {(i + j, j + i) for i, j in product(returns, repeat=2) if i != j}


@dataclass(frozen=True)
class Loop:
    left: str
    bag: tuple
    right: str

    def word(self):
        return self.left + ''.join(self.bag) + self.right

    def port(self):
        return self.left + self.right


def word(path):
    return path.word() if path else ''


def blocks(path):
    tokens = []
    i = 1
    while i < len(path) - 1:
        length = 2 if path[i] in rights else 1
        token = path[i:i + length]
        assert token in returns
        tokens.append(token)
        i += length
    assert i == len(path) - 1
    return tokens


class Replay:
    def __init__(self, rules):
        self.rules = {(word(source), word(target)) for source, target in rules} | swaps
        self.current = ''
        self.steps = 0

    def rewrite(self, pos, lhs, rhs):
        assert (lhs, rhs) in self.rules and self.current.startswith(lhs, pos)
        # Match the vertex as well as the edge word, including for empty births.
        if (lhs, rhs) not in swaps:
            assert pos == 0 or self.current[pos - 1] in rights
        self.current = self.current[:pos] + rhs + self.current[pos + len(lhs):]
        self.steps += 1

    def permute(self, target):
        assert self.current[0] == target[0] and self.current[-1] == target[-1]
        source, desired = blocks(self.current), blocks(target)
        assert Counter(source) == Counter(desired)
        for i, token in enumerate(desired):
            j = source.index(token, i)
            while i < j:
                pos = 1 + sum(len(block) for block in source[:j - 1])
                a, b = source[j - 1:j + 1]
                self.rewrite(pos, a + b, b + a)
                source[j - 1:j + 1] = [b, a]
                j -= 1
        assert self.current == target

    def middle(self, run, start, finish, anchor, anchor_first):
        ports, bag = [start.port()], Counter(start.bag)
        def display(selected=None, spelling='', parked=None):
            pieces = [spelling if i == selected else port for i, port in enumerate(ports)]
            if selected == len(ports):
                pieces.append(spelling)
            stored = ''.join(sorted((bag if parked is None else parked).elements()))
            safe = anchor.left + stored + ''.join(anchor.bag) + anchor.right
            return safe + ''.join(pieces) if anchor_first else ''.join(pieces) + safe

        for source, target in run:
            index = ports.index(source.port()) if source else len(ports)
            consumed = Counter(source.bag if source else ())
            assert consumed <= bag
            parked = bag - consumed
            self.permute(display(index, word(source), parked))
            pos = sum(len(port) for port in ports[:index])
            if anchor_first:
                pos += len(anchor.word()) + sum(len(block) * n for block, n in parked.items())
            self.rewrite(pos, word(source), word(target))
            bag -= consumed
            if source:
                ports.pop(index)
            if target:
                ports.insert(index, target.port())
                bag.update(target.bag)
        assert ports == [finish.port()] and bag == Counter(finish.bag)
        self.permute(anchor.word() + finish.word() if anchor_first else finish.word() + anchor.word())

    def cycle(self, run):
        empty, start = run[0]
        finish, end = run[-1]
        assert empty is end is None
        self.rewrite(0, '', start.word())
        self.rewrite(0, '', start.word())
        self.middle(run[1:-1], start, finish, start, False)
        self.middle(run[1:-1], start, finish, finish, True)
        self.rewrite(0, finish.word(), '')
        self.rewrite(0, finish.word(), '')
        assert self.current == ''


def witnesses():
    start = Loop('P', ('a',), 'R')
    bare = Loop('P', (), 'R')
    end = Loop('U', ('b',), 'S')
    # Port changes alter the seam across which tokens are parked. A rule also
    # consumes an actual return through x as data; it is not a protected marker.
    rules = [(None, start), (bare, None), (None, bare), (end, None),
             (Loop('P', ('a', 'a'), 'R'), Loop('U', ('b', 'b'), 'S')),
             (bare, Loop('U', (), 'S')), (start, Loop('P', ('RP',), 'R')),
             (Loop('P', ('RP',), 'R'), end)]
    count = steps = stranded = 0

    def visit(run, ports, bag):
        nonlocal count, steps, stranded
        if not ports and not bag and run:
            replay = Replay(rules)
            replay.cycle(run)
            count += 1
            steps += replay.steps
            return
        if len(run) == 6:
            return
        if not ports and bag:
            stranded += 1
        for source, target in rules:
            key = source.port() if source else None
            spent = Counter(source.bag if source else ())
            if source and (not ports[key] or not spent <= bag):
                continue
            next_ports = ports.copy()
            if source:
                next_ports.subtract([key])
            if target:
                next_ports.update([target.port()])
            visit(run + [(source, target)], +next_ports, bag - spent + Counter(target.bag if target else ()))

    visit([], Counter(), Counter())
    assert stranded and count
    return count, steps


def cycle_nets(data):
    """Compile one strongly connected component with explicit adjacent shuffles."""
    hub, edges = data['hub'], data['edges']
    vertices = {hub} | {v for endpoints in edges.values() for v in endpoints}
    outgoing = {v: [(edge, end) for edge, (start, end) in edges.items() if start == v]
                for v in vertices}

    def reach(start):
        seen, todo = {start}, [start]
        while todo:
            for _, v in outgoing[todo.pop()]:
                if v not in seen:
                    seen.add(v)
                    todo.append(v)
        return seen

    if any(reach(v) != vertices for v in vertices):
        raise ValueError('supply a single strongly connected component')

    # All nonempty paths leaving a start, stopping at the first subsequent hub.
    def segments(start):
        stack = [(start, (), {start})]
        by_end = {v: [] for v in vertices}
        while stack:
            at, path, seen = stack.pop()
            for edge, end in outgoing[at]:
                extended = path + (edge,)
                by_end[end].append(extended)
                if end != hub:
                    if end in seen:
                        raise ValueError('the graph has a directed cycle avoiding the hub')
                    stack.append((end, extended, seen | {end}))
        return by_end

    paths = {v: segments(v) for v in vertices}
    loops = paths[hub][hub]
    rules = []
    for start, u, v in data['rules']:
        def end(word):
            at = start
            for edge in word:
                if edges[edge][0] != at:
                    raise ValueError('ill-typed rule path')
                at = edges[edge][1]
            return at
        if end(u) != end(v):
            raise ValueError('rule paths must be parallel')
        rules.append((start, tuple(u), tuple(v), end(u)))
    needed = {(hub, a + b, b + a, hub) for a, b in product(loops, repeat=2) if a != b}
    if not needed <= set(rules):
        raise ValueError('missing an explicit first-return shuffle')
    nets = {}
    for x in vertices:
        def marking(path):
            if not path:
                return ()
            at, block, first, bag = x, (), None, []
            for edge in path:
                block += (edge,)
                at = edges[edge][1]
                if at == hub:
                    if x != hub and first is None:
                        first = block
                    else:
                        bag.append(('return', block))
                    block = ()
            if x != hub:
                assert first is not None and block
                bag.append(('port', first, block))
            return tuple(sorted(bag))

        def exteriors(start, end, on_left):
            # The redex can touch the hub. Then the nearest hub is at distance zero.
            if start == end:
                return [()]
            if (end if on_left else start) == hub:
                return []
            return paths[start][end]

        pairs = set()
        for start, u, v, end in set(rules) - needed:
            for l, r in product({x, hub}, repeat=2):
                for a, b in product(exteriors(l, start, True), exteriors(end, r, False)):
                    prefixes = paths[x][hub] if l == hub and x != hub else [()]
                    suffixes = paths[hub][x] if r == hub and x != hub else [()]
                    for s, t in product(prefixes, suffixes):
                        pairs.add((marking(s+a+u+b+t), marking(s+a+v+b+t)))
        places = sorted({place for step in pairs for side in step for place in side})
        nets[x] = dict(point_gates=places, rules={i: (list(a), list(b)) for i, (a,b) in enumerate(sorted(pairs))})
    return nets


def compiler_test():
    from semistrict_surface_empty_returns import return_rules
    edges = {'P': ('x','h'), 'R': ('h','x'), 'a': ('h','h'), 'b': ('h','h')}
    edges['S'] = ('h', 'x')
    alphabet = ('a', 'b', 'RP', 'SP')
    base = [('h', i+j, j+i) for i,j in product(alphabet, repeat=2) if i != j]
    rules = [('x','','PR'), ('x','P','Pa'), ('h','a','b'), ('h','bR','S'), ('x','PS','')]
    queries = 0
    for mask in product((False, True), repeat=len(rules)):
        selected = [rule for flag, rule in zip(mask, rules) if flag]
        nets = cycle_nets(dict(hub='h', edges=edges, rules=base + selected))
        # Forward necessity: only the left move makes an a, only the middle move
        # makes a b, and only the right move makes an S. The two ends need their
        # own birth and death. No rule can start at the hub on an empty path.
        assert bool(return_rules(nets['x'])) == all(mask)
        assert not return_rules(nets['h'])
        queries += len(nets)
    return queries


if __name__ == '__main__':
    import argparse
    import json
    from pathlib import Path
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path)
    args = parser.parse_args()
    if args.input:
        from semistrict_surface_empty_returns import return_rules
        nets = cycle_nets(json.loads(args.input.read_text()))
        print(json.dumps({v: bool(return_rules(net)) for v, net in nets.items()}, sort_keys=True))
        raise SystemExit
    print(f'{compiler_test()} exact bubble decisions checked at the hub and at a second vertex.')
    count, steps = witnesses()
    print(f'{count} multiset excursions replayed as {steps} typed positioned steps through the empty path.')
