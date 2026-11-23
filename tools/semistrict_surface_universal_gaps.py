"""Compile a unary computation into universal Gray square returns on f h* g.

The executable uses the unary language {0,...,limit} for an independent
negative oracle. The compiler also accepts positive machine rules on the
stationary g alphabet as described in Response 105.
"""

from argparse import ArgumentParser
from collections import Counter
from dataclasses import asdict
from itertools import product
import json
from pathlib import Path

from semistrict_surface_return_gaps import Presentation, Rule

EDGES = {'f': (0, 1), 'h': (1, 1), 'g': (1, 2)}
MOBILE = ('+', '-', 'pass', 'C')
FREE = ('+', '-', 'pass')


def word(*symbols):
    return tuple((0, x) for x in symbols)


def machine(limit):
    states = tuple(f'q{i}' for i in range(limit + 1))
    rules = [(('I',), ('q0',))]
    rules += [((s, 'U'), (t,)) for s, t in zip(states, states[1:])]
    rules += [(('L', s, 'R'), ('passg',)) for s in states]
    return states, rules


def compile_machine(symbols, machine_rules):
    marks = {x + e: (e, e) for x in MOBILE for e in EDGES}
    marks['a'] = ('f', 'f')
    stationary = ('b', 'L', 'I', 'R', 'U', *symbols)
    marks.update({x: ('g', 'g') for x in stationary})
    rules = []

    def both(path, lhs, rhs):
        rules.extend((Rule(path, lhs, rhs), Rule(path, rhs, lhs)))

    for e in EDGES:
        for m in MOBILE:
            for x, (s, _) in marks.items():
                if s == e and x != m + e:
                    both(e, word(m + e, x), word(x, m + e))
    for path in ('fh', 'fg', 'hh', 'hg'):
        a, b = path
        for m in FREE:
            both(path, ((0, m + a),), ((1, m + b),))
        ca, cb = ((0, 'C' + a),), ((1, 'C' + b),)
        if b == 'h':
            both(path, ca, ((1, '+h'),) + cb)
            both(path, cb, ((0, '-' + a),) + ca)
        else:
            both(path, ca, cb)
    rules += [Rule('f', word('a'), word('Cf')),
              Rule('f', word('passf'), word('a')),
              Rule('g', word('Cg'), word('L', 'I', 'R')),
              Rule('g', word('+g', 'I'), word('I', 'U'))]
    rules.extend(Rule('g', word(*lhs), word(*rhs)) for lhs, rhs in machine_rules)
    return Presentation(EDGES, marks, list(dict.fromkeys(rules)))


class Witness:
    def __init__(self, pres, path, history):
        self.pres, self.path, self.history = pres, path, history
        self.dictionary = set(pres.rules)
        self.count = 0

    def apply(self, site, width, k, source, target):
        within = self.path[site:site + width]
        def relative(steps):
            return tuple((i - site, x) for i, x in steps)
        law = Rule(within, relative(source), relative(target))
        assert law in self.dictionary and self.history[k:k + len(source)] == source
        self.history = self.history[:k] + target + self.history[k + len(source):]
        assert self.pres.walk(self.path, self.history)[-1] == self.path
        self.count += 1

    def local(self, site, k, source, target):
        self.apply(site, 1, k, tuple((site, x) for x in source), tuple((site, x) for x in target))

    def travel(self, k, dest, scan=False):
        """Return the new mover index and the list of invertible steps."""
        log = []
        site, name = self.history[k]
        while site != dest:
            j = site + (1 if site < dest else -1)
            moved = (j, name[:-1] + self.path[j])
            tick = ()
            if scan and self.path[max(site, j)] == 'h':
                tick = ((j, ('+' if site < j else '-') + self.path[j]),)
            lhs, rhs = ((site, name),), tick + (moved,)
            self.apply(min(site, j), 2, k, lhs, rhs)
            log.append((min(site, j), lhs, rhs))
            k += len(tick)
            site, name = moved
        return k, log

    def commute_free(self, k, mover_first):
        mobile = k if mover_first else k + 1
        other = k + 1 if mover_first else k
        dest = self.history[other][0]
        _, log = self.travel(mobile, dest)
        x, y = self.history[k:k + 2]
        if x != y:
            self.local(dest, k, (x[1], y[1]), (y[1], x[1]))
        for site, lhs, rhs in reversed(log):
            self.apply(site, 2, other, rhs, lhs)

    def commute_scanner(self, k, scanner_first):
        # Move the scanner to its neighbour, commute its whole expansion, then
        # invert the recorded travel on the other side of that neighbour.
        index = k if scanner_first else k + 1
        other = k + 1 if scanner_first else k
        dest = self.history[other][0]
        end, log = self.travel(index, dest, scan=True)
        ticks = end - index
        if not scanner_first:
            for i in range(ticks):
                self.commute_free(k + i, False)
        at = k + ticks
        x, y = self.history[at:at + 2]
        if x != y:
            self.local(dest, at, (x[1], y[1]), (y[1], x[1]))
        if scanner_first:
            for i in reversed(range(ticks)):
                self.commute_free(k + i, True)
        end = k + ticks + int(scanner_first)
        for site, lhs, rhs in reversed(log):
            end -= len(rhs) - 1
            self.apply(site, 2, end, rhs, lhs)

    def run_epoch(self):
        n = self.path.count('h')
        last = len(self.path) - 1
        self.local(0, 0, ('a',), ('Cf',))
        self.travel(0, last, scan=True)
        for i in range(n):
            self.travel(i, last)
        self.local(last, n, ('Cg',), ('L', 'I', 'R'))
        for i in reversed(range(n)):
            self.local(last, i, ('+g', 'L'), ('L', '+g'))
        for i in reversed(range(1, n + 1)):
            self.local(last, i, ('+g', 'I'), ('I', 'U'))
        self.local(last, 1, ('I',), ('q0',))
        for i in range(n):
            self.local(last, 1, (f'q{i}', 'U'), (f'q{i+1}',))
        self.local(last, 0, ('L', f'q{n}', 'R'), ('passg',))
        self.commute_free(0, True)
        self.travel(1, 0)
        self.local(0, 1, ('passf',), ('a',))


def verify(limit):
    states, program = machine(limit)
    pres = compile_machine(states, program)
    counts = Counter()
    for n in range(limit + 1):
        for path in ('f' + 'h' * n + 'g', 'f' + 'h' * (n + 1), 'h' * (n + 1) + 'g', 'h' * (n + 2)):
            for (x, (sx, _)), (y, (sy, _)) in product(pres.marks.items(), repeat=2):
                if (sx, sy) != (path[0], path[-1]):
                    continue
                start, lr, rl = pres.square(x, path[1:-1], y)
                w = Witness(pres, start, lr)
                if x[:-1] in FREE or y[:-1] in FREE:
                    w.commute_free(0, x[:-1] in FREE)
                elif x[:-1] == 'C' or y[:-1] == 'C':
                    w.commute_scanner(0, x[:-1] == 'C')
                else:
                    w.run_epoch()
                assert w.history == rl
                counts['complete bare returns'] += 1
                counts['literal declared steps'] += w.count
    # Verify the signed accounting on every contextual rule at its actual
    # edge path. A scanner move adds its exact displacement to signed ticks.
    # Entering an epoch starts at zero; reaching g collects the full gap.
    p = 'f' + 'h' * (limit + 4) + 'g'
    def score(steps):
        ticks = sum((x[0] == '+') - (x[0] == '-') for _, x in steps)
        scanner = sum(p[:i+1].count('h') for i, x in steps if x[:-1] == 'C')
        return ticks - scanner
    for law in pres.rules:
        for off in range(len(p) - len(law.path) + 1):
            if not p.startswith(law.path, off):
                continue
            a, b = [tuple((i + off, x) for i, x in steps) for steps in (law.source, law.target)]
            delta = score(b) - score(a)
            assert delta == (p.count('h') if law.source == word('Cg') and law.target == word('L', 'I', 'R')
                             else -1 if law.source == word('+g', 'I') and law.target == word('I', 'U') else 0)
            counts['positioned signed balances'] += 1
    return pres, counts


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=4)
    parser.add_argument('--emit', type=Path, help='write explicit edge/mark/rule JSON')
    args = parser.parse_args()
    if args.limit < 0:
        parser.error('limit must be nonnegative')
    pres, totals = verify(args.limit)
    if args.emit:
        args.emit.write_text(json.dumps({'edges': pres.edges, 'marks': pres.marks,
                                        'rules': [asdict(r) for r in pres.rules]}, indent=2))
    for label, count in sorted(totals.items()):
        print(f'{count:,} {label}')
