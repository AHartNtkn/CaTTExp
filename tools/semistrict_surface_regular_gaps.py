"""Compile two-event Gray returns to a MONA formula over *all* spatial gaps.

Use positive temporal rules all nonincreasing or all nondecreasing, and marks
that are endomorphisms of nonempty edge paths. Input uses Response 103's JSON.
"""

from argparse import ArgumentParser
from functools import cache
import json
from itertools import product
import re
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from semistrict_surface_return_gaps import Presentation, Rule


def any_of(parts):
    return '(' + ' | '.join(parts or ['false']) + ')'


def all_of(parts):
    return '(' + ' & '.join(parts or ['true']) + ')'


def plus(x, i):
    return f'({x}+{i})' if i else str(x)


class Compiler:
    def __init__(self, pres):
        self.pres = pres
        if any(s != t for s, t in pres.marks.values()):
            raise ValueError('marks must preserve the spatial path')
        differences = {len(r.target) - len(r.source) for r in pres.rules}
        if any(d < 0 for d in differences) and any(d > 0 for d in differences):
            raise ValueError('the temporal rule lengths must have a common direction')
        self.marks = list(pres.marks)
        self.edges = list(pres.edges)
        self.lines = ['ws1s;', 'var1 n;', 'var2 ' + ','.join(self.edge(e) for e in self.edges) + ';']
        self.unary = [r for r in pres.rules if len(r.source) == len(r.target) == 1]
        self.binary = [r for r in pres.rules if len(r.source) == len(r.target) == 2]
        self.paths = {a: {a} for a in self.marks}
        for r in self.unary:
            self.paths[r.source[0][1]].add(r.target[0][1])
        for a in self.marks:
            for b in self.marks:
                if a in self.paths[b]:
                    self.paths[b].update(self.paths[a])

    def edge(self, e):
        return f'E{self.edges.index(e)}'

    def window(self, x, path):
        return all_of([f'{plus(x, len(path))} <= n'] +
                      [f'{plus(x, i)} in {self.edge(e)}' for i, e in enumerate(path)])

    def graph_word(self):
        choices = []
        for e, (_, end) in self.pres.edges.items():
            followers = [f'(w+1) in {self.edge(f)}' for f, (start, _) in self.pres.edges.items() if start == end]
            choices.append(all_of([f'w in {self.edge(e)}'] + [f'w notin {self.edge(f)}' for f in self.edges if f != e]
                                  + [f'((w+1) = n | {any_of(followers)})']))
        return '(all1 w: w < n => ' + any_of(choices) + ')'

    @cache
    def unary_name(self, a, b):
        """Reachability on one finite copy of word positions per relevant label."""
        name = f'U{self.marks.index(a)}to{self.marks.index(b)}'
        selected = [q for q in self.marks if q in self.paths[a] and b in self.paths[q]]
        sets = {q: f'X{i}' for i, q in enumerate(selected)}
        laws = [r for r in self.unary if r.source[0][1] in sets and r.target[0][1] in sets]
        clauses = []
        for r in laws:
            (i, s), (j, t) = r.source[0], r.target[0]
            clauses.append(f'(all1 w: ({self.window("w", r.path)} & {plus("w", i)} in {sets[s]}) => {plus("w", j)} in {sets[t]})')
        if not selected:
            body = 'false'
        elif not laws:
            body = 'x = y'
        else:
            closed = all_of([f'x in {sets[a]}'] + clauses)
            body = f'(all2 {",".join(sets.values())}: {closed} => y in {sets[b]})'
        self.lines.append(f'pred {name}(var1 x,y) = {body};')
        return name

    def unary_call(self, a, x, b, y):
        return f'{self.unary_name(a,b)}({x},{y})'

    @cache
    def independent_name(self, a, b, c, d):
        parts = []
        if c in self.paths[a] and d in self.paths[b]:
            parts.append(all_of([self.unary_call(a,'x',c,'z'), self.unary_call(b,'y',d,'w')]))
        for i in self.marks:
            for j in self.marks:
                if i not in self.paths[a] or d not in self.paths[i] or j not in self.paths[b] or c not in self.paths[j]:
                    continue
                through = [self.unary_call(a,'x',i,'u'), self.unary_call(i,'u',d,'w'),
                           self.unary_call(b,'y',j,'v'), self.unary_call(j,'v',c,'z'),
                           f'{plus("v", len(self.pres.marks[j][0]))} <= u']
                parts.append(f'(ex1 u,v: {all_of(through)})')
        name = 'F' + 'q'.join(str(self.marks.index(q)) for q in (a,b,c,d))
        self.lines.append(f'pred {name}(var1 x,y,z,w) = {any_of(parts)};')
        return name

    def segment(self, start, end):
        args = start + end
        pred = self.independent_name(*(q for _, q in args))
        return pred + '(' + ','.join(x for x, _ in args) + ')'

    def comparison(self, start, end):
        direct = self.segment(start, end)
        if not self.binary:
            return direct
        def at(x, side):
            return tuple((plus(x, i), a) for i, a in side)
        clauses, finish = [], []
        for i, r in enumerate(self.binary):
            enabled = self.window('u', r.path)
            enter = self.segment(start, at('u', r.source))
            clauses.append(f'(all1 u: ({enabled} & {enter}) => u in Y{i})')
            out = at('u', r.target)
            finish.append(f'(ex1 u: u in Y{i} & {enabled} & {self.segment(out, end)})')
            for j, s in enumerate(self.binary):
                adjacent = self.segment(out, at('v', s.source))
                clauses.append(f'(all1 u,v: (u in Y{i} & {enabled} & {self.window("v",s.path)} & {adjacent}) => v in Y{j})')
        sets = ','.join(f'Y{i}' for i in range(len(self.binary)))
        return f'({direct} | (all2 {sets}: {all_of(clauses)} => {any_of(finish)}))'

    def formula(self, a, b, gap_parity=None):
        left, right = (self.pres.marks[x][0] for x in (a,b))
        pair = (('0', a), ('s', b))
        question = self.comparison(pair, pair[::-1])
        if gap_parity is not None:
            # Test whether the *entire* accepted language is a given parity.
            parity = '(ex2 Z: 0 in Z & (all1 j: j<n => ((j in Z) <=> ((j+1) notin Z))) & s in Z)'
            want_s_even = (gap_parity + len(left)) % 2 == 0
            question = f'({question} <=> {parity if want_s_even else "~"+parity})'
        valid = all_of([self.graph_word(), self.window('0', left), self.window('s', right),
                        f's+{len(right)} = n', f'{len(left)} <= s'])
        return '\n'.join(self.lines + [f'all1 s: {valid} => {question};', ''])


def parity_case():
    edges = {'f': (0,1), 'h': (1,1), 'g': (1,2)}
    marks = {'a': ('f','f'), 'u': ('h','h'), 'v': ('h','h'), 'b': ('g','g')}
    rules = []
    def both(path, x, y):
        rules.extend((Rule(path,x,y),Rule(path,y,x)))
    both('fh', ((0,'a'),), ((1,'u'),))
    for x,y in [('u','v'),('v','u')]:
        both('hh', ((0,x),), ((1,y),))
    rules.append(Rule('hg', ((0,'u'),(1,'b')), ((1,'b'),(0,'u'))))
    return Presentation(edges,marks,rules)


def from_json(data):
    return Presentation(data['edges'], data['marks'],
                        [Rule(r['path'], tuple(map(tuple,r['source'])), tuple(map(tuple,r['target']))) for r in data['rules']])


def countermodel(binary, formula, path):
    path.write_text(formula)
    result = subprocess.run([binary,'-q',str(path)], check=True, capture_output=True, text=True)
    if 'Formula is valid' in result.stdout:
        return None
    model = result.stdout.split('A satisfying example')[0]
    length = re.search(r'^n = (\d+)$', model, re.M)
    if not length:
        raise RuntimeError(result.stdout)
    size = int(length[1])
    letters = [None] * size
    for edge, positions in re.findall(r'^E(\d+) = \{([^}]*)\}$', model, re.M):
        for value in positions.split(','):
            if value.strip() and int(value) < size:
                letters[int(value)] = int(edge)
    return letters


def run_mona(binary, formula, path):
    return countermodel(binary, formula, path) is None


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path)
    parser.add_argument('--pair', nargs=2)
    parser.add_argument('--formula', type=Path)
    parser.add_argument('--mona', default='mona')
    args = parser.parse_args()
    if args.base:
        if args.formula and not args.pair:
            parser.error('use --pair A B to export a formula')
        pres = from_json(json.loads(args.base.read_text()))
        compiler = Compiler(pres)
        if args.formula:
            args.formula.write_text(compiler.formula(*args.pair))
        else:
            pairs = [args.pair] if args.pair else product(pres.marks, repeat=2)
            with TemporaryDirectory() as loc:
                for a, b in pairs:
                    model = countermodel(args.mona,compiler.formula(a,b),Path(loc)/'gap.mona')
                    if model is not None:
                        spatial = ''.join(compiler.edges[i] for i in model)
                        gap = spatial[len(pres.marks[a][0]):len(spatial)-len(pres.marks[b][0])]
                        p, left, right = pres.square(a, gap, b)
                        assert p == spatial and right not in pres.reachable(p, left, 2)
                        print(json.dumps({'failed_square': [a, gap, b]}))
                        break
                else:
                    print('all gaps return')
    else:
        pres = parity_case()
        with TemporaryDirectory() as loc:
            path = Path(loc)/'gap.mona'
            assert run_mona(args.mona,Compiler(pres).formula('a','b',1),path)
            assert not run_mona(args.mona,Compiler(pres).formula('a','b'),path)
            complete = Presentation(pres.edges,pres.marks,pres.rules +
                                    [Rule(*pres.square('a','','b')),
                                     Rule('hg',((0,'v'),(1,'b')),((1,'b'),(0,'v')))])
            assert run_mona(args.mona,Compiler(complete).formula('a','b'),path)
            edges = {'f':(0,1), 'g':(1,2)}
            marks = {q: ('f','f') for q in 'axy'} | {'b':('g','g')}
            bare = Presentation(edges,marks,[])
            p, src, dst = bare.square('a','','b')
            blocks = [src, ((0,'x'),)*2, ((0,'y'),)*2, dst]
            rules = [Rule(p,u,v) for u,v in zip(blocks, blocks[1:])]
            for take in (2,3):
                branch = Presentation(edges,marks,rules[:take])
                assert run_mona(args.mona,Compiler(branch).formula('a','b'),path) == (take == 3)
        for n in range(26):
            p, l, r = pres.square('a','h'*n,'b')
            assert (r in pres.reachable(p,l,2)) == bool(n%2)
        print('MONA verified the exact odd-length language, rejected universality, and verified the completed language. 26 literal gap searches agree.')
