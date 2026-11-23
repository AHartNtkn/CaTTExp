"""Check the physical Gray return construction for a recognizer of even unary inputs."""

from argparse import ArgumentParser
from collections import Counter
from itertools import product
from pathlib import Path
from random import Random

from catt import STAR, arr, check_ctx, comp2, infer, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_return_gaps import Presentation, Rule, gap_outside_dictionary


HELPERS = '[]SCTK'
MACHINE = [('SCC', 'CCS'), ('S]', 'K]'), ('CK', 'KC'), ('[K', '[T')]
PRES = Presentation({'f': (0, 1), 'g': (1, 1), 'h': (1, 2)},
                    {**{x: ('f', 'f') for x in HELPERS + 'L'},
                     'd': ('fg', 'f'), 'e': ('f', 'fg'), 'B': ('h', 'h')}, [])


def grow(letter):
    return letter + 'C' if letter in 'ST' else letter


def schema():
    rules = [('f', 'L', '[S]'), ('f', '[T]', 'L')]
    reversible = [('fg', 'de', ''), ('f', 'ed', '')]
    for mark in HELPERS:
        reversible.append(('fg', mark, 'd' + grow(mark) + 'e'))
        rules.append(('fh', mark + 'B', 'B' + mark))
    for path, source, target in reversible:
        rules.extend([(path, source, target), (path, target, source)])
    return rules + [('fh', s, t) for s, t in MACHINE]


def positioned(start, word):
    path = start
    result = []
    for name in word:
        pos = path.index('h') if name == 'B' else 0
        s, t = PRES.marks[name]
        assert path.startswith(s, pos)
        result.append((pos, name))
        path = path[:pos] + t + path[pos + len(s):]
    return tuple(result)


RULES = [Rule(p, positioned(p, s), positioned(p, t)) for p, s, t in schema()]


def physical_moves(start, steps):
    paths = PRES.walk(start, steps)
    # The generic square moves right-then-left to left-then-right.
    for new, _ in PRES.moves(start, steps):
        yield new
    for i, path in enumerate(paths):
        for rule in RULES:
            # All declared spatial windows start at the unique f, at position zero.
            if not path.startswith(rule.path):
                continue
            end = i + len(rule.source)
            if steps[i:end] == rule.source:
                yield steps[:i] + rule.target + steps[end:]


def project(start, steps):
    result = []
    for path, (_, x) in zip(PRES.walk(start, steps), steps):
        n = path.count('g')
        if x == 'L':
            result.append(('L', n))
        elif x in 'ST':
            result.extend([x] + ['C'] * n)
        elif x not in 'de':
            result.append(x)
    return tuple(result)


def allowed_projection(before, after):
    strip = lambda w: tuple(x for x in w if x != 'B')
    a, b = strip(before), strip(after)
    if a == b:
        # Choose the ordered subsequence of the protected L's and right events.
        order = lambda w: tuple(x for x in w if x == 'B' or isinstance(x, tuple))
        u, v1 = order(before), order(after)
        return u == v1 or any(
            x == 'B' and isinstance(y, tuple) and u[:i] + (y, x) + u[i + 2:] == v1
            for i, (x, y) in enumerate(zip(u, u[1:])))
    rewrites = [(tuple(s), tuple(t)) for s, t in MACHINE]
    for x in (*a, *b):
        if isinstance(x, tuple):
            marks = 'C' * x[1]
            rewrites += [((x,), tuple('[S' + marks + ']')), (tuple('[T' + marks + ']'), (x,))]
    return any(a[i:i + len(s)] == s and a[:i] + t + a[i + len(s):] == b
               for s, t in rewrites for i in range(len(a)))


def expansion(n, word):
    """Move a nonempty word of helpers to the path fh by reversible left rules."""
    trace = [word]
    for k in range(n):
        left, right = 'd' * k, 'e' * k
        new_payload = ''.join(map(grow, word))
        prefix = ''
        for i, mark in enumerate(word):
            prefix += 'd' + grow(mark) + 'e'
            trace.append(left + prefix + word[i + 1:] + right)
        for _ in range(len(word) - 1):
            prefix = prefix.replace('ed', '', 1)
            trace.append(left + prefix + right)
        assert prefix == 'd' + new_payload + 'e'
        word = new_payload
    return trace


def sweep(payload):
    trace = [payload + 'B']
    for i in reversed(range(len(payload))):
        left, ch, right = payload[:i], payload[i], payload[i + 1:]
        if ch in 'de':
            inv = 'e' if ch == 'd' else 'd'
            trace.append(left + ch + 'B' + inv + ch + right)
            trace.append(left + ch + inv + 'B' + ch + right)
        trace.append(left + 'B' + ch + right)
    return trace


def machine_run(word):
    yield word
    while (successors := [word.replace(s, t, 1) for s, t in MACHINE if s in word]):
        (word,) = successors
        yield word


def witness(n, letter):
    if letter in 'de':
        return sweep(letter)
    if letter != 'L':
        exp = expansion(n, letter)
        return [s + 'B' for s in exp] + sweep(exp[-1])[1:] + ['B' + s for s in reversed(exp[:-1])]
    source, target = expansion(n, '[S]'), expansion(n, '[T]')
    work = list(machine_run('[S' + 'C' * n + ']'))
    if work[-1] != '[T' + 'C' * n + ']':
        return None
    trace = ['LB'] + [s + 'B' for s in source]
    trace.extend('d' * n + s + 'e' * n + 'B' for s in work[1:])
    trace.extend(sweep(target[-1])[1:])
    trace.extend('B' + s for s in reversed(target[:-1]))
    return trace + ['BL']


def check_histories(counts):
    for n, letter in product(range(8), 'Lde' + HELPERS):
        trace = witness(n, letter)
        if trace is None:
            assert letter == 'L' and n % 2
            counts['odd inputs trapped in the projected machine'] += 1
            continue
        start, lr, rl = PRES.square(letter, 'g' * n, 'B')
        steps = [positioned(start, w) for w in trace]
        assert steps[0] == lr and steps[-1] == rl
        for u, v1 in zip(steps, steps[1:]):
            assert v1 in physical_moves(start, u)
        counts['physical moves in explicit return paths'] += len(steps) - 1
        counts['complete physical returns'] += 1

    rng = Random(20261123)
    for _ in range(1200):
        start = 'f' + 'g' * rng.randrange(4) + 'h'
        word = ''.join(rng.choices(HELPERS + 'LddeeBB', k=rng.randrange(9)))
        if min([start.count('g')] + [start.count('g') + word[:i].count('e') - word[:i].count('d')
                                    for i in range(1, len(word) + 1)]) < 0:
            continue
        steps = positioned(start, word)
        before = project(start, steps)
        for new in physical_moves(start, steps):
            assert allowed_projection(before, project(start, new))
            counts['contextual moves tested against the projection'] += 1


def check_positive_windows(counts):
    marks = {k: PRES.marks[k] for k in 'LBde'}
    marks.update(u=('gh', 'h'), v=('h', 'gh'))
    expansions = [Rule('fg', ((0, 'L'),), ((0, 'd'), (0, 'L'), (0, 'e'))),
                  Rule('gh', ((1, 'B'),), ((0, 'u'), (0, 'B'), (0, 'v'))),
                  Rule('f', ((0, 'L'),), ((0, 'L'), (0, 'L')))]
    crossing = Rule('fh', ((0, 'L'), (1, 'B')), ((1, 'B'), (0, 'L')))
    rules = expansions + [Rule(r.path, r.target, r.source) for r in expansions] + [crossing]
    pres = Presentation(PRES.edges, marks, rules)
    dictionary = {word[i:j] for word in [r.path for r in rules] + [s for s, _ in marks.values()]
                  for i in range(len(word) + 1) for j in range(i, len(word) + 1)}
    assert gap_outside_dictionary(pres.edges, 1, 1, dictionary) == 'gg'
    rng = Random(418)
    for n in range(2, 7):
        start = 'f' + 'g' * n + 'h'
        deep = positioned(start, 'd' * n + 'LB' + 'e' * n)
        assert any(detail and detail[0] == crossing for _, detail in pres.moves(start, deep))
        histories = [deep, pres.square('L', 'g' * n, 'B')[1]]
        for _ in range(80):
            path, steps = start, []
            for _ in range(rng.randrange(1, 16)):
                candidates = [(i, name) for name, (source, _) in marks.items()
                              for i in range(len(path)) if path.startswith(source, i)]
                step = rng.choice(candidates)
                path = pres.walk(path, (step,))[-1]
                steps.append(step)
            histories.append(tuple(steps))
        for steps in histories:
            if steps[0][0] != 0:
                continue
            for after, _ in pres.moves(start, steps):
                assert after[0][0] == 0
                counts['positive moves preserving the side of the first event'] += 1


def raw_rules():
    ctx = [STAR] * 3

    def declare(ty):
        gen = v(len(ctx))
        ctx.append(ty)
        return gen

    f, g, h = [declare(arr(STAR, v(i), v(j))) for i, j in ((0, 1), (1, 1), (1, 2))]
    fg, fh = (comp2(tuple(ctx), 0, f, right) for right in (g, h))
    marks = {x: declare(arr(infer(tuple(ctx), f), f, f)) for x in HELPERS + 'L'}
    for x, s, t in [('d', fg, f), ('e', f, fg), ('B', h, h)]:
        marks[x] = declare(arr(infer(tuple(ctx), s), s, t))
    base = tuple(ctx)

    def reading(path, word):
        current = {'f': f, 'fg': fg, 'fh': fh}[path]
        result = None
        for name in word:
            term = marks[name]
            if name == 'B':
                term = comp2(base, 0, f, term)
            elif name not in 'de' and current != f:
                term = comp2(base, 0, term, g if current == fg else h)
            assert infer(base, term)[2] == current
            current = infer(base, term)[3]
            result = term if result is None else comp2(base, 1, result, term)
        return result if result is not None else identity(base, current)

    emitter = Emitter()
    for i, (path, before, after) in enumerate(schema()):
        s, t = reading(path, before), reading(path, after)
        ty = infer(base, s)
        assert infer(base, t) == ty
        declare(arr(ty, s, t))
        emitter.check_type(f'source-{i}', base, s, ty)
        emitter.check_type(f'target-{i}', base, t, ty)
    check_ctx(tuple(ctx))
    return emitter


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    counts = Counter()
    check_histories(counts)
    check_positive_windows(counts)
    emitter = raw_rules()
    if args.agda:
        module = emitter.module(args.agda.stem, 'Boundaries of the parity presentation.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n',
                                            'open import CaTTExp.Gray.Pure\n'))
    for label, value in counts.items():
        print(f'{value:,} {label}')
