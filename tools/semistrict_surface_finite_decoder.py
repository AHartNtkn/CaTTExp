"""Check literal decoding of positive arrow codes and the residual-tree boundary fits."""
from argparse import ArgumentParser
from dataclasses import dataclass
from itertools import product
from pathlib import Path

from catt import STAR, arr, chain_tree, coh_between, comp2, disc_tree, infer, maximal_vars, src, tgt, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity
from semistrict_surface_mixed_winding import slots


class Decoder:
    def __init__(self, alphabet):
        self.width = (alphabet - 1).bit_length() + 1
        self.reset_length = (2 * self.width - 1).bit_length()
        reset = 'P' * self.reset_length
        payloads = (''.join(bits) for bits in product('PQ', repeat=self.width))
        self.edges = {}
        for payload in payloads:
            if reset not in payload:
                self.edges[payload] = len(self.edges) + 1
                if len(self.edges) == alphabet:
                    break
        assert len(self.edges) == alphabet
        self.codes = [reset + 'Q' + payload + 'Q' for payload in self.edges]
        self.idle = (0, 'idle', '')

    def step(self, state, letter):
        run, phase, prefix = state
        if letter == 'P':
            run = min(self.reset_length, run + 1)
            if run == self.reset_length:
                return (run, 'reset', ''), None
        else:
            run = 0
            if phase == 'reset':
                return (0, 'read', ''), None
        if phase == 'read':
            if len(prefix) < self.width:
                return (run, 'read', prefix + letter), None
            emitted = self.edges.get(prefix) if letter == 'Q' else None
            return (run, 'idle', ''), emitted
        return (run, phase, ''), None

    def states(self):
        states, pending = {self.idle}, [self.idle]
        while pending:
            state = pending.pop()
            for letter in 'PQ':
                target, _ = self.step(state, letter)
                if target not in states:
                    states.add(target)
                    pending.append(target)
        return sorted(states)


@dataclass(frozen=True)
class Reading:
    action: tuple
    marked: bool
    term: object


def codes(alphabet):
    machine = Decoder(alphabet)
    states = machine.states()
    indices = {state: i for i, state in enumerate(states)}
    identity_action = tuple(range(len(states)))
    reset_action = (indices[machine.idle],) * len(states)
    ordinary = {identity_action, reset_action}
    actions = {c: tuple(indices[machine.step(s, c)[0]] for s in states) for c in 'PQ'}
    assert all(action not in ordinary for action in actions.values())

    def paste(a, b):
        term = ('comp', a.term, b.term)
        if (a.action not in ordinary or b.action not in ordinary) and a.marked != b.marked:
            term = a.term if a.marked else b.term
        return Reading(tuple(b.action[i] for i in a.action), a.marked or b.marked, term)

    checks = 0
    for state in states:
        entries = []
        for i, word in enumerate(machine.codes, 1):
            cursor, readings, emissions = state, [], []
            for letter in word:
                cursor, emitted = machine.step(cursor, letter)
                emissions.append(emitted)
                term = ('edge', emitted) if emitted else 'id'
                readings.append(Reading(actions[letter], bool(emitted), term))
            result = readings[-1]
            for leaf in reversed(readings[:-1]):
                result = paste(leaf, result)
            assert cursor == machine.idle and emissions == [None] * (len(word) - 1) + [i]
            assert result == Reading(reset_action, True, ('edge', i))
            entries.append(result)
        entries.append(Reading(identity_action, False, 'id'))
        for a, b, c in product(entries, repeat=3):
            assert paste(a, paste(b, c)).term == ('comp', a.term, ('comp', b.term, c.term))
            assert paste(paste(a, b), c).term == ('comp', ('comp', a.term, b.term), c.term)
            checks += 2
    return checks


def rotations():
    count = 0
    for alphabet in range(1, 129):
        machine = Decoder(alphabet)
        seen = set()
        for word in machine.codes:
            for offset in range(len(word)):
                rotation = word[offset:] + word[:offset]
                assert rotation not in seen
                seen.add(rotation)
                count += 1
        assert len(seen) == alphabet * len(machine.codes[0])
    return count


def weight_checks():
    candidates = [((0,), (1,)), ((1,), (2,)), ((0,), (2,)),
                  ((0,), (1, 2)), ((1, 0), (2,)), ((2, 0), (1, 2, 1))]
    checks = 0
    for keep in product((False, True), repeat=len(candidates)):
        rules = [rule for selected, rule in zip(keep, candidates, strict=True) if selected]
        for query in range(3):
            component = {query}
            while True:
                added = set()
                for a, b in rules:
                    if len(a) == len(b) == 1 and component.intersection(a + b):
                        added.update(a + b)
                if added <= component:
                    break
                component.update(added)
            blocked = any(len(a) == 1 and a[0] in component and len(b) > 1
                          for sides in rules for a, b in (sides, sides[::-1]))
            possible = any(
                w[query] == 1 and all(min(2, sum(w[i] for i in a)) == min(2, sum(w[i] for i in b))
                                      for a, b in rules)
                for w in product((1, 2), repeat=3))
            assert possible == (not blocked)
            checks += 1
    return checks


def fits(emitter):
    # Formal retained columns D^2 and D^1. The silent prefix reads an identity.
    ctx = tree_ctx((disc_tree(1), disc_tree(0)))
    alpha, r = map(v, maximal_vars(ctx))
    f, g = src(ctx, alpha), tgt(ctx, alpha)
    unit = identity(ctx, v(0))
    old = comp2(ctx, 0, comp2(ctx, 0, unit, alpha), r)

    line = chain_tree(2)
    arity = tree_ctx(line)
    x, y = map(v, maximal_vars(arity))
    padded = comp2(arity, 0, comp2(arity, 0, identity(arity, v(0)), x), y)
    plain = comp2(arity, 0, x, y)
    enter = coh_between(ctx, line, [f, r], plain, padded)
    leave = coh_between(ctx, line, [g, r], padded, plain)
    result = comp2(ctx, 1, comp2(ctx, 1, enter, old), leave)
    ty = arr(infer(ctx, comp2(ctx, 0, f, r)), comp2(ctx, 0, f, r), comp2(ctx, 0, g, r))
    assert infer(ctx, result) == ty
    if emitter:
        emitter.check_type('fitted', ctx, result, ty)

    # A genuine top declaration on an object has no marked 1-event.
    # Its occurrence still survives whiskering by the retained edge.
    base = (STAR, arr(STAR, v(0), v(0)))
    pole = identity(base, identity(base, v(0)))
    ctx = base + (arr(infer(base, pole), pole, pole),)
    top, edge = v(2), v(1)
    carried = comp2(ctx, 0, top, edge)
    lower = comp2(ctx, 0, pole, edge)
    ty = arr(infer(ctx, lower), lower, lower)
    assert infer(ctx, carried) == ty
    _, arity, _, sub = carried
    positions, _ = slots(arity)
    assert [sub[i] for pos, i in positions.items() if len(pos) == 3] == [top]
    if emitter:
        emitter.check_type('emptyBoundaryTop', ctx, carried, ty)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter() if args.agda_dir else None
    checks = sum(codes(size) for size in (1, 2, 3, 5, 8))
    print(f'{checks} literal bracketings, including old identities, survived finite decoding.')
    print(f'{rotations()} rotations lay in disjoint full-length orbits within their codebooks.')
    print(f'{weight_checks()} singleton-component tests matched exhaustive saturated gradings.')
    fits(emitter)
    print('Verified the two-column boundary fit and the retained top occurrence on an empty path.')
    if emitter:
        name = 'FiniteDecoder'
        module = emitter.module(name, __doc__).replace('open import CaTTExp.Pure', 'open import CaTTExp.Gray.Pure')
        (args.agda_dir / (name + '.agda')).write_text(module)
