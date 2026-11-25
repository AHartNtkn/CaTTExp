"""Compile marked word computations at literal CaTT 4-boundaries."""
from argparse import ArgumentParser
from dataclasses import dataclass
from itertools import product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, infer, maximal_vars, src, tdim, tgt, v
from ct_suspension import susp_ctx, susp_tm, susp_ty
from emit_agda import Emitter
from relative_coherence_hidden_seam import identity


def placed(ctx, cut, left, term, right):
    return comp2(ctx, cut, comp2(ctx, cut, left, term), right)


@dataclass(frozen=True)
class Query:
    word: tuple
    gate: tuple
    mark: tuple
    empty: tuple


@dataclass(frozen=True)
class Frame:
    advance: tuple
    close: tuple
    outgoing: tuple
    returning: tuple
    birth: tuple
    death: tuple

    def wrap(self, ctx, successor):
        inner = placed(ctx, 1, self.outgoing, successor, self.returning)
        return placed(ctx, 2, self.birth, inner, self.death)

    def propagate(self, ctx, successor):
        return placed(ctx, 3, self.advance, self.wrap(ctx, successor), self.close)


class Machine:
    def __init__(self, tape, states):
        self.ctx = (STAR,)
        self.x = v(0)
        self.tape = tape
        self.letters = {a: self.arrow(self.x, self.x) for a in tape + states}
        self.marks = {}
        for q in states:
            cell = identity(self.ctx, self.letters[q])
            self.marks[q] = self.arrow(cell, cell)

    def arrow(self, s, t):
        ty = infer(self.ctx, s)
        assert ty == infer(self.ctx, t)
        value = v(len(self.ctx))
        self.ctx += (arr(ty, s, t),)
        return value

    def tape_term(self, word):
        value = identity(self.ctx, self.x)
        for a in word:
            value = comp2(self.ctx, 0, value, self.letters[a])
        return value

    def parts(self, cfg):
        [i] = [i for i, a in enumerate(cfg) if a not in self.tape]
        return self.tape_term(cfg[:i]), cfg[i], self.tape_term(cfg[i + 1:])

    def query(self, cfg):
        left, q, right = self.parts(cfg)
        edge = self.letters[q]
        gate = identity(self.ctx, edge)
        return Query(*(placed(self.ctx, 0, left, cell, right) for cell in
                       (edge, gate, self.marks[q], identity(self.ctx, gate))))

    def frame(self, u, w):
        before, after = self.query(u), self.query(w)
        outgoing = self.arrow(before.word, after.word)
        returning = self.arrow(after.word, before.word)
        port = placed(self.ctx, 1, outgoing, after.gate, returning)
        birth, death = self.arrow(before.gate, port), self.arrow(port, before.gate)
        def wrap(cell):
            return placed(self.ctx, 2, birth, placed(self.ctx, 1, outgoing, cell, returning), death)
        advance = self.arrow(before.mark, wrap(after.mark))
        close = self.arrow(wrap(after.empty), before.empty)
        return Frame(advance, close, outgoing, returning, birth, death)

    def accept(self, cfg):
        left, q, right = self.parts(cfg)
        gate = identity(self.ctx, self.letters[q])
        erase = self.arrow(self.marks[q], identity(self.ctx, gate))
        return placed(self.ctx, 0, left, erase, right)


def indexed_reading(machine, term, rank, left='', right=''):
    """Read the fixed-whisker fragment used in the frames, retaining the position of a mark."""
    if term[0] == 'v':
        if rank == 1:
            [letter] = [a for a, edge in machine.letters.items() if edge == term]
            return letter
        event = (left, term, right)
        return (event,) if rank == 2 else (((), event, ()),)
    slots = maximal_vars(term[1])
    if len(slots) == 1:  # Identity on a lower slot.
        return '' if rank == 1 else ()
    a, b = (term[3][i] for i in slots)
    p, q = (tdim(term[1][i]) + 1 for i in slots)
    if p == q:
        return indexed_reading(machine, a, rank, left, right) + indexed_reading(machine, b, rank, left, right)
    if p == 1:
        return indexed_reading(machine, b, rank, left + indexed_reading(machine, a, 1), right)
    if q == 1:
        return indexed_reading(machine, a, rank, left, indexed_reading(machine, b, 1) + right)
    assert rank == 3 and {p, q} == {2, 3}
    fixed, moving = (a, b) if p == 2 else (b, a)
    path = indexed_reading(machine, fixed, 2, left, right)
    history = indexed_reading(machine, moving, 3, left, right)
    if p == 2:
        return tuple((path + prefix, event, suffix) for prefix, event, suffix in history)
    return tuple((prefix, event, suffix + path) for prefix, event, suffix in history)


def raw_check(emitter):
    machine = Machine('ab', 'STH')
    first = machine.frame('S', 'aTb')
    second = machine.frame('aTb', 'H')
    erase = machine.accept('H')
    ctx = machine.ctx
    check_ctx(ctx)
    step = second.propagate(ctx, erase)
    result = first.propagate(ctx, step)
    for name, cfg, proof in (('accept', 'H', erase), ('inner', 'aTb', step), ('outer', 'S', result)):
        query = machine.query(cfg)
        assert (src(ctx, proof), tgt(ctx, proof)) == (query.mark, query.empty)
        emitter.check_type(name, ctx, proof, arr(infer(ctx, query.mark), query.mark, query.empty))
    left, right = machine.tape_term('ab'), machine.tape_term('ba')
    outer = placed(ctx, 0, left, result, right)
    query = machine.query('S')
    start, end = (placed(ctx, 0, left, cell, right) for cell in (query.mark, query.empty))
    assert (src(ctx, outer), tgt(ctx, outer)) == (start, end)
    emitter.check_type('exterior', ctx, outer, arr(infer(ctx, start), start, end))
    # Read a proper substring step independently at its grouped and ungrouped
    # writings. The successor's erasure must be placed between precisely c,d.
    for outside_left in ('', 'a', 'ab'):
        for outside_right in ('', 'b', 'ba'):
            lo, hi = map(machine.tape_term, (outside_left, outside_right))
            def exterior(cell):
                return indexed_reading(machine, placed(ctx, 0, lo, cell, hi), 3)
            actual = exterior(tgt(ctx, first.advance))
            successor = machine.query(outside_left + 'aTb' + outside_right)
            [(no_prefix, mark, no_suffix)] = indexed_reading(machine, successor.mark, 3)
            assert no_prefix == no_suffix == ()
            prefix = ((outside_left, first.outgoing, outside_right),)
            suffix = ((outside_left, first.returning, outside_right),)
            assert actual[1] == (prefix, mark, suffix)
            assert actual[:1] + actual[2:] == exterior(src(ctx, first.close))
            start = machine.query(outside_left + 'S' + outside_right)
            assert exterior(src(ctx, first.advance)) == indexed_reading(machine, start.mark, 3)
            assert exterior(tgt(ctx, first.close)) == indexed_reading(machine, start.empty, 3) == ()
    print('Gray terms generated for acceptance, two nested rule frames, and an exterior placement.')


def suspended_check(emitter):
    machine = Machine('', 'SH')
    frame = machine.frame('S', 'H')
    after = machine.query('H')
    assumption = machine.arrow(after.mark, after.empty)
    proof = frame.propagate(machine.ctx, assumption)
    before = machine.query('S')
    target = arr(infer(machine.ctx, before.mark), before.mark, before.empty)
    ctx = susp_ctx(machine.ctx)
    value, ty = susp_tm(proof), susp_ty(target)
    check_ctx(ctx)
    assert infer(ctx, value) == ty
    emitter.check_type('propagate', ctx, value, ty)


def compose(a, b):
    """Apply finite-state transition a, then b."""
    return tuple(b[i] for i in a)


def finite_model_check():
    # Keep the parity of a-prefixes and b-suffixes, in a noncommutative
    # transition monoid that also records the effect of reset letters.
    identity_map = (0, 1)
    letter = {'a': (1, 0), 'b': (1, 0), 'e': identity_map, 'r': (0, 0)}
    monoid = {identity_map}
    while True:
        extended = monoid | {compose(x, y) for x in monoid for y in letter.values()}
        if extended == monoid:
            break
        monoid = extended
    assert len(monoid) == 4

    def grade(word):
        value = identity_map
        for a in word:
            value = compose(value, letter[a])
        return value

    def membership(l, q, r):
        return q in 'ST' and r[l[0]] == 0

    def vector(l, q, r):
        return frozenset((a, b) for a, b in product(monoid, repeat=2)
                         if membership(compose(a, l), q, compose(r, b)))

    def act(l, r, mask):
        return frozenset((a, b) for a, b in product(monoid, repeat=2)
                         if (compose(a, l), compose(r, b)) in mask)

    moves = [(('a', 'S', ''), ('', 'T', 'b')), (('r', 'T', ''), ('r', 'S', 'e')), (('', 'U', ''), ('', 'S', ''))]
    for (l, q, r), (l2, q2, r2) in moves:
        assert vector(grade(l), q, grade(r)) <= vector(grade(l2), q2, grade(r2))
    trials = 0
    for l, r in product(monoid, repeat=2):
        for q in 'STH':
            mask = vector(l, q, r)
            for a, b in product(monoid, repeat=2):
                assert act(a, b, mask) == vector(compose(a, l), q, compose(r, b))
                assert act(a, b, mask | vector(r, q, l)) == act(a, b, mask) | act(a, b, vector(r, q, l))
                trials += 1
    assert vector(identity_map, 'U', identity_map) < vector(identity_map, 'S', identity_map)
    assert not vector(identity_map, 'H', identity_map)
    assert (identity_map, identity_map) in vector(identity_map, 'S', identity_map)
    print(f'Validated both exterior actions and union on {trials} indexed Boolean weights.')


def pump_check():
    rules = [('S', 'aSb'), ('S', 'T'), ('aTb', 'T'), ('aTr', 'Hk'), ('lTb', 'Hk')]

    def successors(word):
        return {word[:i] + v + word[i + len(u):] for u, v in rules
                for i in range(len(word)) if word.startswith(u, i)}

    for n in range(9):
        for q in ('S', 'T'):
            word = 'l' + n * 'a' + q + n * 'b' + 'r'
            for result in successors(word):
                assert 'H' not in result and result.count('a') == result.count('b')
    trials = 0
    for size in range(1, 5):
        for advance in product(range(size), repeat=size):
            for start in range(size):
                orbit = [start]
                for _ in range(size):
                    orbit.append(advance[orbit[-1]])
                j = next(j for j in range(1, len(orbit)) if orbit[j] in orbit[:j])
                i = orbit.index(orbit[j])
                long = 'l' + j * 'a' + 'S' + j * 'b' + 'r'
                short = 'l' + i * 'a' + 'S' + j * 'b' + 'r'
                assert long != short and orbit[i] == orbit[j]
                short = short.replace('S', 'T')
                for _ in range(i):
                    [short] = successors(short)
                assert any('H' in outcome for outcome in successors(short))
                trials += 1
    print(f'Checked the accepting mismatch for all {trials} pointed unary automata through four states.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--agda-dir', type=Path)
    args = parser.parse_args()
    emitter = Emitter()
    raw_check(emitter)
    suspended = Emitter()
    suspended_check(suspended)
    finite_model_check()
    pump_check()
    if args.agda_dir:
        args.agda_dir.mkdir(parents=True, exist_ok=True)
        module = emitter.module('MarkedComputations', __doc__).replace('open import CaTTExp.Pure',
                                                                      'open import CaTTExp.Gray.Pure')
        (args.agda_dir / 'MarkedComputations.agda').write_text(module)
        module = suspended.module('SuspendedMarkedComputation', __doc__)
        (args.agda_dir / 'SuspendedMarkedComputation.agda').write_text(module)
