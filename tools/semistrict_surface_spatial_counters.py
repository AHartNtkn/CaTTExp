"""Compile a two-counter machine into the fixed spatial degree-four query.

--program accepts a JSON list of [source, operation, counter, target].
Operations are inc, dec (positive branch), zero, and goto (counter ignored).
States 0 and 1 are the initial and accepting states. Both counters start and
finish at zero. --emit writes the presentation for semistrict_surface_scalar_sites.
"""
import argparse
import json
from itertools import product
from pathlib import Path

from semistrict_surface_braid_reflection import follow
from semistrict_surface_return_gaps import exchange_at
from semistrict_surface_scalar_sites import decide

MARKS = {'a': ('', '')}
INITIAL = (1, 2, 1, 0)
MIDDLE = (1, 1, 2, 0)
FINAL = (1, 0, 1, 2)
P, Q = (2,), (3, 2)


def protected(n):
    return P + (1,)*n + Q


def history(sites):
    return tuple((i, 'a') for i in sites)


def together(words):
    return tuple(x+4*i for i, w in enumerate(words) for x in w)


def faces(portions):
    """An exact guard spans the block, an ordinary guard uses its middle."""
    sites, left, right = [], [], []
    for i, (exact, a, b) in enumerate(portions):
        sites.extend(s+3*i for s in (INITIAL if exact else MIDDLE))
        left.append(protected(a) if exact else (1,)*a)
        right.append(protected(b) if exact else (1,)*b)
    h, l, r = history(sites), together(left), together(right)
    assert follow(h, l, MARKS) == follow(h, r, MARKS)
    return dict(root='v', path='f'*8, history=h, left=l, right=r)


def portions(instruction):
    source, op, counter, dest = instruction
    if min(source, dest) < 0 or op not in ('inc', 'dec', 'zero', 'goto') or counter not in (0, 1):
        raise ValueError('invalid two-counter instruction')
    parts = [(True, source, dest), (False, 0, 0), (False, 0, 0)]
    if op != 'goto':
        parts[counter+1] = (op == 'zero', int(op == 'dec'), int(op == 'inc'))
    return parts


def compile_program(instructions):
    # This inaccessible exact control supplies a signed +1 even on rejecting programs.
    dead = 1+max([1]+[q for u, _, _, v in instructions for q in (u,v)])
    rules = [faces(portions(rule)) for rule in [*instructions, (dead,'goto',0,dead+1)]]
    return dict(edges={'f': ('v','v')}, scalars={'a':'v'}, rules=rules,
                query=faces([(True,0,1), (True,0,0), (True,0,0)]))


def apply_at_configuration(marks, parts):
    before, after = [], []
    prefix, suffix = [], []
    new = []
    for value, (exact, a, b) in zip(marks, parts):
        if value < a or (exact and value != a):
            return None
        prefix.append(() if exact else P+(1,)*(value-a))
        suffix.append(() if exact else Q)
        before.append(protected(a) if exact else (1,)*a)
        after.append(protected(b) if exact else (1,)*b)
        new.append(value-a+b)
    # Each of the equalities below uses only distant moves between different
    # four-event blocks. Within each block the literal spelling stays fixed.
    init = history(tuple(s+3*i for i in range(3) for s in INITIAL))
    prefixed = together(prefix)
    rule = faces(parts)
    assert follow(init, prefixed, MARKS) == rule['history']
    for v, words, face in ((marks, before, 'left'), (new, after, 'right')):
        spelling = prefixed + rule[face] + together(suffix)
        assert rule[face] == together(words)
        assert follow(init, spelling, MARKS) == history(tuple(s+3*i for i in range(3) for s in FINAL))
        for i, val in enumerate(v):
            projection = tuple(x-4*i for x in spelling if 4*i < x < 4*i+4)
            assert projection == protected(val)
    return tuple(new)


def local_guards():
    # Enumerate all positive paths with these counts, including every possible
    # cube spelling. Test a factor at its actual input history in each spelling.
    initial, final = history(INITIAL), history(FINAL)
    exact_queries = 0
    for count in range(6):
        todo = [(initial, ())]
        for _ in range(len(P)+len(Q)+count):
            following = []
            for h, w in todo:
                for i in (1,2,3):
                    v = exchange_at(h,i-1,MARKS)
                    if v is not None:
                        following.append((v,w+(i,)))
            todo = following
        old = [w for h, w in todo if h == final]
        for exact, a in product((False,True), range(6)):
            word = protected(a) if exact else (1,)*a
            start = initial if exact else history(MIDDLE)
            occurrence = any(w[i:i+len(word)] == word and follow(initial,w[:i],MARKS) == start
                             for w in old for i in range(len(w)-len(word)+1))
            assert occurrence == (count == a if exact else count >= a)
            exact_queries += 1
    return exact_queries


def checks():
    local = local_guards()
    checked = 0
    for src, dest, op, i in product(range(3), range(3), ('inc','dec','zero','goto'), range(2)):
        inst = (src,op,i,dest)
        parts = portions(inst)
        for state in product(range(3), repeat=3):
            possible = (state[0] == src and (op != 'zero' or state[i+1] == 0)
                        and (op != 'dec' or state[i+1] > 0))
            result = apply_at_configuration(state, parts)
            assert (result is not None) == possible
            if possible:
                expected = list(state)
                expected[0] = dest
                expected[i+1] += (op == 'inc') - (op == 'dec')
                assert tuple(expected) == result
            checked += 1
    accepted = [(0,'inc',0,2), (2,'dec',0,3), (3,'zero',0,1)]
    rejected = [(0,'inc',0,2), (2,'zero',0,1)]
    for code, accept in ((accepted,True), (rejected,False)):
        data = compile_program(code)
        assert decide(data)[2] is not None
        state = (0,0,0)
        for inst in code:
            nxt = apply_at_configuration(state, portions(inst))
            if nxt is None:
                break
            state = nxt
        assert (state == (1,0,0)) == accept
    print(f'{local} corridor tests, {checked} compiled instruction/configuration checks, '
          'fixed surface-yes accepting and rejecting examples')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--program', type=Path)
    ap.add_argument('--emit', type=Path)
    args = ap.parse_args()
    if args.program or args.emit:
        if not (args.program and args.emit):
            ap.error('--program and --emit must be supplied together')
        model = compile_program(json.loads(args.program.read_text()))
        assert decide(model)[2] is not None
        args.emit.write_text(json.dumps(model, indent=2)+'\n')
    else:
        checks()
