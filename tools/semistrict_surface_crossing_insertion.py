"""Check the first failure by strand count for adding one scalar crossing."""
from argparse import ArgumentParser
from collections import deque
from functools import cache
from itertools import product
from pathlib import Path

from catt import arr, comp2, infer, maximal_vars, tree_ctx, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite, head, string_tree
from relative_coherence_hidden_seam import identity
from semistrict_surface_scalar_cube import cube_terms
from semistrict_surface_three_axis import fitted_crossing, specialize

from semistrict_surface_braid_reflection import positive_moves
from semistrict_surface_shared_edge import braid_image


def reverse_search(source, target):
    """Raw reachability by insertion and positive relations, searching from above."""
    if len(source) > len(target):
        return None, {}
    parents = {target: None}
    pending = deque([target])
    while pending:
        w = pending.popleft()
        if w == source:
            path = [w]
            while parents[w] is not None:
                w = parents[w]
                path.append(w)
            return path, parents
        candidates = list(positive_moves(w))
        if len(w) > len(source):
            candidates.extend(w[:i] + w[i+1:] for i in range(len(w)))
        for v in candidates:
            if v not in parents:
                parents[v] = w
                pending.append(v)
    return None, parents


@cache
def b3_step(state, x):
    """Append one positive letter to the classical right-Delta normal form."""
    word, power = state
    new = word + ((3-x if power % 2 else x),)
    if len(new) >= 3 and new[-3] == new[-1] != new[-2]:
        return new[:-3], power+1
    return new, power


def b3_word(word):
    state = ((), 0)
    for x in word:
        state = b3_step(state, x)
    return state


def right_complement(b):
    # b C = Delta^len(b). Move each pending right Delta inverse across
    # the right complement of the next inverse letter in reversed(b).
    factors = []
    for i, x in enumerate(reversed(b)):
        factor = (3-x, x)
        factors.append(tuple(3-j for j in factor) if i % 2 else factor)
    return tuple(factors)


def three_strand_surface(b, c):
    """Orevkov's subword test on c times the positive right complement of b."""
    if len(b) > len(c):
        return False
    full = c + tuple(j for factor in right_complement(b) for j in factor)
    target_size = 3*len(b)
    states = {((), 0)}
    for i, x in enumerate(full):
        states |= {b3_step(s,x) for s in states if len(s[0])+3*s[1] < target_size}
        states = {s for s in states if len(s[0])+3*s[1]+len(full)-i-1 >= target_size}
    return ((), len(b)) in states


def check_complements():
    checks = 0
    D = (1,2,1)
    for size in range(5):
        for b in product((1,2), repeat=size):
            factors = right_complement(b)
            complement = tuple(x for f in factors for x in f)
            assert b3_word(b+complement) == ((),size)
            # Form Delta^p (C')^-1 as a positive product of left complements.
            for choices in product(range(4),repeat=size):
                surviving = []
                upgraded = []
                for i,(factor,mask) in enumerate(zip(reversed(factors),reversed(choices))):
                    sub = tuple(x for j,x in enumerate(factor) if mask & (1<<j))
                    surviving[:0] = sub
                    # Enumerate the small left divisor of Delta, choosing a
                    # spelling containing the original letter of b at this slot.
                    variants = [w for w in product((1,2),repeat=3-len(sub)) if b3_word(w+sub) == ((),1)]
                    # Delta^p f_p^-1 ... f_1^-1 twists the first complement p-1 times.
                    variants = [tuple(3-x for x in w) if (size-1-i)%2 else w for w in variants]
                    upgraded.extend(next(w for w in variants if b[i] in w))
                assert b3_word(tuple(upgraded)+tuple(surviving)) == ((),size)
                checks += 1
    return checks


def check_four():
    u = tuple(map(int,'321111'))
    v = tuple(map(int,'21322132'))
    cert, explored = reverse_search(u,v)
    assert cert is None
    frontier = [sum(len(w)==k for w in explored) for k in (8,7,6)]
    # Independently close equality using Artin images instead of local moves:
    # enumerate *all* positive words at each permitted length, then erase a letter.
    keys = {braid_image(4,v)}
    for size in (8,7,6):
        representatives = [w for w in product((1,2,3),repeat=size) if braid_image(4,w) in keys]
        assert set(representatives) == {w for w in explored if len(w)==size}
        if size > 6:
            keys = {braid_image(4,w[:i]+w[i+1:]) for w in representatives for i in range(size)}
    prefix = (1,)
    cert, _ = reverse_search(prefix+u, prefix+v)
    assert cert is not None
    assert sum(len(t)>len(s) for s,t in zip(cert,cert[1:])) == 2
    print(f'Four-strand reverse frontiers at lengths 8, 7, 6: {frontier}.')
    print('Prefixed raw certificate:', ' -> '.join(''.join(map(str,w)) for w in cert))


def raw_four():
    ctx, stationary, crossing = fitted_crossing()
    p, q, ty = cube_terms(ctx, v(1), v(1), v(1))
    loop_face = infer(ctx, crossing)[2]
    empty = identity(ctx, loop_face)
    ctx += (arr(ty, q, p), arr(infer(ctx, crossing), empty, crossing))
    arity = tree_ctx(string_tree(1, [2]*4))
    slots = tuple(map(v, maximal_vars(arity)))
    outside = composite(arity, 1, slots)
    letters = []
    emitter = Emitter()
    target = composite(ctx, 1, [stationary]*4)
    loop_type = arr(infer(ctx, target), target, target)
    for i in range(3):
        pair = comp2(arity, 1, slots[i], slots[i+1])
        grouped = composite(arity, 1, slots[:i] + (pair,) + slots[i+2:])
        move = composite(ctx, 1, [stationary]*i + [crossing] + [stationary]*(2-i))
        if grouped != outside:
            enter, leave = [specialize(head(arity,s,t), arity, ctx, [stationary]*4)
                            for s,t in ((outside,grouped), (grouped,outside))]
            move = composite(ctx, 2, [enter,move,leave])
        assert infer(ctx, move) == loop_type
        emitter.check_type('crossing-' + str(i+1), ctx, move, loop_type)
        letters.append(move)
    s,t = [composite(ctx, 2, [letters[int(c)-1] for c in word]) for word in ('321111','21322132')]
    expected = arr(loop_type,s,t)
    assert infer(ctx, s) == infer(ctx, t) == loop_type
    g = emitter.ctx(ctx)
    emitter.checks.append(f'old-boundary : {g} ⊢ty {emitter.ty(expected)}\n'
                          f'old-boundary = from-just (checkTy {g} (from-just (checkCtx {g}))'
                          f' {emitter.ty(expected)})\n')
    return emitter


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--three', nargs=2, metavar=('SOURCE','TARGET'))
    parser.add_argument('--agda', type=Path, help='emit the old four-strand boundary for the Gray kernel')
    args = parser.parse_args()
    if args.three:
        if any(set(w)-set('12') for w in args.three):
            parser.error('three-strand words use the crossing positions 1 and 2')
        b,c = (tuple(map(int,w)) for w in args.three)
        print('raw and surface comparison exists' if three_strand_surface(b,c) else 'comparison absent')
        return
    print(f'{check_complements():,} split complements verified.')
    # Cross-check the independent subword and contextual reachability decisions.
    classes = {b3_word(w): w for n in range(7) for w in product((1,2),repeat=n)}
    checks = 0
    for b,c in product(classes.values(),repeat=2):
        if len(b) <= len(c):
            assert three_strand_surface(b,c) == (reverse_search(b,c)[0] is not None)
            checks += 1
    print(f'{checks:,} independent three-strand decisions agreed.')
    check_four()
    emitter = raw_four()
    if args.agda:
        module = emitter.module(args.agda.stem, 'Old four-strand insertion boundary.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n','open import CaTTExp.Gray.Pure\n'))


if __name__ == '__main__':
    main()
