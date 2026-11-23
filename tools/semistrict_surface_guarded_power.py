"""Inspect a scalar cube return plus a width-N guarded crossing-power rule."""
from argparse import ArgumentParser
from collections import deque
from itertools import product
from pathlib import Path

from catt import arr, infer, src, v
from emit_agda import Emitter
from relative_coherence_exchange_faces import composite
from relative_coherence_hidden_seam import identity
from semistrict_surface_braid_reflection import positive_moves
from semistrict_surface_scalar_cube import cube_terms
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_three_axis import fitted_crossing


def raw_reaches(width, guard_width, increment, start, goal):
    """Exhaust positive moves up to the target length; an increase cannot be undone."""
    if len(start) > len(goal):
        return False
    pending = deque([start])
    seen = {start}
    while pending:
        word = pending.popleft()
        if word == goal:
            return True
        moves = list(positive_moves(word))
        if len(word) + increment <= len(goal):
            for i, letter in enumerate(word):
                if letter <= width - guard_width + 1:
                    moves.append(word[:i] + (letter,)*increment + word[i:])
        for after in moves:
            if after not in seen:
                seen.add(after)
                pending.append(after)
    return False


def raw_boundary(guard_width, increment):
    ctx, scalar, crossing = fitted_crossing()
    p, q, ty = cube_terms(ctx, v(1), v(1), v(1))
    ctx += (arr(ty, q, p),)
    if guard_width > 2:
        crossing = composite(ctx, 1, [crossing] + [scalar]*(guard_width-2))
    ty = infer(ctx, crossing)
    power = lambda k: composite(ctx, 2, [crossing]*k) if k > 1 else crossing
    ctx += (arr(ty, crossing, power(increment+1)),)
    emitter = Emitter()
    emitter.check_type('guarded-power', ctx, v(3), ctx[3])
    old = arr(ty, identity(ctx, src(ctx,crossing)), power(increment))
    g = emitter.ctx(ctx)
    emitter.checks.append(f'first-failure : {g} ⊢ty {emitter.ty(old)}\n'
                          f'first-failure = from-just (checkTy {g} (from-just (checkCtx {g}))'
                          f' {emitter.ty(old)})\n')
    return emitter


def check():
    count = 0
    for n, N, d in product(range(2,5), range(2,6), range(1,5)):
        words = [w for k in range(min(3, d)+1) for w in product(range(1,n), repeat=k)]
        for s,t in product(words, repeat=2):
            # In these regions every comparison in the signed group must be equality.
            if n < N or max(len(s),len(t)) < d or len(s) == len(t):
                assert raw_reaches(n,N,d,s,t) == (braid_image(n,s) == braid_image(n,t))
                count += 1
        for pos in range(1,n):
            letter = (pos,)
            direct = pos <= n-N+1
            assert raw_reaches(n,N,d,letter,letter*(1+d)) == direct
            assert not raw_reaches(n,N,d,(),letter*d)
    return count


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--family', type=int, nargs=2, default=(4,3), metavar=('WIDTH','INCREASE'))
    parser.add_argument('--agda', type=Path)
    args = parser.parse_args()
    width, increase = args.family
    if width < 2 or increase < 1:
        parser.error('the guard needs at least two strands and a positive increase')
    print(f'{check():,} comparisons agreed with the independent braid action.')
    assert raw_reaches(width,width,increase,(1,), (1,)*(increase+1))
    assert not raw_reaches(width,width,increase,(), (1,)*increase)
    print(f'First failure: width {width}, maximum face length {increase}, empty to crossing^{increase}.')
    if args.agda:
        emitter = raw_boundary(width,increase)
        module = emitter.module(args.agda.stem, 'Old guarded crossing-power declaration and boundary.')
        args.agda.write_text(module.replace('open import CaTTExp.Pure\n','open import CaTTExp.Gray.Pure\n'))


if __name__ == '__main__':
    main()
