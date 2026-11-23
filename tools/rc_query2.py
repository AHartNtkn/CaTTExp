"""
Horiz3 query (2), the coherence-only cap-block comparison (notes/rc-generator.md §7),
as a reproducible instance for the descent (tools/rc_descent.py).

  python3 tools/rc_query2.py            # pieces of Sd(c) holding both inputs, and the in-arity comparison
  python3 tools/rc_query2.py full       # also run rc_descent.piece (expected: does not finish yet)

Reports: the number of factors of each input along the top cut, the elements
of Sd(c) whose piece holds both inputs, and the time of the comparison of
R(t) with R(u) in the pasting arity W.
"""
import os, sys, gzip, ast, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(100000)
from rc_oracle import *
import steiner as St
import rc_descent as D

def load():
    fx = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fixtures', 'rc_horiz3_query2.txt.gz')
    with gzip.open(fx, 'rt') as f:
        return ast.literal_eval(f.read())

def main(full=False):
    G, A, t, u = load()
    n = tdim(A) + 1
    K = St.Complex(G)
    c = St.base_cell(St.image_to_cell(strict_image(G, t)))
    print('context %d variables, strong Steiner %s, input rank %d, h %d'
          % (len(G), K.is_strong_steiner(), n, St.intrinsic_rank(c)))
    print('factors along the top cut: t %d, u %d' % (len(vfactors(G, t, n)), len(vfactors(G, u, n))))
    elems, _ = St.Sd(K, c)
    hold = []
    S = St.support(K, c)
    lab = lambda x: St.base_cell(St.image_to_cell(strict_image(G, x)))
    def in_U(x, gen, memo):
        if x in memo:
            return memo[x]
        l = lab(x)
        if l not in gen:
            r = False
        elif St.support(K, l) != S:
            r = True
        elif x[0] == 'coh' and all(lab(e) in gen for e in x[3]):
            r = all(in_U(e, gen, memo) for e in x[3])
        else:
            r = False
        memo[x] = r
        return r
    for j, (tl, gen) in enumerate(elems):
        if in_U(t, gen, {}) and in_U(u, gen, {}):
            hold.append(j)
    print('|Sd(c)| = %d; pieces holding both inputs: %s' % (len(elems), hold))
    # the in-arity comparison: intercept the first rank-n call made in W
    timing = {}
    class Stop(Exception):
        pass
    def rec(H, B, a, b):
        if tdim(B) + 1 == n and 'W' not in timing:
            t0 = time.time()
            w = rc(H, B, a, b)
            timing['W'] = (len(H), w is not None, time.time() - t0)
            if not full:
                raise Stop
            return w
        return rc(H, B, a, b)
    t0 = time.time()
    try:
        w = D._piece(G, A, t, u, rec)
    except Stop:
        w = None
    if 'W' in timing:
        print('comparison in W (%d variables): %s in %.1f s' % (timing['W'][0], 'answered' if timing['W'][1] else 'FAILED', timing['W'][2]))
    if full:
        print('piece: %s after %.0f s' % ('answered' if w is not None else 'no answer', time.time() - t0))

if __name__ == '__main__':
    main(len(sys.argv) > 1 and sys.argv[1] == 'full')
