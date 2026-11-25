"""
Horiz3 query (2), the coherence-only cap-block comparison (notes/rc-generator.md §7),
as a reproducible instance for the descent (tools/rc_descent.py).

  python3 tools/rc_query2.py            # pieces of Sd(c) holding both inputs, and the in-arity comparison
  python3 tools/rc_query2.py full [LIMIT] [CACHE]
        # answer the query: rc_descent.piece, whose calls go to the oracle
        # (stopped after LIMIT s, default 120) and, when it fails or times
        # out, to the single-piece step again; answers of the single-piece
        # step are kept in the pickle CACHE if given, so a stopped run resumes.
        # The answer is type-checked against the query at the end.

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
            return w if w is not None else D.descend(H, B, a, b)
        return D.descend(H, B, a, b)
    t0 = time.time()
    try:
        w = D._piece(G, A, t, u, rec)
    except Stop:
        w = None
    if 'W' in timing:
        print('comparison in W (%d variables): %s in %.1f s' % (timing['W'][0], 'answered' if timing['W'][1] else 'FAILED', timing['W'][2]))
    if full:
        print('piece: %s after %.0f s' % ('answered' if w is not None else 'no answer', time.time() - t0))

def full(limit=120, cache=None):
    import signal, pickle, hashlib, catt
    G, A, t, u = load()
    C = {}
    if cache and os.path.exists(cache):
        with open(cache, 'rb') as f:
            C = pickle.load(f)
        hm = {}
        C = {k: catt.hc(w, hm) for k, w in C.items()}
    def dig(x, memo):                       # sharing-aware digest
        r = memo.get(id(x))
        if r is not None:
            return r[1]
        b = (b'(' + b','.join(dig(e, memo) for e in x) + b')') if isinstance(x, tuple) else repr(x).encode()
        d = hashlib.sha1(b).digest()
        memo[id(x)] = (x, d)
        return d
    def key(*xs):
        m = {}
        return tuple(dig(x, m) for x in xs)
    class Timeout(BaseException):
        pass
    def alarm(*_):
        raise Timeout()
    signal.signal(signal.SIGALRM, alarm)
    armed = [False]
    def timed_rc(H, B, a, b):
        if armed[0]:
            return rc(H, B, a, b)
        armed[0] = True
        signal.alarm(limit)
        try:
            return rc(H, B, a, b)
        except Timeout:
            return 'timeout'
        finally:
            signal.alarm(0)
            armed[0] = False
    stats = {'rc': 0, 'piece': 0, 'cached': 0}
    def rec(H, B, a, b):
        n = tdim(B) + 1
        k = key(H, B, a, b) if n >= 3 else None
        if k in C:
            stats['cached'] += 1
            return C[k]
        w = timed_rc(H, B, a, b)
        if w != 'timeout' and (w is not None or n < 2):
            stats['rc'] += 1
            return w
        stats['piece'] += 1
        w = D._piece(H, B, a, b, rec)
        if w is not None and k is not None:
            C[k] = catt.hc(w)
            if cache:
                with open(cache + '.tmp', 'wb') as f:
                    pickle.dump(C, f)
                os.replace(cache + '.tmp', cache)
        return w
    t0 = time.time()
    w = D._piece(G, A, t, u, rec)
    print('piece: %s after %.0f s (oracle answers %d, single-piece steps %d, cached %d)'
          % ('answered' if w is not None else 'no answer', time.time() - t0,
             stats['rc'], stats['piece'], stats['cached']))
    if w is not None:
        catt.INFER_LIMIT[0] = 10 ** 9
        catt._IDC.clear()               # check from an empty memo, as a fresh process would
        catt._IDN[0] = 0
        t0 = time.time()
        ok = infer(G, w) == arr(A, t, u)
        print('answer type-checks as t -> u: %s (%.0f s)' % (ok, time.time() - t0))
    return w

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'full':
        full(int(sys.argv[2]) if len(sys.argv) > 2 else 120, sys.argv[3] if len(sys.argv) > 3 else None)
    else:
        main()
