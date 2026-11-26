"""
The oracle loop for ConeRCS cones, run on the Python mirror (cone_rcs.py)
instead of the compiled Agda driver.

  python3 tools/cone_rcs_loop.py OUT.pkl [CACHE_DIR] [--check AGDA_ANSWERED.pkl]

Repeats: compute the construction's first unanswered query on Horiz3
(oracle = the answers so far, then RC(1) as in `TBL orRC rc1`), answer it
with rc_top.rec (answers kept in CACHE_DIR, so a run stopped by its memory
guard resumes), until the construction returns a cone. Writes
(answered, cone_ctx) to OUT.pkl, where answered is the list of
(G, A, t, u, w) in query order: the table the Agda cone needs.

--check compares the queries with those of an rc_loop.py run of the Agda
driver (its answered.pkl), round by round, using that run's answers.
"""
import sys, os, pickle, time, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(1000000)
import catt, cone_rcs as C

def digest(x, memo):
    r = memo.get(id(x))
    if r is not None:
        return r[1]
    b = (b'(' + b','.join(digest(e, memo) for e in x) + b')') if isinstance(x, tuple) else repr(x).encode()
    d = hashlib.sha1(b).digest()
    memo[id(x)] = (x, d)
    return d

def key(q):
    m = {}
    return tuple(digest(x, m) for x in q)

def run(shape, answer, table=None, log=print):
    """answer(G, A, t, u) -> w or None. table: list of (G, A, t, u, w) to start from."""
    answered = list(table or [])
    T = {key(r[:4]): catt.hc(r[4]) for r in answered}
    def oracle(G, A, t, u):
        w = T.get(key((G, A, t, u)))
        return w if w is not None else C.rc1(G, A, t, u)
    while True:
        t0 = time.time()
        out = C.cone_out(shape, oracle)
        if out[0] != 'miss':
            log('construction: %s after %d answers' % (out[0], len(answered)))
            return answered, (out[1] if out[0] == 'ret' else None)
        q = out[1]
        log('round %d: query in %.1f s (|G| = %d)' % (len(answered), time.time() - t0, len(q[0])))
        t0 = time.time()
        w = answer(*q)
        if w is None:
            log('round %d: unanswered' % len(answered))
            return answered, None
        log('round %d: answered in %.0f s' % (len(answered), time.time() - t0))
        answered.append(q + (w,))
        T[key(q)] = catt.hc(w)

def check(shape, agda_answered, log=print):
    """Do the mirror's queries equal the Agda driver's, round by round?"""
    T = {}
    def oracle(G, A, t, u):
        w = T.get(key((G, A, t, u)))
        return w if w is not None else C.rc1(G, A, t, u)
    for i, row in enumerate(agda_answered):
        q = C.first_miss(shape, oracle)
        if q is None or key(q) != key(row[:4]):
            log('round %d: DIFFERS from the Agda driver' % i)
            return False
        T[key(row[:4])] = catt.hc(row[4])
    log('all %d queries equal the Agda driver\'s' % len(agda_answered))
    return True

if __name__ == '__main__':
    args = sys.argv[1:]
    if '--check' in args:
        i = args.index('--check')
        agda = pickle.load(open(args[i + 1], 'rb'))[0]
        sys.exit(0 if check(C.HORIZ3, agda) else 1)
    out = args[0]
    import rc_top
    catt.INFER_LIMIT[0] = 10 ** 9
    if len(args) > 1:
        rc_top.load_cache(args[1])
    rc_top.EXIT_GB[0] = 10
    answered, K = run(C.HORIZ3, rc_top.rec, log=lambda s: print(s, flush=True))
    with open(out, 'wb') as f:
        pickle.dump((answered, K.evCtx() if K is not None else None), f)
