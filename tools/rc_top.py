"""
The relative-coherence comparison with both descent steps as its
recursion (r9 Responses 3 and 15): a query whose strict value is a genuine
top cell (h = n) goes to the event normalization (`rc_events.normalize`),
any other rank >= 3 query to the oracle and then the single-piece step
(`rc_descent._piece`). Every sub-query of either step comes back here.

  rec(G, A, t, u) -> w : t -> u, or None

Options (module globals): RC_LIMIT, seconds for each outermost oracle
call (rc_heur's local reductions can search for a long time; on timeout
the query goes to the descent); CACHE, a path for a pickle of rank >= 3
answers keyed by sha1 digests, so that a stopped run resumes; LOG, print
one line per rank >= 3 query.
"""
import sys, os, pickle, time, hashlib, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import catt
import rc_oracle as R, rc_events as E, rc_descent as D
from catt import tdim, infer, arr

RC_LIMIT = [120]
CACHE = [None]
LOG = [False]
STATS = {'rc': 0, 'piece': 0, 'event': 0, 'cached': 0, 'fail': 0}
_C = {}

def _dig(x, memo):
    r = memo.get(id(x))
    if r is not None:
        return r[1]
    b = (b'(' + b','.join(_dig(e, memo) for e in x) + b')') if isinstance(x, tuple) else repr(x).encode()
    d = hashlib.sha1(b).digest()
    memo[id(x)] = (x, d)
    return d

def key(*xs):
    m = {}
    return tuple(_dig(x, m) for x in xs)

def load_cache(path):
    CACHE[0] = path
    if path and os.path.exists(path):
        _C.update(pickle.load(open(path, 'rb')))

def _save():
    if CACHE[0]:
        pickle.dump(_C, open(CACHE[0] + '.tmp', 'wb'))
        os.replace(CACHE[0] + '.tmp', CACHE[0])

class _Timeout(BaseException):
    pass

def _alarm(*_):
    raise _Timeout()

_armed = [False]

def _timed_rc(H, B, a, b):
    """The oracle; the outermost call is stopped after RC_LIMIT seconds."""
    if _armed[0] or not RC_LIMIT[0]:
        return R.rc(H, B, a, b)
    old = signal.signal(signal.SIGALRM, _alarm)
    _armed[0] = True
    signal.alarm(RC_LIMIT[0])
    try:
        return R.rc(H, B, a, b)
    except _Timeout:
        return None
    finally:
        signal.alarm(0)
        _armed[0] = False
        signal.signal(signal.SIGALRM, old)

_DEPTH = [0]

def rec(H, B, a, b):
    n = tdim(B) + 1
    k = key(H, B, a, b) if n >= 3 else None
    if k is not None and k in _C:
        STATS['cached'] += 1
        return _C[k]
    _DEPTH[0] += 1
    T = time.time()
    try:
        top = n >= 3 and bool(R.top_chain(H, a))
        w = None
        if top and not _armed[0]:
            w = E.normalize(H, B, a, b, rec)
            if w is not None:
                STATS['event'] += 1
        if w is None:
            w = _timed_rc(H, B, a, b)
            if w is not None:
                STATS['rc'] += 1
        if w is None and n >= 3 and not top and not _armed[0]:
            STATS['piece'] += 1
            w = D._piece(H, B, a, b, rec)
        if LOG[0] and n >= 3:
            print('  ' * _DEPTH[0] + 'rec n=%d |H|=%d top=%s -> %s %.0fs' % (n, len(H), top, w is not None, time.time() - T), flush=True)
        if w is None:
            STATS['fail'] += 1
        elif k is not None:
            _C[k] = catt.hc(w)
            _save()
        return w
    finally:
        _DEPTH[0] -= 1
