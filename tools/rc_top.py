"""
The relative-coherence comparison with both descent steps as its
recursion (r9 Responses 3 and 15): a query whose strict value is a genuine
top cell (h = n) goes to the event normalization (`rc_events.normalize`),
any other rank >= 3 query to the oracle and then the single-piece step
(`rc_descent._piece`). Every sub-query of either step comes back here.

  rec(G, A, t, u) -> w : t -> u, or None

Options (module globals): RC_LIMIT, seconds for each outermost oracle
call (rc_heur's local reductions can search for a long time; on timeout
the query goes to the descent); CACHE, a directory of rank >= 3 answers
keyed by sha1 digests (one pickle each), so that a stopped run resumes;
MEM_GB, past which the module memos are dropped; EXIT_GB, past which the
process exits with code 75 for a restart from the cache; LOG, print one
line per rank >= 3 query.
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

class _Disk:
    """Answers on disk, one pickle per query under a directory, with a
    small in-memory window: a run's answers are large shared terms, and
    holding all of them (and pickling them whole) exhausted memory."""
    def __init__(self, path, window=8):
        self.path, self.window, self.mem = path, window, {}
        os.makedirs(path, exist_ok=True)
    def _f(self, k):
        return os.path.join(self.path, hashlib.sha1(b''.join(k)).hexdigest() + '.pkl')
    def __contains__(self, k):
        return k in self.mem or os.path.exists(self._f(k))
    def __getitem__(self, k):
        if k not in self.mem:
            self._keep(k, pickle.load(open(self._f(k), 'rb')))
        return self.mem[k]
    def __setitem__(self, k, w):
        f = self._f(k)
        pickle.dump(w, open(f + '.tmp', 'wb'))
        os.replace(f + '.tmp', f)
        self._keep(k, w)
    def _keep(self, k, w):
        if len(self.mem) >= self.window:
            self.mem.pop(next(iter(self.mem)))
        self.mem[k] = w
    def update(self, d):
        for k, w in d.items():
            self[k] = w

def load_cache(path):
    """path: a directory (answers kept on disk), or a pickle of a dict
    (old format: loaded into the directory path + '.d')."""
    global _C
    if path and os.path.isfile(path):
        old = pickle.load(open(path, 'rb'))
        _C = _Disk(path + '.d')
        _C.update(old)
        del old
    elif path:
        _C = _Disk(path)
    CACHE[0] = path

def _save(force=False):
    """Answers are written as they are found (see _Disk)."""
    pass

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

def restrict(G, A, t, u):
    """rc_oracle.restrict_to with sharing-preserving renaming."""
    import rc_nat as N
    S = R.support(G, set(catt.fv_ty(A)) | set(catt.fv_tm(t)) | set(catt.fv_tm(u)))
    if len(S) == len(G):
        return G, None, A, t, u
    order = sorted(S)
    m = {old: catt.v(new) for new, old in enumerate(order)}
    memo = {}
    rt = lambda x: N.rename_map(x, m, memo)
    def ry(B):
        return B if B == catt.STAR else ('->', ry(B[1]), rt(B[2]), rt(B[3]))
    H = tuple(ry(G[o]) for o in order)
    incl = tuple(catt.v(o) for o in order)
    return H, incl, ry(A), rt(t), rt(u)

def preload(G, A, t, u, w):
    """Put a known answer w : t -> u (checked here) into the cache, under
    the key of its support-restricted query."""
    H, incl, AH, tH, uH = restrict(G, A, t, u)
    if incl is not None:
        raise ValueError('preload: give the answer on the restricted query')
    k = key(H, AH, tH, uH)
    if k in _C:
        return
    assert infer(G, w) == arr(A, t, u), 'preload: ill-typed answer'
    _C[k] = catt.hc(w)

def rec(G, A, t, u):
    """Answered on the dependency-closed support, pulled back."""
    if t == u:
        return R.identity(G, t)
    H, incl, AH, tH, uH = restrict(G, A, t, u)
    w = _rec(H, AH, tH, uH)
    if w is None:
        return None
    return catt.subst_tm(w, incl) if incl is not None else w

MEM_GB = [6.0]
EXIT_GB = [None]   # past this after a trim, exit (code 75): answers so far are on disk
_NEXT = [6.0]

def _rss_gb():
    try:
        with open('/proc/self/statm') as f:
            return int(f.read().split()[1]) * os.sysconf('SC_PAGE_SIZE') / 1e9
    except (OSError, ValueError):
        return 0.0

def _trim():
    """Drop the module memos (each is only a speed-up) when the process
    is past MEM_GB, at a point where no walk that uses them is running."""
    if _armed[0] or R._DEPTH[0] or catt._IDEPTH[0] or _rss_gb() < _NEXT[0]:
        return
    import gc, rc_nat as N
    for f in (catt.tdim, catt.ps_boundary_vars, catt.is_ps, catt._head_ok,
              catt.check_ty_cached, catt.ucomp):
        f.cache_clear()
    catt._HC.clear(); catt._HID.clear(); catt._IDC.clear()
    catt._IDN[0] = 0; N._K.clear(); R._MEMO.clear()
    gc.collect()
    try:
        import ctypes
        ctypes.CDLL('libc.so.6').malloc_trim(0)
    except (OSError, AttributeError):
        pass
    if EXIT_GB[0] and _rss_gb() > EXIT_GB[0]:
        print('trim: rss %.1f GB past EXIT_GB, exiting for a restart' % _rss_gb(), flush=True)
        os._exit(75)
    # what is left is live: trim again only after a further 2 GB
    _NEXT[0] = max(MEM_GB[0], _rss_gb() + 2.0)
    if LOG[0]:
        print('trim: rss %.1f GB' % _rss_gb(), flush=True)

def _rec(H, B, a, b):
    _trim()
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
        if n >= 3:
            # common prefix and suffix first, the middle through this rec
            # (so that cached middles are found)
            try:
                w = R.peel(H, B, a, b, rec)
            except (catt.TypeError_, AssertionError, KeyError, ValueError, TypeError):
                w = None
        if w is None and top and not _armed[0]:
            w = E.normalize(H, B, a, b, rec)
            if w is not None:
                STATS['event'] += 1
        if w is None:
            w = _timed_rc(H, B, a, b)
            if w is not None:
                STATS['rc'] += 1
        if w is None and n >= 3 and not top and not _armed[0]:
            STATS['piece'] += 1
            try:
                w = D._piece(H, B, a, b, rec)
            except (catt.TypeError_, AssertionError, KeyError, ValueError, TypeError):
                w = None
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
