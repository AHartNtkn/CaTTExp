"""
Regression checks for the top-rank step (tools/rc_events.py, r9 Response 3).

  python3 tools/rc_events_selftest.py          # the small cases (seconds)
  python3 tools/rc_events_selftest.py cow17    # also the round-21 change of
                                               # writing (fixture, long)

Each case asserts that rc_events.normalize answers, that the answer has the
type t -> u, and that the step did the work it is meant to do (a swap, a
change of writing), not a fallback.
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(1000000)
from rc_oracle import *
import rc_events as E, rc_top, rc_selftest as ST

def globes3():
    """Two 3-globes side by side: A : alpha => alpha' over f, f' : x -> y and
    B : beta => beta' over g, g' : y -> z."""
    S1 = arr(STAR, v(0), v(1)); G = [STAR, STAR, S1, S1]
    S2 = arr(S1, v(2), v(3)); G += [S2, S2, arr(S2, v(4), v(5))]
    T1 = arr(STAR, v(1), v(7)); G += [STAR, T1, T1]
    T2 = arr(T1, v(8), v(9)); G += [T2, T2, arr(T2, v(10), v(11))]
    return tuple(G)

def triangle3():
    """rc_selftest.triangle (a 2-cell a : h => f * g with a composite target,
    b : g => g') with a 3-cell B : b => b2 on top."""
    H = list(ST.triangle())
    H.append(H[8]); H.append(arr(H[8], v(8), v(13)))
    return tuple(H)

def cases():
    out = []
    G = globes3()
    c = lambda k, a, b: comp2(G, k, a, b)
    t = c(2, c(0, v(6), v(10)), c(0, v(5), v(12)))
    u = c(2, c(0, v(4), v(12)), c(0, v(6), v(11)))
    out.append(('swap-two-globes', G, t, u, 'swap'))
    H = triangle3()
    c = lambda k, a, b: comp2(H, k, a, b)
    fB = c(0, v(2), v(14))
    t = c(1, v(6), fB)
    u0 = c(1, c(1, v(6), identity(H, c(0, v(2), v(4)))), fB)
    K = rc(H, infer(H, src(H, t)), src(H, t), src(H, u0))
    K2 = rc(H, infer(H, tgt(H, u0)), tgt(H, u0), tgt(H, t))
    u = c(2, K, c(2, u0, K2))
    out.append(('change-of-writing', H, t, u, 'square'))
    out.append(('change-of-writing-rev', H, u, t, 'square'))
    return out

def _fixture(name):
    import gzip, ast
    fx = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fixtures', name)
    with gzip.open(fx, 'rt') as f:
        return ast.literal_eval(f.read())

def small_fixture_cases():
    # a sub-query of the round-21 run: an event factor whose top slot holds
    # an old cell composed with the event, so the event's composite source
    # is not a face of the head until the head is distributed (unfold)
    G, A, t, u = _fixture('rc_round21_unfold15.txt.gz')
    out = [('round21-unfold', G, t, u, 'unfold')]
    # a sub-query of the round-21 run whose sort moves L_e past an old block
    # that writes f's composite source (a rebracketing creates it): the
    # block is pulled back across L_e by its oplax square along e first
    G, A, t, u = _fixture('rc_round21_pull17.txt.gz')
    out.append(('round21-pull-back', G, t, u, 'pull'))
    return out

def fixture_cases():
    G, A, t, u = _fixture('rc_round21_cow17.txt.gz')
    return [('round21-cow17', G, t, u, 'square')]

def run(cs):
    ok = True
    for name, G, t, u, need in cs:
        A = infer(G, t)
        for k in E.STATS:
            E.STATS[k] = 0
        T = time.time()
        w = E.normalize(G, A, t, u, rc_top.rec)
        good = w is not None and infer(G, w) == arr(A, t, u) and E.STATS.get(need, 0) > 0
        print('%-24s %s (%.0f s, %s)' % (name, 'answered' if good else 'FAILED', time.time() - T, dict(E.STATS)), flush=True)
        ok &= good
    return ok

if __name__ == '__main__':
    cs = cases() + small_fixture_cases()
    if 'cow17' in sys.argv[1:]:
        cs += fixture_cases()
    sys.exit(0 if run(cs) else 1)
