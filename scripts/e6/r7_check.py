"""Independent re-check of parts of the E6 round-7 researcher response.

Reuses the round-5 graph construction (scripts/e6/triple_tensor_r5_check.py), then checks:
 - section 1: counts of the source-only joining completion (inner arrows, positive seeds,
   positive generators after completion = sum over positive arrows of #inner paths ending at the
   target), and the rank hypothesis (positive arrows acyclic between inner classes, rank range);
 - section 2: the five-word counterexample (arrow kinds and directions, tau = h_z ; f);
 - section 3: the critical-pair arrows;
 - section 6: the routes (13)-(15) used for A_{2,1} are arrows of the graph.
Run: python3 scripts/e6/r7_check.py
"""
import io, contextlib, functools, runpy, os
from collections import defaultdict
here = os.path.dirname(os.path.abspath(__file__))
with contextlib.redirect_stdout(io.StringIO()):
    g = runpy.run_path(os.path.join(here, 'triple_tensor_r5_check.py'))
W, E, arr, label = g['W'], g['E'], g['arr'], g['label']
kind = {}
for k, s, t, i in E: kind.setdefault((s, t), k)
for a in arr:
    if a not in kind: kind[a] = label[a]
inner = [a for a in arr if kind[a] == 'inner']
pos = [a for a in arr if kind[a] != 'inner']
print('section 1: vertices', len(W), 'inner arrows', len(inner), 'positive seeds', len(pos))
isucc = defaultdict(list); ipred = defaultdict(list)
for s, t in inner: isucc[s].append(t); ipred[t].append(s)
@functools.lru_cache(None)
def npaths_to(t):  # number of inner paths (incl. empty) ending at t
    return 1 + sum(npaths_to(s) for s in ipred[t])
J = sum(npaths_to(t) for s, t in pos)
print('  positive generators after completion', J, 'new', J - len(pos), 'total arrows', J + len(inner))
# rank: inner classes, positive arrows between classes acyclic
par = {w: w for w in W}
def f(x):
    while par[x] != x: par[x] = par[par[x]]; x = par[x]
    return x
for s, t in inner: par[f(s)] = f(t)
cls = {f(w) for w in W}
cs = defaultdict(set)
for s, t in pos:
    assert f(s) != f(t), 'positive arrow inside an inner class'
    cs[f(s)].add(f(t))
rank = {}
def r(c):
    if c in rank: return rank[c]
    rank[c] = -1
    v = 0
    for d in cs[c]:
        assert rank.get(d) != -1, 'cycle'
        v = max(v, r(d) + 1)
    rank[c] = v; return v
for c in cls: r(c)
# phi must increase along positive arrows: use longest-path-to-sink reversed
print('  inner classes', len(cls), 'class graph acyclic, longest positive chain', max(rank.values()))
def show(s, t): return (s, t, kind.get((s, t), 'NOT AN ARROW'))
print('section 2:')
for a in [('abpcqr','abcpqr'),('abcpqr','bacpqr'),('abpcqr','bapcqr'),('bapcqr','bacpqr'),('bacrqp','bapcqr')]:
    print('  ', show(*a))
print('   tau x->v present before h_z elimination:', any(k=='tau' and s=='bacrqp' and t=='bacpqr' for k,s,t,i in E))
print('section 3:')
for a in [('bapcqr','bapqcr'),('abpqcr','bapqcr'),('abpqcr','abpqrc')]:
    print('  ', show(*a))
print('section 6 routes:')
routes = [['crqbpa','crqpba','crqpab'],
          ['crqpab','pcqrab','pcqarb','pacqrb','apcqrb'],
          ['crqpab','crqapb','acrqpb','apcqrb'],
          ['apcqrb','apqcrb','apqbcr','apqbrc'],
          ['apcqrb','acpqrb','capqrb']]
for rt in routes:
    print('  ', [show(rt[i], rt[i+1])[2] for i in range(len(rt)-1)])
