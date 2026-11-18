"""Counts for the cospan completion (src/CaTTExp/Join/Cospan.agda) on the K14 comparison graph.

Reuses the round-5 graph (scripts/e6/triple_tensor_r5_check.py), as r7_check.py does.
For a seed alpha : s -> t, a cospan is (I : t -> m, R : u -> m) of inner paths.
 - unreduced: all cospans (the Agda construction);
 - forced (minimal): R nonempty and either I empty (r7's generators) or I nonempty with last(I) != last(R)
   (src/CaTTExp/Join/Forced.agda shows these have no division in r7's completion).
Also checks that every j alpha I R raises the rank phi (acyclicity) by recomputing phi.
Run: python3 scripts/e6/cospan_count.py
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
isucc = defaultdict(list); ipred = defaultdict(list)
for s, t in inner: isucc[s].append(t); ipred[t].append(s)

@functools.lru_cache(None)
def into(m):  # inner paths ending at m, by last edge: dict last-edge -> count; key None = empty path
    d = defaultdict(int); d[None] = 1
    for x in ipred[m]:
        d[(x, m)] += sum(into(x).values())
    return dict(d)

@functools.lru_cache(None)
def outof(t):  # inner paths starting at t, grouped by (end m, last edge)
    d = defaultdict(int); d[(t, None)] = 1
    for y in isucc[t]:
        for (m, le), c in outof(y).items():
            d[(m, le if le is not None else (t, y))] += c
    return dict(d)

r7 = sum(sum(into(t).values()) for s, t in pos)
unreduced = forced = 0
for s, t in pos:
    for (m, li), ci in outof(t).items():
        for lr, cr in into(m).items():
            unreduced += ci * cr
            if lr is None: continue                  # R empty: j = alpha ; I, not new
            if li is None or li != lr: forced += ci * cr
print('seeds', len(pos), 'r7 generators', r7)
print('cospan completion: unreduced generators', unreduced, '(of which R = [] are composites)')
print('forced (minimal natural) joining generators', forced, '+ seeds', len(pos), '=', forced + len(pos))

# rank check: phi constant on inner classes, increasing on positive arrows
par = {w: w for w in W}
def f(x):
    while par[x] != x: par[x] = par[par[x]]; x = par[x]
    return x
for s, t in inner: par[f(s)] = f(t)
succ = defaultdict(set)
for s, t in pos: succ[f(s)].add(f(t))
@functools.lru_cache(None)
def h(c): return 0 if not succ[c] else 1 + max(h(d) for d in succ[c])
phi = {w: -h(f(w)) for w in W}
assert all(phi[s] < phi[t] for s, t in pos)
assert all(phi[s] == phi[t] for s, t in inner)
print('rank phi verified; every cospan generator j : s -> u has phi(u) = phi(t) > phi(s)')
