from catt import *
from rc2 import *
from ladder import ladder, lift_comp
from emit_agda import emit
G, n = ladder(1); V = lambda s: v(n[s])
D1 = tree_ctx(chain_tree(1))
idx = ident(D1, 0)
lsrc = comp2(D1, 0, idx, v(2))
lam = ('coh', D1, arr(infer(D1, lsrc), lsrc, v(2)), (v(0), v(1), v(2)))
side = lambda sg: sub_from(D1, G, {2: V('f1'+sg)})
lm, lp = subst_tm(lam, side('m')), subst_tm(lam, side('p'))
iota = kappa(G, comp2(G,0,ident(G,n['x0m']),V('v0')), comp2(G,0,V('v0'),ident(G,n['x0p'])))
s_up = lift_comp(G, ident(G,n['x0m']), V('f1m'), ident(G,n['x0p']), V('f1p'), V('v0'), V('v1'), iota, V('F1'))
L = comp2(G, 1, comp2(G, 0, lm, V('v1')), V('F1'))
R = comp2(G, 1, s_up, comp2(G, 0, V('v0'), lp))
K = rc2(G, L, R)
open('../src/CaTTExp/Generated/UnitorNaturality.agda','w').write(emit('CaTTExp.Generated.UnitorNaturality', G, K, infer(G,K), 'Left unitor naturality 3-cell at depth 2 over the lax square, built by tools/rc2.py.'))
print('ok')
