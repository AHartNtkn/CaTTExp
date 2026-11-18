from catt import *
from rc2 import *

def ladder(m):
    G = []
    names = {}
    def add(name, A):
        names[name] = len(G); G.append(A); return v(len(G)-1)
    def T(): return tuple(G)
    for i in range(m+1):
        xm = add('x%dm'%i, STAR); xp = add('x%dp'%i, STAR)
        add('v%d'%i, arr(STAR, xm, xp))
        if i >= 1:
            fm = add('f%dm'%i, arr(STAR, v(names['x%dm'%(i-1)]), xm))
            fp = add('f%dp'%i, arr(STAR, v(names['x%dp'%(i-1)]), xp))
            Gt = T()
            src_ = comp2(Gt, 0, fm, v(names['v%d'%i]))
            tgt_ = comp2(Gt, 0, v(names['v%d'%(i-1)]), fp)
            add('F%d'%i, arr(infer(Gt, src_), src_, tgt_))
    return T(), names

def lift_comp(G, am, bm, ap, bp, vX, vZ, A, B):
    """naturality 2-cell of a*b: (am*bm)*vZ => vX*(ap*bp), from A: am*vY => vX*ap, B: bm*vZ => vY*bp"""
    c_m = comp2(G, 0, am, bm); c_p = comp2(G, 0, ap, bp)
    s0 = comp2(G, 0, c_m, vZ); t0 = comp2(G, 0, vX, c_p)
    w1 = comp2(G, 0, am, B)          # am*(bm*vZ) => am*(vY*bp)
    w2 = comp2(G, 0, A, bp)          # (am*vY)*bp => (vX*ap)*bp
    k0 = kappa(G, s0, src(G, w1))
    k1 = kappa(G, tgt(G, w1), src(G, w2))
    k2 = kappa(G, tgt(G, w2), t0)
    return lfold(G, 1, [k0, w1, k1, w2, k2])

if __name__ == '__main__':
    import time
    G, n = ladder(3)
    check_ctx(G)
    V = lambda s: v(n[s])
    f, g, h = 1, 2, 3
    m = lambda i: V('f%dm'%i); p = lambda i: V('f%dp'%i)
    Fg = lift_comp(G, m(1), m(2), p(1), p(2), V('v0'), V('v2'), V('F1'), V('F2'))
    Gh = lift_comp(G, m(2), m(3), p(2), p(3), V('v1'), V('v3'), V('F2'), V('F3'))
    s_up = lift_comp(G, comp2(G,0,m(1),m(2)), m(3), comp2(G,0,p(1),p(2)), p(3), V('v0'), V('v3'), Fg, V('F3'))
    t_up = lift_comp(G, m(1), comp2(G,0,m(2),m(3)), p(1), comp2(G,0,p(2),p(3)), V('v0'), V('v3'), V('F1'), Gh)
    # associator over the chain, substituted on each side
    Q = tree_ctx(chain_tree(3))
    sQ = comp2(Q,0,comp2(Q,0,v(2),v(4)),v(6)); tQ = comp2(Q,0,v(2),comp2(Q,0,v(4),v(6)))
    assoc = ('coh', Q, arr(infer(Q,sQ), sQ, tQ), tuple(v(i) for i in range(len(Q))))
    def side(sg):
        return sub_from(Q, G, {2: V('f1'+sg), 4: V('f2'+sg), 6: V('f3'+sg)})
    am, ap = subst_tm(assoc, side('m')), subst_tm(assoc, side('p'))
    L = comp2(G, 1, comp2(G, 0, am, V('v3')), t_up)
    R = comp2(G, 1, s_up, comp2(G, 0, V('v0'), ap))
    print('L : ', infer(G, L) == infer(G, R))
    t0 = time.time()
    K = rc2(G, L, R)
    print('K built and checked in Python', time.time()-t0)
    import pickle; pickle.dump((G, L, R, K), open('/tmp/claude-0/assoc_nat.pkl','wb'))
    def size(t):
        return 1 if t[0]=='v' else 1+sum(size(u) for u in t[3])
    print('size', size(K))

def emit_assoc():
    import pickle
    from emit_agda import emit
    G, L, R, K = pickle.load(open('/tmp/claude-0/assoc_nat.pkl','rb'))
    src = emit('CaTTExp.Generated.AssociatorNaturality', G, K, arr(infer(G, L), L, R),
               'Associator naturality 3-cell over the fully selected 3-chain (depth 2), built by tools/rc2.py following the ladder theorem.')
    open('../src/CaTTExp/Generated/AssociatorNaturality.agda', 'w').write(src)
