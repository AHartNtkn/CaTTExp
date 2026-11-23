"""
Self-test of the relative-coherence tooling (notes/rc-generator.md).

  python3 tools/rc_selftest.py          # Python-side checks only
  python3 tools/rc_selftest.py emit     # also writes Generated/RCSelfTest{,Check}.agda
  python3 tools/rc_selftest.py neg      # writes Generated/RCSelfTestNeg{,Check}.agda,
                                        # a negative control whose Check Agda must reject

Checks: answers of rc in each implemented case (identity, globular support
in dimensions 2 and 3, RC(1), Theorem A with an exchange, peeling, the
rank-3 reductions of rc_heur), refusal
of a pair with different strict images, the strict word of every cell of a
small context evaluating back to it, word lifting at prescribed poles, and
the marked-globe reduction with padding removal (r9 Response 2).
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rc_oracle import *
import steiner as St
import rc_lift as L

def bigons():
    """x, y, z; f, f' : x -> y, a : f => f'; g, g' : y -> z, b : g => g'."""
    G = [STAR, STAR, arr(STAR, v(0), v(1)), arr(STAR, v(0), v(1))]
    G.append(arr(arr(STAR, v(0), v(1)), v(2), v(3)))
    G += [STAR, arr(STAR, v(1), v(5)), arr(STAR, v(1), v(5))]
    G.append(arr(arr(STAR, v(1), v(5)), v(6), v(7)))
    return tuple(G)

def triangle():
    """A 2-cell with a composite target: x -> y -> z, h : x -> z, a : h => f * g,
    plus an extra 2-cell b : g => g' (not a pasting context)."""
    G = [STAR, STAR, arr(STAR, v(0), v(1)), STAR, arr(STAR, v(1), v(3)), arr(STAR, v(0), v(3))]
    fg = comp2(tuple(G), 0, v(2), v(4))
    G.append(arr(arr(STAR, v(0), v(3)), v(5), fg))                 # a : 6
    G.append(arr(STAR, v(1), v(3)))                                # g' : 7
    G.append(arr(arr(STAR, v(1), v(3)), v(4), v(7)))               # b : 8
    G += [STAR, arr(STAR, v(3), v(9)), arr(STAR, v(3), v(9))]     # w : 9, k : 10, k' : 11
    G.append(arr(arr(STAR, v(3), v(9)), v(10), v(11)))             # c : 12
    return tuple(G)

def whisker3():
    """x, y; f, g : x -> y; a, b, c : f => g; A : a => b, B : b => c; z, h : y -> z,
    k : x -> z and a 2-cell tau : k => f * h with a composite target."""
    S = arr(STAR, v(0), v(1)); T2 = arr(S, v(2), v(3))
    G = (STAR, STAR, S, S, T2, T2, T2, arr(T2, v(4), v(5)), arr(T2, v(5), v(6)),
         STAR, arr(STAR, v(1), v(9)), arr(STAR, v(0), v(9)))
    return G + (arr(arr(STAR, v(0), v(9)), v(11), comp2(G, 0, v(2), v(10))),)

def cases():
    out = []
    G = bigons()
    T = comp2(G, 1, comp2(G, 0, v(4), v(6)), comp2(G, 0, v(3), v(8)))
    U = comp2(G, 1, comp2(G, 0, v(2), v(8)), comp2(G, 0, v(4), v(7)))
    out.append(('exchange-globular', G, infer(G, T), T, U))
    a = comp2(G, 0, comp2(G, 0, v(2), v(6)), identity(G, v(5)))
    b = comp2(G, 0, v(2), comp2(G, 0, identity(G, v(1)), v(6)))
    out.append(('rc1', G, infer(G, a), a, b))
    out.append(('identity', G, infer(G, T), T, T))
    P = tree_ctx(((((), ()),),))
    Th, Ps = maximal_vars(P)
    t3 = comp2(P, 2, v(Th), comp2(P, 2, v(Ps), identity(P, tgt(P, v(Ps)))))
    u3 = comp2(P, 2, v(Th), v(Ps))
    out.append(('globular-dim3', P, infer(P, t3), t3, u3))
    H = triangle()
    # exchange of a with b, not on a pasting context: Theorem A
    t = comp2(H, 1, v(6), comp2(H, 0, v(2), v(8)))
    u = comp2(H, 1, comp2(H, 1, v(6), comp2(H, 0, v(2), v(8))), identity(H, comp2(H, 0, v(2), v(7))))
    out.append(('peel-unitor', H, infer(H, t), t, u))
    fg = comp2(H, 0, v(2), v(4))
    t = comp2(H, 1, comp2(H, 0, v(6), v(10)), comp2(H, 0, fg, v(12)))
    u = comp2(H, 1, comp2(H, 0, v(5), v(12)), comp2(H, 0, v(6), v(11)))
    out.append(('theorem-a-exchange', H, infer(H, t), t, u))
    # rank 3 on a nonglobular support (rc_heur): distribution over a composite
    W3 = whisker3()
    wh = lambda X: comp2(W3, 1, v(12), comp2(W3, 0, X, v(10)))
    t = comp2(W3, 2, wh(v(7)), wh(v(8)))
    u = wh(comp2(W3, 2, v(7), v(8)))
    out.append(('rank3-distribute', W3, infer(W3, t), t, u))
    # and an identity in a top slot
    t = comp2(W3, 1, v(12), identity(W3, comp2(W3, 0, v(4), v(10))))
    u = comp2(W3, 1, v(12), comp2(W3, 0, identity(W3, v(4)), v(10)))
    out.append(('rank3-identity-slot', W3, infer(W3, t), t, u))
    # a whiskered coherence followed by its inverse, against the identity
    a1 = comp2(W3, 1, v(4), identity(W3, v(3)))
    D2 = tree_ctx(disc_tree(2))
    k1 = ('coh', D2, arr(D2[4], v(4), comp2(D2, 1, v(4), identity(D2, v(3)))), (v(0), v(1), v(2), v(3), v(4)))
    k2 = ('coh', D2, arr(D2[4], comp2(D2, 1, v(4), identity(D2, v(3))), v(4)), (v(0), v(1), v(2), v(3), v(4)))
    t = comp2(W3, 2, wh(k1), wh(k2))
    u = identity(W3, wh(v(4)))
    out.append(('rank3-cancel-loop', W3, infer(W3, t), t, u))
    return out

def run_python_checks():
    ok = True
    answered = []
    for name, G, A, t, u in cases():
        w = rc(G, A, t, u)
        good = w is not None and infer(G, w) == arr(A, t, u)
        print('%-20s %s' % (name, 'answered' if good else 'FAILED'))
        ok &= good
        if good:
            answered.append((G, A, t, u, w))
    G = bigons()
    bad = rc(G, infer(G, v(2)), v(2), v(3))
    print('%-20s %s' % ('refuse-different', 'refused' if bad is None else 'FAILED'))
    ok &= bad is None
    K = St.Complex(G)
    cells = St.cells_upto(K, set(range(len(G))), 2)
    words_ok = all(St.eval_word(K, St.strict_word(K, c)) == c for c in cells)
    print('%-20s %s (%d cells)' % ('strict-words', 'ok' if words_ok else 'FAILED', len(cells)))
    ok &= words_ok
    T = comp2(G, 1, comp2(G, 0, v(4), v(6)), comp2(G, 0, v(3), v(8)))
    c = St.image_to_cell(strict_image(G, T))
    s = comp2(G, 0, v(2), comp2(G, 0, v(6), identity(G, v(5))))
    t = comp2(G, 0, comp2(G, 0, identity(G, v(0)), v(3)), v(7))
    X = L.lift_at(G, c, s, t, rc)
    lift_ok = infer(G, X)[2:] == (s, t) and St.image_to_cell(strict_image(G, X)) == c
    print('%-20s %s' % ('word-lift', 'ok' if lift_ok else 'FAILED'))
    ok &= lift_ok
    u2 = comp2(G, 1, identity(G, v(2)), identity(G, v(2)))
    w2 = identity(G, v(2))
    Kg = L.via_globe(G, u2, w2, rc)
    globe_ok = Kg is not None and infer(G, Kg) == arr(infer(G, u2), u2, w2)
    print('%-20s %s' % ('marked-globe', 'ok' if globe_ok else 'FAILED'))
    ok &= globe_ok
    if globe_ok:
        answered.append((G, infer(G, u2), u2, w2, Kg))
    # Event interchange (rc_heur.interchange, via rc_nat.square): the
    # [E_tau, E_b] against [E_c, (sigma c_1)^] sub-query of Horiz3 round 21.
    # Python-only (not emitted to the Agda table): asserts that the step fires.
    import gzip, ast, rc_heur
    fx = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fixtures', 'rc_interchange_round21.txt.gz')
    with gzip.open(fx, 'rt') as f:
        Gi, Ai, ti, ui = ast.literal_eval(f.read())
    fired = [0]
    orig = rc_heur.interchange
    def spy(*a):
        r = orig(*a)
        fired[0] += r is not None
        return r
    rc_heur.interchange = spy
    try:
        wi = rc(Gi, Ai, ti, ui)
    finally:
        rc_heur.interchange = orig
    inter_ok = wi is not None and infer(Gi, wi) == arr(Ai, ti, ui) and fired[0] > 0
    print('%-20s %s' % ('interchange', 'ok' if inter_ok else 'FAILED'))
    ok &= inter_ok
    H = triangle()
    print('%-20s %s' % ('strong-steiner', 'ok' if St.Complex(H).is_strong_steiner() else 'FAILED'))
    return ok, answered

if __name__ == '__main__':
    ok, answered = run_python_checks()
    mode = sys.argv[1] if len(sys.argv) > 1 else None
    if mode == 'emit':
        with open(os.path.join(GEN, 'RCSelfTest.agda'), 'w') as f:
            f.write(emit_table('RCSelfTest', answered, 'Self-test answers (tools/rc_selftest.py).'))
        with open(os.path.join(GEN, 'RCSelfTestCheck.agda'), 'w') as f:
            f.write(emit_check('RCSelfTest'))
        print('wrote RCSelfTest and RCSelfTestCheck')
    elif mode == 'neg':
        # swap source and target of the first entry: the checker must reject it
        G, A, t, u, w = answered[0]
        bad = [(G, A, u, t, w)] + answered[1:]
        with open(os.path.join(GEN, 'RCSelfTestNeg.agda'), 'w') as f:
            f.write(emit_table('RCSelfTestNeg', bad, 'Negative control: first entry has its ends swapped.'))
        with open(os.path.join(GEN, 'RCSelfTestNegCheck.agda'), 'w') as f:
            f.write(emit_check('RCSelfTestNeg'))
        print('wrote RCSelfTestNeg and RCSelfTestNegCheck (Agda must reject the Check)')
    sys.exit(0 if ok else 1)
