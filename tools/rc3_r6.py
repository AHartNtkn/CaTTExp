"""
Generated checks of the constructions in three verified researcher answers:

  cone-over-coherences r4 (answered/cone-over-coherences-r4-2026-11-18.md):
    S_i^j (2) with its target associator, and the 4-cell (14) over D^3 *1 D^3
    in Cone(Q_2; c);
  gray-contexts r6 (answered/gray-contexts-r6-2026-11-18.md):
    Omega_P (3) on two 3-dimensional arities, the point-support 4-term (6)
    over D^3, the interchange 4-coherence (11) over D^2 v1 D^3 v1 D^3 (formal,
    and substituted with a 3-generator of the D^2 *0 D^2 cylinder), and the
    local exchange law (24) over D^3 v0 D^3;
  naturality r6 (answered/naturality-arbitrary-depth-r6-2026-11-18.md):
    the block multiplication M (11) for both orders, zeta (14), the
    horizontal fold psi (18), the first step (20) of the horizontal-vertical
    4-cell over C_6 *0 C_6, and the two routes of (19), checked parallel.
    (36) is checked in TwoDiscCylinderRC3 (tools/rc3_d2d2.py).
Each term is re-checked by catt.infer and by the certified Agda checker in
src/CaTTExp/Generated/RoundSixChecks.agda.
"""
from catt import *
from rc2 import struct_cell, ident, lfold
from rc3_grid import (id2, CN, zvar, full_coh, reassoc_list, lf_groups, insert3,
                      vcomp3, unit_cell, interchange_I, horiz_factors, P22, P33)

def ids(P): return tuple(v(i) for i in range(len(P)))

# ================================================================ cone r4
def cone_ctx():
    G = []
    ix = {}
    def add(n, A): ix[n] = len(G); G.append(A)
    V = lambda n: v(ix[n])
    add('x', STAR); add('y', STAR)
    for i in range(3):
        add('f%d' % i, arr(STAR, V('x'), V('y')))
    for i in (1, 2):
        add('al%d' % i, arr(arr(STAR, V('x'), V('y')), V('f%d' % (i - 1)), V('f%d' % i)))
    add('c', STAR)
    add('px', arr(STAR, V('c'), V('x'))); add('py', arr(STAR, V('c'), V('y')))
    for i in range(3):
        Gt = tuple(G)
        add('u%d' % i, arr(arr(STAR, V('c'), V('y')), V('py'), comp2(Gt, 0, V('px'), V('f%d' % i))))
    for i in (1, 2):
        Gt = tuple(G)
        Ai = comp2(Gt, 0, V('px'), V('al%d' % i))
        tgt = comp2(Gt, 1, V('u%d' % (i - 1)), Ai)
        add('M%d' % i, arr(infer(Gt, V('u%d' % i)), V('u%d' % i), tgt))
    G = tuple(G); check_ctx(G)
    return G, ix

def cone_checks():
    G, ix = cone_ctx()
    V = lambda n: v(ix[n])
    A = {i: comp2(G, 0, V('px'), V('al%d' % i)) for i in (1, 2)}
    # S_1^2 = (M_1 *1 r_12) *2 assoc, r_12 = A_2
    M1 = V('M1')
    s1 = comp2(G, 1, M1, A[2])
    a = struct_or(G, comp2(G, 1, comp2(G, 1, V('u0'), A[1]), A[2]),
                  comp2(G, 1, V('u0'), comp2(G, 1, A[1], A[2])))
    S12 = comp2(G, 2, s1, a)
    # (14) with i = 1, j = 2: R = A_2, R_t = 1_{F_2}, delta : A_2 *1 1 => A_2
    F2 = comp2(G, 0, V('px'), V('f2'))
    RR = comp2(G, 1, A[2], id2(G, F2))
    D2_ = tree_ctx((((),),))                     # x, y, f, g, z
    W1 = tree_ctx(((), ((),)))                   # c -> x (p), x -> y with a 2-disc: c, x, p, y, f, g, al
    Pp = tree_ctx(((), ((),)))
    # delta over D^1(p_x) *0 D^2(alpha_2): (p *0 al) *1 1 => p *0 al
    pa = comp2(Pp, 0, v(2), v(6))
    srcd = comp2(Pp, 1, pa, id2(Pp, infer(Pp, pa)[3]))
    delta = full_coh(Pp, srcd, pa, sub_from(Pp, G, {2: V('px'), 6: V('al2')}))
    P = tree_ctx(glue_tree(3, 1, 3))
    threes = [i for i, T in enumerate(P) if tdim(T) == 2]
    z, w = threes
    al, al_ = P[z][2], P[z][3]
    be, be_ = P[w][2], P[w][3]
    lhs = comp2(P, 2, comp2(P, 1, v(z), be), comp2(P, 1, al_, v(w)))
    rhs = comp2(P, 2, comp2(P, 1, al, v(w)), comp2(P, 1, v(z), be_))
    e14 = full_coh(P, lhs, rhs, sub_from(P, G, {z: M1, w: delta}))
    ty = infer(G, e14)
    want_l = comp2(G, 2, comp2(G, 1, M1, RR), comp2(G, 1, comp2(G, 1, V('u0'), A[1]), delta))
    want_r = comp2(G, 2, comp2(G, 1, V('u1'), delta), comp2(G, 1, M1, A[2]))
    assert ty[2] == want_l and ty[3] == want_r, '(14) type'
    return G, dict(S12=S12, e14=e14)

def struct_or(G, a, b):
    """A coherence a => b between 2-terms whose only 2-variables are whole
    arguments: formed over the pasting context of a vertical chain."""
    # a and b are bracketings of the same vertical list; find the list
    items = []
    def flat(t):
        if t[0] == 'coh' and len(maximal_vars(t[1])) == 2 and tree_of(t[1]) == ((((),), ((),)),) or False:
            pass
        return None
    # specialised: a = (x . y) . z, b = x . (y . z)
    (_, P, A, s) = a
    mx = maximal_vars(P); xy, z_ = s[mx[0]], s[mx[1]]
    (_, P2, A2, s2) = xy
    mx2 = maximal_vars(P2); x_, y_ = s2[mx2[0]], s2[mx2[1]]
    return reassoc_list(G, [x_, y_, z_], ((0, 1), 2), (0, (1, 2)))

# ================================================================ gray-contexts r6
def omega_P(tree):
    """(3): Omega_P = [h_P, (b- *2 K_P) *2 b+]_P for the composition head h_P."""
    P = tree_ctx(tree)
    hP = ucomp(P)
    assert hP[0] == 'coh'
    u, w = infer(P, hP)[2], infer(P, hP)[3]
    # binary evaluation K^0 of the 3-variables (vertical in each 1-column, then *1, then *0)
    K0 = binary_eval(P, tree)
    s2, t2 = infer(P, K0)[2], infer(P, K0)[3]
    assert infer(P, s2) == infer(P, u), 'K0 needs 1-boundary correction (not used here)'
    lo, li = restrict(P, ps_boundary_vars(P, 2, '-'))
    hi, hj = restrict(P, ps_boundary_vars(P, 2, '+'))
    bminus = bdry_coh(P, lo, li, u, s2)
    bplus = bdry_coh(P, hi, hj, t2, w)
    rhs = comp2(P, 2, comp2(P, 2, bminus, K0), bplus)
    return P, full_coh(P, hP, rhs, ids(P))

def bdry_coh(P, B, incl, s, t):
    """coh over the boundary pasting context B (included by incl) between s, t."""
    inv = {}
    for k, tm in enumerate(incl):
        inv[tm[1]] = k
    def rb(x):
        if x[0] == 'v': return v(inv[x[1]])
        return ('coh', x[1], x[2], tuple(rb(y) for y in x[3]))
    return full_coh(B, rb(s), rb(t), incl)

def binary_eval(P, tree):
    """Binary composite of the top cells: for the trees used here, explicit."""
    threes = [i for i, T in enumerate(P) if tdim(T) == 2]
    twos_max = [i for i in maximal_vars(P) if tdim(P[i]) == 1]
    if tree == ((((),), (), ((),)),):            # V(1,0,1): z1 *1 m *1 z2
        z1, z2 = threes
        m = [v(i) for i in twos_max][0]
        return comp2(P, 1, comp2(P, 1, v(z1), m), v(z2))
    if tree == ((((),),), (((),),)):            # D^3 v0 D^3
        z1, z2 = threes
        return comp2(P, 0, v(z1), v(z2))
    raise ValueError

def eq6():
    """(6) over D^3 with the point-supported 3-term beta'(y) = 1_c,
    c : 1_y => 1_y *0 1_y the unitor 2-cell at y."""
    D3 = tree_ctx(((((),),),))                # x, y, f, g, a, b, z
    D0 = tree_ctx(())
    def at_y(P, yv):
        r = ident(P, yv)
        s = comp2(P, 0, r, ident(P, yv))
        c = ('coh', D0, arr(arr(STAR, v(0), v(0)), ident(D0, 0), comp2(D0, 0, ident(D0, 0), ident(D0, 0))), (v(yv),))
        return r, s, c
    r, s, c = at_y(D3, 1)
    beta = id3(D3, c)
    zb = comp2(D3, 0, v(6), beta)
    # kappa_f : f *0 r => f,  kbar_g : g => g *0 s  (over D^1)
    D1_ = tree_ctx(((),))
    r1, s1, _ = at_y(D1_, 1)
    kf_ = full_coh(D1_, comp2(D1_, 0, v(2), r1), v(2), ids(D1_))
    kg_ = full_coh(D1_, v(2), comp2(D1_, 0, v(2), s1), ids(D1_))
    kf = subst_tm(kf_, (v(0), v(1), v(2)))
    kg = subst_tm(kg_, (v(0), v(1), v(3)))
    # l : a *0 c => C(kf, a, kg) over D^2(a); r_b similarly over D^2(b)
    D2_ = tree_ctx((((),),))                  # x, y, f, g, a
    r2, s2, c2 = at_y(D2_, 1)
    kf2 = subst_tm(kf_, (v(0), v(1), v(2))); kg2 = subst_tm(kg_, (v(0), v(1), v(3)))
    ac = comp2(D2_, 0, v(4), c2)
    Cka = comp2(D2_, 1, comp2(D2_, 1, kf2, v(4)), kg2)
    ell_ = full_coh(D2_, ac, Cka, ids(D2_))
    ellbinv_ = full_coh(D2_, Cka, ac, ids(D2_))
    ell = subst_tm(ell_, (v(0), v(1), v(2), v(3), v(4)))
    rbinv = subst_tm(ellbinv_, (v(0), v(1), v(2), v(3), v(5)))
    C3 = comp2(D3, 1, comp2(D3, 1, kf, v(6)), kg)
    rhs = comp2(D3, 2, comp2(D3, 2, ell, C3), rbinv)
    return D3, full_coh(D3, zb, rhs, ids(D3))

def id3(P, c):
    """identity 3-cell on a 2-term c."""
    D2_ = tree_ctx((((),),))
    A = arr(infer(D2_, v(4)), v(4), v(4))
    return ('coh', D2_, A, sub_from(D2_, P, {4: c}))

def eq11_formal():
    P = tree_ctx(((((), ((),), ((),))),))     # D^2(f) v1 D^3(z) v1 D^3(e)
    P = tree_ctx(((), ((),), ((),)),)
    P = tree_ctx((((), ((),), ((),)),))
    threes = [i for i, T in enumerate(P) if tdim(T) == 2]
    z, e = threes
    a, b = P[z][2], P[z][3]
    c, c_ = P[e][2], P[e][3]
    twos = [i for i, T in enumerate(P) if tdim(T) == 1]
    f = [v(i) for i in twos if v(i) not in (a, b, c, c_)][0]
    W = lambda x_, y_: comp2(P, 1, x_, y_)
    lhs = comp2(P, 2, W(W(f, v(z)), c), W(W(f, b), v(e)))
    rhs = comp2(P, 2, W(W(f, a), v(e)), W(W(f, v(z)), c_))
    return P, (z, e, f, c, c_), full_coh(P, lhs, rhs, ids(P))

def eq24():
    P = tree_ctx((((),), ((),)))             # D^2(a) v0 D^2(b)
    f0, f1, a, g0, g1, b = v(2), v(3), v(4), v(6), v(7), v(8)
    L = comp2(P, 1, comp2(P, 0, a, g0), comp2(P, 0, f1, b))
    R = comp2(P, 1, comp2(P, 0, f0, b), comp2(P, 0, a, g1))
    chi = full_coh(P, L, R, ids(P))
    Pu = tree_ctx(((((),),), (((),),)))     # D^3 v0 D^3
    th = [i for i, T in enumerate(Pu) if tdim(T) == 2]
    za, zb = th
    a0, a1 = Pu[za][2], Pu[za][3]
    b0, b1 = Pu[zb][2], Pu[zb][3]
    fz0, fz1 = infer(Pu, a0)[2], infer(Pu, a0)[3]
    gz0, gz1 = infer(Pu, b0)[2], infer(Pu, b0)[3]
    def chi_at(x_, y_):
        return subst_tm(chi, sub_from(P, Pu, {4: x_, 8: y_}))
    AL = comp2(Pu, 1, comp2(Pu, 0, v(za), gz0), comp2(Pu, 0, fz1, v(zb)))
    AR = comp2(Pu, 1, comp2(Pu, 0, fz0, v(zb)), comp2(Pu, 0, v(za), gz1))
    lhs = comp2(Pu, 2, chi_at(a0, b0), AR)
    rhs = comp2(Pu, 2, AL, chi_at(a1, b1))
    return Pu, full_coh(Pu, lhs, rhs, ids(Pu))

def eq11_instance():
    """(11) substituted in the full cylinder of D^2 *0 D^2: z |-> U_A *0 g0+,
    f |-> a path comparison into its 2-source, e |-> a path-contraction 3-cell."""
    from rc3_d2d2 import build
    Wf, IX = build(True)
    X = lambda n: v(IX[n])
    P, (z, e, f, c, c_), law = eq11_formal()
    Z = comp2(Wf, 0, X('UA'), X('g0+'))
    a_ = infer(Wf, Z)[2]
    p_ = infer(Wf, a_)[2]; q_ = infer(Wf, a_)[3]
    alt = lfold(Wf, 0, [X('f0-'), X('Yv'), X('g0+')])
    fz = struct_cell(Wf, alt, p_)
    q1 = lfold(Wf, 0, [X('Xv'), X('f1+'), X('g0+')])
    q2 = comp2(Wf, 0, X('Xv'), comp2(Wf, 0, X('f1+'), X('g0+')))
    cc = comp2(Wf, 1, struct_cell(Wf, q_, q1), struct_cell(Wf, q1, q2))
    cc_ = struct_cell(Wf, q_, q2)
    ee = struct_cell(Wf, cc, cc_)
    sig = sub_from(P, Wf, {z: Z, e: ee, f[1]: fz})
    t = subst_tm(law, sig)
    infer(Wf, t)
    return Wf, t

# ================================================================ naturality r6 (wedge context)
def nat_checks():
    import rc3_wedge as wd
    W = wd.W
    k = lambda a, b: struct_cell(W, a, b)
    c0 = lambda a, b: comp2(W, 0, a, b)
    c1 = lambda a, b: comp2(W, 1, a, b)
    fs = [v(wd.FM), wd.XF]; gs = [v(wd.GM), v(wd.GP)]
    aa = {(0, 0): id2(W, fs[0]), (1, 1): id2(W, fs[1]), (0, 1): v(wd.FF)}
    bb = {(0, 0): id2(W, gs[0]), (1, 1): id2(W, gs[1]), (0, 1): v(wd.GG)}
    E = lambda i, i2, j, j2: c0(aa[i, i2], bb[j, j2])
    def M(d, e):
        Ex, Ey = E(*d), E(*e)
        a, b = horiz_factors(Ex); a_, b_ = horiz_factors(Ey)
        return comp2(W, 2, interchange_I(W, a, b, a_, b_),
                     c0(unit_cell(W, a, a_), unit_cell(W, b, b_)))
    M_FG = M((0, 1, 0, 0), (1, 1, 0, 1))      # F first, then G
    M_GF = M((0, 0, 0, 1), (0, 1, 1, 1))      # G first, then F
    for t in (M_FG, M_GF):
        assert infer(W, t)[3] == c0(v(wd.FF), v(wd.GG))
    # zeta (14) at the displayed cut y: a, a' bracketings of X f+, b = b' = g-
    a1 = wd.XF
    zeta = struct_cell(W, k(c0(a1, gs[0]), c0(a1, gs[0])), c0(k(a1, a1), k(gs[0], gs[0])))
    # local normal forms (6) and psi (18)
    def NF(i, i2, A, A_):
        return [k(A, fs[i]), aa[i, i2], k(fs[i2], A_)]
    def NG(j, j2, B, B_):
        return [k(B, gs[j]), bb[j, j2], k(gs[j2], B_)]
    def psi(Ll, Rl):
        twos = [i for i, T in enumerate(P33) if tdim(T) == 1]
        l, r = twos[:3], twos[3:]
        src = comp2(P33, 0, lfold(P33, 1, [v(i) for i in l]), lfold(P33, 1, [v(i) for i in r]))
        tgt = lfold(P33, 1, [comp2(P33, 0, v(x_), v(y_)) for x_, y_ in zip(l, r)])
        Z3 = full_coh(P33, src, tgt, sub_from(P33, W, dict(zip(l + r, Ll + Rl))))
        L = [c0(x_, y_) for x_, y_ in zip(Ll, Rl)]
        cells = [Z3]
        for pos in (0, 2):
            x_, y_ = Ll[pos], Rl[pos]
            s_ = c0(infer(W, x_)[2], infer(W, y_)[2]); t_ = c0(infer(W, x_)[3], infer(W, y_)[3])
            t, L = insert3(W, L, pos, pos + 1, struct_cell(W, L[pos], k(s_, t_)))
            cells.append(t)
        return vcomp3(W, cells), L
    A0, A1 = fs[0], fs[1]; B0, B1 = gs[0], gs[1]
    L1, L2 = NF(0, 1, A0, A1), NF(1, 1, A1, A1)
    R1, R2 = NG(0, 0, B0, B0), NG(0, 1, B0, B1)
    psi1, N1 = psi(L1, R1)
    psi2, N2 = psi(L2, R2)
    # mu for padded normal forms: reassociate, contract the middle pair, kappa => 1, unit, M
    def mu6(Na, Nb, d, e):
        L = Na + Nb
        cells = [reassoc_list(W, L, ((0, 1, 2), (3, 4, 5)), lf_groups(6))]
        X_ = infer(W, L[2])[2]; Z_ = infer(W, L[3])[3]
        t, L = insert3(W, L, 2, 4, struct_cell(W, c1(L[2], L[3]), k(X_, Z_)))
        cells.append(t)
        q_ = infer(W, L[2])[2]
        t, L = insert3(W, L, 2, 3, struct_cell(W, L[2], id2(W, q_)))
        cells.append(t)
        P = CN(2)
        s = comp2(P, 1, comp2(P, 1, zvar(1), id2(P, v(3))), zvar(2))
        tt = comp2(P, 1, zvar(1), zvar(2))
        u = full_coh(P, s, tt, sub_from(P, W, {4: L[1], 6: L[3]}))
        t, L = insert3(W, L, 1, 4, comp2(W, 2, u, M(d, e)))
        cells.append(t)
        return vcomp3(W, cells), L
    route1_a = comp2(W, 1, psi1, psi2)
    mu_, Lm = mu6(N1, N2, (0, 1, 0, 0), (1, 1, 0, 1))
    route1 = comp2(W, 2, route1_a, mu_)
    # route 2: I ; (mu^F *0 mu^G) ; psi
    I = interchange_I(W, lfold(W, 1, L1), lfold(W, 1, R1), lfold(W, 1, L2), lfold(W, 1, R2))
    def mu_loc(La, Lb, side):
        L = La + Lb
        cells = [reassoc_list(W, L, ((0, 1, 2), (3, 4, 5)), lf_groups(6))]
        X_ = infer(W, L[2])[2]; Z_ = infer(W, L[3])[3]
        t, L = insert3(W, L, 2, 4, struct_cell(W, c1(L[2], L[3]), k(X_, Z_)))
        cells.append(t)
        q_ = infer(W, L[2])[2]
        t, L = insert3(W, L, 2, 3, struct_cell(W, L[2], id2(W, q_)))
        cells.append(t)
        P = CN(2)
        s = comp2(P, 1, comp2(P, 1, zvar(1), id2(P, v(3))), zvar(2))
        tt = comp2(P, 1, zvar(1), zvar(2))
        u = full_coh(P, s, tt, sub_from(P, W, {4: L[1], 6: L[3]}))
        t, L = insert3(W, L, 1, 4, comp2(W, 2, u, unit_cell(W, L[1], L[3])))
        cells.append(t)
        return vcomp3(W, cells), L
    muF, LF_ = mu_loc(L1, L2, 'F')
    muG, LG_ = mu_loc(R1, R2, 'G')
    psi12, N12 = psi(LF_, LG_)
    route2 = vcomp3(W, [I, comp2(W, 0, muF, muG), psi12])
    t1, t2 = infer(W, route1), infer(W, route2)
    assert t1 == t2, '(19): the two routes are not parallel'
    # (20) over C_6 *0 C_6
    P66 = tree_ctx((tuple(() for _ in range(6)), tuple(() for _ in range(6))))
    P66 = tree_ctx((((), (), (), (), (), ()), ((), (), (), (), (), ())))
    twos = [i for i, T in enumerate(P66) if tdim(T) == 1]
    l, r = [v(i) for i in twos[:6]], [v(i) for i in twos[6:]]
    def lf(xs): return lfold(P66, 1, xs)
    top = comp2(P66, 0, lf(l[:3]), lf(r[:3])); bot = comp2(P66, 0, lf(l[3:]), lf(r[3:]))
    src = comp2(P66, 1, top, bot)
    zips = lambda ls, rs: lf([comp2(P66, 0, a_, b_) for a_, b_ in zip(ls, rs)])
    def z3(ls, rs):
        s_ = comp2(P66, 0, lf(ls), lf(rs))
        return sub_coh(P33, P66, ls + rs, s_, zips(ls, rs))
    stepA1 = comp2(P66, 1, z3(l[:3], r[:3]), z3(l[3:], r[3:]))
    six = [comp2(P66, 0, a_, b_) for a_, b_ in zip(l, r)]
    stepA2 = sub_coh(CN(6), P66, six, comp2(P66, 1, lf(six[:3]), lf(six[3:])), lf(six))
    routeA = comp2(P66, 2, stepA1, stepA2)
    I66 = sub_coh(P22, P66, [lf(l[:3]), lf(l[3:]), lf(r[:3]), lf(r[3:])], src,
                  comp2(P66, 0, comp2(P66, 1, lf(l[:3]), lf(l[3:])), comp2(P66, 1, lf(r[:3]), lf(r[3:]))),
                  order=(4, 6, 10, 12))
    rl = sub_coh(CN(6), P66, l, comp2(P66, 1, lf(l[:3]), lf(l[3:])), lf(l))
    rr = sub_coh(CN(6), P66, r, comp2(P66, 1, lf(r[:3]), lf(r[3:])), lf(r))
    z6 = sub_coh(P66, P66, l + r, comp2(P66, 0, lf(l), lf(r)), zips(l, r))
    routeB = vcomp3(P66, [I66, comp2(P66, 0, rl, rr), z6])
    e20 = full_coh(P66, routeA, routeB, ids(P66))
    return W, dict(M_FG=M_FG, M_GF=M_GF, zeta=zeta, psi1=psi1, psi2=psi2, psi12=psi12,
                   route1=route1, route2=route2), (P66, e20), t1

def sub_coh(P, Q, entries, s_Q, t_Q, order=None):
    """A coherence over P (whose maximal 2-variables are listed in order, or at
    the positions `order`) sent into Q by entries, between the Q-terms s_Q,
    t_Q, which must be the images of full parallel P-terms.  We find those
    P-terms by building them over P with the same recipe: here we use the
    fact that s_Q, t_Q are built from the entries by comp2 only."""
    twos = list(order) if order else [i for i, T in enumerate(P) if tdim(T) == 1 and i in maximal_vars(P)]
    sig = sub_from(P, Q, dict(zip(twos, entries)))
    back = {}
    for i, e in enumerate(sig):
        back.setdefault(e, v(i))
    for i, e in zip(twos, entries):
        back[e] = v(i)
    def pull(t):
        if t in back: return back[t]
        if t[0] == 'v':
            for i, s in enumerate(sig):
                if s == t: return v(i)
            raise ValueError('cannot pull back')
        _, R, A, s = t
        sp = tuple(pull(u) for u in s)
        return ('coh', R, A, sp)
    sP, tP = pull(s_Q), pull(t_Q)
    res = full_coh(P, sP, tP, sig)
    assert infer(Q, res) == arr(infer(Q, s_Q), s_Q, t_Q)
    return res

# ================================================================ run
def main():
    out = {}
    Gc, cone = cone_checks()
    out['cone'] = (Gc, cone)
    om = [omega_P(((((),), (), ((),)),)), omega_P(((((),),), (((),),)))]
    D3, e6 = eq6()
    P11, _, e11 = eq11_formal()
    Wf, e11i = eq11_instance()
    Pu, e24 = eq24()
    W, nat, (P66, e20), t19 = nat_checks()
    print('cone r4: S_1^2, (14); gray r6: Omega_P x2, (6), (11) formal + instance, (24); '
          'naturality r6: M both orders, zeta, psi x3, (19) routes parallel, (20) ok')
    return dict(Gc=Gc, cone=cone, om=om, e6=(D3, e6), e11=(P11, e11), e11i=(Wf, e11i),
                e24=(Pu, e24), W=W, nat=nat, e20=(P66, e20), t19=t19)

def emit_module():
    from emit_agda import Emitter
    r = main()
    E = Emitter()
    for k_, t in r['cone'].items():
        E.check_typed('cone-' + k_, r['Gc'], t)
    for i, (P, t) in enumerate(r['om']):
        E.check_typed('Omega%d' % i, P, t)
    E.check_typed('eq6', *r['e6'])
    E.check_typed('eq11', *r['e11'])
    E.check_typed('eq11-inst', *r['e11i'])
    E.check_typed('eq24', *r['e24'])
    for k_, t in r['nat'].items():
        E.check_typed('nat-' + k_, r['W'], t)
    E.check_type('nat-route1-ty', r['W'], r['nat']['route1'], r['t19'])
    E.check_type('nat-route2-ty', r['W'], r['nat']['route2'], r['t19'])
    E.check_typed('eq20', *r['e20'])
    src = E.module('CaTTExp.Generated.RoundSixChecks',
                   'Checks of constructions from three verified researcher answers: cone r4 (2), (14); gray-contexts r6 (3), (6), (11), (24); naturality r6 (11), (14), (18), (20) and the two routes of (19). Built by tools/rc3_r6.py.')
    open('../src/CaTTExp/Generated/RoundSixChecks.agda', 'w').write(src)
    print('emitted', len(E.defs), 'definitions,', len(E.checks), 'checks')

def emit_negative():
    from emit_agda import Emitter
    Pu, t = eq24(); A = infer(Pu, t)
    E = Emitter(); E.check_type('bad', Pu, t, arr(A[1], A[3], A[2]))
    open('../src/CaTTExp/Generated/NegRoundSix.agda', 'w').write(
        E.module('CaTTExp.Generated.NegRoundSix', 'Negative control: must be rejected.'))

if __name__ == '__main__':
    import sys
    if sys.argv[1:] == ['emit']:
        emit_module()
    elif sys.argv[1:] == ['neg']:
        emit_negative()
    else:
        main()
