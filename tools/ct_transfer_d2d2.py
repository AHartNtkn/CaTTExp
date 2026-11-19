"""
CT(D² ⊗ D²) by transfer from the three-interval cube (route (iv) of
notes/conjectures/outbox/canonical-gray-terms-r4.md, P = Q = I).

The strict functor Φ : I ⊗ I ⊗ I → (D² ⊗ D²)((0,0),(1,1)) of
answered/canonical-gray-terms-r3-2026-11-19.md sends p⊗e⊗q to Sp⊗Sq and an
endpoint cell p⊗v⊗q to  ε(q) Sp⊗(1−v) + ε(p) v⊗Sq  (degree +1).  We realise it
syntactically as a substitution

    σ : Γ' → Σ_{(0,0),(1,1)} Fam(I ⊗ I ⊗ I)

where Fam(I ⊗ I ⊗ I) is the 27-variable cube context of canonical_gray_cube.py
and Γ' is a context for D² ⊗ D²:

  * the 16 endpoint generators of D² ⊗ D² (4 vertices, α_i⊗w, w⊗β_j, A⊗w, w⊗B),
    with variable boundaries;
  * σ on the cube's endpoint vertices = binary composites of two edges,
    on endpoint edges = whiskerings R₂ / L₂ of A⊗w, w⊗B by an edge,
    on the two **endpoint panels** e⊗v⊗e (strict image an identity) = the
    exchange coherence over D² ∨₀ D² between the two transferred edge orders;
  * one new variable for each of the 9 mixed generators Sp⊗Sq, declared with
    the σ-substituted suspended type of the cube variable p⊗e⊗q.

Then T'(c) = (Σ T(c̄))[σ] for every cell c̄ of the cube.  The script checks:
σ is literally well typed (every endpoint image, and the two panel
coherences, have exactly the σ-substituted suspended type of the variable
they replace); Γ' is well formed; all 49 non-identity cube cells transfer.

  python3 ct_transfer_d2d2.py         # Python kernel check
  python3 ct_transfer_d2d2.py emit    # write src/CaTTExp/Generated/GrayDiscDiscTransfer.agda
  python3 ct_transfer_d2d2.py neg     # negative control (must be rejected)
"""
import sys
from itertools import combinations
from catt import *
from emit_agda import Emitter
from canonical_gray_cube import build_cube
from ct_suspension import susp_tm, susp_ty, R, L

# ---------------------------------------------------------------- the cube, with its variable layout
cube, cube_checks = build_cube()
edge_ix, sq_ix = {}, {}
i = 8
for vertex in range(8):
    for axis in range(3):
        if not vertex & (1 << axis):
            edge_ix[vertex, axis] = i; i += 1
for vertex in range(8):
    for low, high in combinations(range(3), 2):
        if not vertex & ((1 << low) | (1 << high)):
            sq_ix[vertex, low, high] = i; i += 1
TOP = i
assert TOP == 26 and len(cube) == 27
for (vtx, axis), j in edge_ix.items():
    assert cube[j] == arr(STAR, v(vtx), v(vtx | (1 << axis)))

def coords(vtx):           # (p, middle, q): axis 0 = P, axis 1 = I, axis 2 = Q
    return vtx & 1, (vtx >> 1) & 1, (vtx >> 2) & 1

# ---------------------------------------------------------------- Γ', endpoint part
G = []
def decl(A):
    G.append(A); return v(len(G) - 1)
X = {}
for p in (0, 1):
    for q in (0, 1):
        X[p, q] = None
X[0, 0] = decl(STAR); X[1, 0] = decl(STAR); X[0, 1] = decl(STAR); X[1, 1] = decl(STAR)
al = {(i_, w): decl(arr(STAR, X[0, w], X[1, w])) for w in (0, 1) for i_ in (0, 1)}   # α_i ⊗ w
be = {(w, j): decl(arr(STAR, X[w, 0], X[w, 1])) for w in (0, 1) for j in (0, 1)}    # w ⊗ β_j
A_ = {w: decl(arr(arr(STAR, X[0, w], X[1, w]), al[0, w], al[1, w])) for w in (0, 1)}  # A ⊗ w
B_ = {w: decl(arr(arr(STAR, X[w, 0], X[w, 1]), be[w, 0], be[w, 1])) for w in (0, 1)}  # w ⊗ B
assert len(G) == 16

# ---------------------------------------------------------------- σ, incrementally
sig = {0: X[0, 0], 1: X[1, 1]}         # suspension endpoints
mixed = {}                              # cube var -> Γ' var

def want(j):
    """σ-substituted suspended type of cube variable j."""
    return subst_ty(susp_ty(cube[j]), tuple(sig[x] for x in range(j + 2)))

def exchange(Gt, S, T, panel_vars):
    """Coherence S → T over D² ∨₀ D², where panel_vars lists the Γ' variables
    playing x, y, f, f', a, z, g, g', b of the pasting context."""
    Q = tree_ctx(glue_tree(2, 0, 2))
    ren = {gv[1]: qi for qi, gv in zip([0, 1, 2, 3, 4, 5, 6, 7, 8], panel_vars)}
    def rn(t):
        if t[0] == 'v': return v(ren[t[1]])
        return ('coh', t[1], t[2], tuple(rn(u) for u in t[3]))
    SQ, TQ = rn(S), rn(T)
    assert infer(Q, SQ) == infer(Q, TQ)
    k = ('coh', Q, arr(infer(Q, SQ), SQ, TQ), tuple(panel_vars))
    return k

panels = []
for j in range(27):
    Gt = tuple(G)
    if j < 8:                                    # vertex p⊗v⊗q
        p, m, q = coords(j)
        sig[j + 2] = R(Gt, 1, be[0, q], al[p, 1]) if m == 0 else R(Gt, 1, al[p, 0], be[1, q])
    elif j < 20:                                 # edge
        (vtx, axis), = [k for k, ix in edge_ix.items() if ix == j]
        p, m, q = coords(vtx)
        if axis == 0:                            # e⊗v⊗q
            sig[j + 2] = L(Gt, 2, be[0, q], A_[1]) if m == 0 else R(Gt, 2, A_[0], be[1, q])
        elif axis == 2:                          # p⊗v⊗e
            sig[j + 2] = R(Gt, 2, B_[0], al[p, 1]) if m == 0 else L(Gt, 2, al[p, 0], B_[1])
        else:                                    # mixed p⊗e⊗q ↦ α_p ⊗ β_q
            sig[j + 2] = decl(want(j)); mixed[j] = sig[j + 2]
    elif j < 26:                                 # square
        (vtx, low, high), = [k for k, ix in sq_ix.items() if ix == j]
        if (low, high) == (0, 2):                # endpoint panel e⊗v⊗e: exchange coherence
            m = coords(vtx)[1]
            W = want(j)
            pv = ([X[0, 0], X[0, 1], be[0, 0], be[0, 1], B_[0], X[1, 1], al[0, 1], al[1, 1], A_[1]] if m == 0 else
                  [X[0, 0], X[1, 0], al[0, 0], al[1, 0], A_[0], X[1, 1], be[1, 0], be[1, 1], B_[1]])
            sig[j + 2] = exchange(Gt, W[2], W[3], pv)
            panels.append((j, sig[j + 2], W))
        else:
            sig[j + 2] = decl(want(j)); mixed[j] = sig[j + 2]
    else:                                        # top cell e⊗e⊗e ↦ A ⊗ B
        sig[j + 2] = decl(want(j)); mixed[j] = sig[j + 2]
    # σ is literally well typed at j
    assert infer(tuple(G), sig[j + 2]) == want(j), ('σ ill-typed at cube var', j)

G = tuple(G)
sigma = tuple(sig[x] for x in range(29))
assert len(G) == 25 and len(mixed) == 9
check_ctx(G)

transferred = []
for label, t, E in cube_checks:
    t2, E2 = subst_tm(susp_tm(t), sigma), subst_ty(susp_ty(E), sigma)
    assert infer(G, t2) == E2, label
    transferred.append((label, t2, E2))
# the mixed generators are their variables (CT (a))
for j, var in mixed.items():
    assert subst_tm(susp_tm(v(j)), sigma) == var

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'check'
    print('Γ\': %d variables (16 endpoint, 9 mixed); σ well typed incl. %d panel exchanges; %d cube cells transferred'
          % (len(G), len(panels), len(transferred)))
    if mode == 'emit':
        em = Emitter()
        for j, k, W in panels:
            em.check_type('panel%d' % j, G, k, W)
        for j in range(8, 20):
            pass
        for label, t2, E2 in transferred:
            em.check_type('T-' + label, G, t2, E2)
        open('../src/CaTTExp/Generated/GrayDiscDiscTransfer.agda', 'w').write(
            em.module('CaTTExp.Generated.GrayDiscDiscTransfer',
                      'CT(D² ⊗ D²) by transfer from the Gray cube (tools/ct_transfer_d2d2.py).'))
        print('emitted')
    if mode == 'neg':
        j, k, W = panels[0]
        em = Emitter()
        em.check_type('neg', G, k, arr(W[1], W[3], W[2]))
        open('../src/CaTTExp/Generated/NegGrayDiscDiscTransfer.agda', 'w').write(
            em.module('CaTTExp.Generated.NegGrayDiscDiscTransfer', 'Negative control: must be rejected.'))
        print('negative control written')
