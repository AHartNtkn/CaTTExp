------------------------------------------------------------------------
-- The whiskered-generator cell (ledger S20 (i), stage 3c; notes/
-- relative-coherence.md §2 Step 3, H_g).
--
-- Over the chain tree with N = m + 1 + n leaves, raising leaf m gives
-- the column context; the congruence cell of the N-ary composite
-- (PsRaiseCongr.cong-cell-op, k = 1) is the column coherence H_g. This
-- module discharges its hypotheses for every m, n.
------------------------------------------------------------------------
module CaTTExp.RCProc.Whisker where

open import CaTTExp.Prelude
open import CaTTExp.Derived using (subst₂)
open import CaTTExp.Pure
open import CaTTExp.PsRaise using (TopOK; anyR; Le)
open import CaTTExp.RCProc.Column
open import CaTTExp.RCProc.Path1 using (B-ty; B-op; dim-chain)
open import CaTTExp.GraphFillerTotal.Chains using (chainC; vtx)

private
  topNone : ∀ n → TopOK 1 0 (leaves n) []
  topNone zero    = tt
  topNone (suc n) = topNone n

topOK-chain : ∀ m n → TopOK 1 0 (leaves (suc (m + n))) (flagAt m)
topOK-chain zero    n = refl , topNone n
topOK-chain (suc m) n = topOK-chain m n

any-chain : ∀ m n → T (anyR (flagAt m) (leaves (suc (m + n))))
any-chain zero    n = tt
any-chain (suc m) n = any-chain m n

private
  P≡ : ∀ N → ctxOf (chainT N) ≡ chainC N
  P≡ N = trans (chain-ctx N) (C₀-chainC N)

le-chain : ∀ N → Le (dimCtx (ctxOf (chainT (suc N)))) 1
le-chain N rewrite P≡ (suc N) | dim-chain N = tt

ty-chain : ∀ N → ctxOf (chainT N) ⊢ty arr ⋆ (var 0) (var (vtx N))
ty-chain N = subst (_⊢ty arr ⋆ (var 0) (var (vtx N))) (sym (P≡ N)) (B-ty N)

op-chain : ∀ N → T (isOp (ctxOf (chainT N)) ⋆ (var 0) (var (vtx N)))
op-chain N = subst (λ Γ → T (isOp Γ ⋆ (var 0) (var (vtx N)))) (sym (P≡ N)) (B-op N)

------------------------------------------------------------------------
-- H_g: the congruence cell of the N-ary composite, N = m + 1 + n,
-- in its middle slot.

open import CaTTExp.PsRaiseCongr using (A^; c⁻; c⁺; cong-cell-op)
open import CaTTExp.GrayCtx.Lift using (raiseT)

module Col (m n : Nat) where
  N : Nat
  N = suc (m + n)

  R : Ctx
  R = ctxOf (raiseT (flagAt m) (chainT N))

  R≡ : R ≡ colCtx m n
  R≡ = raised-ctx m n

  HTy : Ty
  HTy = arr (A^ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx N)))
            (c⁻ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx N)))
            (c⁺ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx N)))

  H : Sub → Tm
  H θ = coh R HTy θ

  H-wf : ∀ {Γ θ} → Γ ⊢sub θ ∶ colCtx m n → Γ ⊢tm H θ ∶ HTy [ θ ]ty
  H-wf {Γ} {θ} sθ =
    cong-cell-op (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx N)) 1
      (le-chain (m + n)) (topOK-chain m n) (any-chain m n) (ty-chain N) (op-chain N)
      (subst (Γ ⊢sub θ ∶_) (sym R≡) sθ)

  -- The type of H_g[θ_g] is a → b.
  open import CaTTExp.PsRaise using (inclM; inclM-0; inclM-pt)

  A^-eq : A^ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx N)) ≡ arr ⋆ (var 0) (var (colEnd m n))
  A^-eq = cong₂ (arr ⋆) (inclM-0 (flagAt m) (node []) (leaves (m + n)))
            (subst₂ (λ i j → lookupₛ (inclM (flagAt m) (node []) (leaves (m + n))) i ≡ var j)
               (chain-pt N) (raised-pt m n) (inclM-pt (flagAt m) (node []) (leaves (m + n))))
