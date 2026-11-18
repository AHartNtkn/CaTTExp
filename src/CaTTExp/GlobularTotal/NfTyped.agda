------------------------------------------------------------------------
-- F2c, lemma (1′): normal forms of well-typed terms of a globular
-- context. This module fixes the statement and proves the variable
-- case; the coherence case (which needs (1c) inside the pasting
-- context of the coh, from the same induction) is the next step.
--
-- A context is globular when the endpoints of every type in it are
-- variables of it (PsOrd.TyIn). For Γ ⊢ t : A, `Res Γ t A` says:
-- for some fuel, nf t is a tree a that is
--   * well formed, of dimension dim A,
--   * a diagram of Γ (Uniq.Ex),
--   * with dim B boundaries the normal forms of A's endpoints, when
--     A = s →_B u,
--   * labelled exactly by the variables of t and A.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.NfTyped where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; nf; wrap; bd)
open import CaTTExp.GlobularTotal.TreeAlg using (WF)
open import CaTTExp.GlobularTotal.Uniq using (mem; memL; Ex)
open import CaTTExp.GlobularTotal.PsOrd using (TyIn)
open import CaTTExp.GlobularTotal.Wrap

Glob : Ctx → Set
Glob Γ = ∀ y A → lookup Γ y ≡ just A → TyIn Γ A

-- a has dimension at most d.
Dim : Nat → LT → Set
Dim d a = ∀ β i → bd β (d + i) a ≡ a

Ends : Ctx → Ty → LT → Set
Ends Γ ⋆           a = ⊤
Ends Γ (arr B s u) a =
  Σ Nat λ n → (nf n Γ s ≡ just (bd false (dim B) a)) × (nf n Γ u ≡ just (bd true (dim B) a))

Res : Ctx → Tm → Ty → Set
Res Γ t A = Σ Nat λ n → Σ LT λ a →
    (nf n Γ t ≡ just a) × WF a × Dim (dim A) a × Ex Γ 0 nothing a × Ends Γ A a
  × (∀ y → mem y a ≡ memL y (fvTmTy t A))

------------------------------------------------------------------------
-- Variables.

private
  ∨-swap : ∀ F p → (F ∨ ((p ∨ false) ∨ false)) ≡ (p ∨ F)
  ∨-swap true  true  = refl
  ∨-swap true  false = refl
  ∨-swap false true  = refl
  ∨-swap false false = refl

res-var : ∀ Γ i A → Glob Γ → lookup Γ i ≡ just A → Res Γ (var i) A
res-var Γ i A g e = 1 , w , nf-eq , wf , dm , ex , ends A (g i A e) , labs
  where
  tA = g i A e
  pt = lt (i ∷ []) []
  w  = wrapT A pt

  nf-eq : nf 1 Γ (var i) ≡ just w
  nf-eq rewrite e = wrap-T Γ A pt tA

  wf : WF w
  wf = wrapT-wf Γ A pt tA (refl , tt)

  dm : Dim (dim A) w
  dm β k = wrapT-dim Γ A i β k tA

  ex : Ex Γ 0 nothing w
  ex = wrapT-ex Γ A pt tA (point-ex Γ i A e tA)

  ends : ∀ A' → TyIn Γ A' → Ends Γ A' (wrapT A' pt)
  ends ⋆ _ = tt
  ends (arr B (var a) (var b)) (_ , _ , ea , eb , tB) =
    1 ,
    trans (nf-pt a B ea tB) (cong just (sym (fst (wrapT-ends Γ B a b pt tB)))) ,
    trans (nf-pt b B eb tB) (cong just (sym (snd (wrapT-ends Γ B a b pt tB))))
    where
    nf-pt : ∀ x B → lookup Γ x ≡ just B → TyIn Γ B → nf 1 Γ (var x) ≡ just (wrapT B (lt (x ∷ []) []))
    nf-pt x B ex tB rewrite ex = wrap-T Γ B _ tB
  ends (arr B (var a) (coh _ _ _)) ()
  ends (arr B (var a) (cst ()))    _
  ends (arr B (coh _ _ _) _)       ()
  ends (arr B (cst ()) _)          _

  labs : ∀ y → mem y w ≡ memL y (fvTmTy (var i) A)
  labs y = trans (wrapT-mem Γ A pt y tA) (∨-swap (memL y (fvTy A)) (y ==ℕ i))

------------------------------------------------------------------------
-- The images of the variables of a globular context under the
-- identity are typed in the sense of ExGood (so `TypedImg` is
-- inhabited for every globular Θ, not only assumed).

open import CaTTExp.GlobularTotal.ExGood using (TypedImg; Bnd)

typedImg-id : ∀ Θ → Glob Θ → TypedImg Θ (λ y → nf 1 Θ (var y))
typedImg-id Θ g y A e = w , nf-eq , wf , dm , bnd A tA
  where
  tA = g y A e
  pt = lt (y ∷ []) []
  w  = wrapT A pt

  nf-pt : ∀ x B → lookup Θ x ≡ just B → TyIn Θ B → nf 1 Θ (var x) ≡ just (wrapT B (lt (x ∷ []) []))
  nf-pt x B ex tB rewrite ex = wrap-T Θ B _ tB

  nf-eq : nf 1 Θ (var y) ≡ just w
  nf-eq = nf-pt y A e tA

  wf : WF w
  wf = wrapT-wf Θ A pt tA (refl , tt)

  dm : ∀ β i → bd β (dim A + i) w ≡ w
  dm β k = wrapT-dim Θ A y β k tA

  bnd : ∀ A' → TyIn Θ A' → Bnd (λ y → nf 1 Θ (var y)) A' (wrapT A' pt)
  bnd ⋆ _ = tt
  bnd (arr B (var a) (var b)) (_ , _ , ea , eb , tB) =
    trans (nf-pt a B ea tB) (cong just (sym (fst (wrapT-ends Θ B a b pt tB)))) ,
    trans (nf-pt b B eb tB) (cong just (sym (snd (wrapT-ends Θ B a b pt tB))))
  bnd (arr B (var a) (coh _ _ _)) ()
  bnd (arr B (var a) (cst ()))    _
  bnd (arr B (coh _ _ _) _)       ()
  bnd (arr B (cst ()) _)          _
