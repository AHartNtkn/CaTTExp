------------------------------------------------------------------------
-- Where the dimension-1 filler family suffices for binder cylinders.
--
-- For a selection s (on the bound variables of depth 0), `goodTy s A`
-- says that every touched term of A on which CaTTExp.Binder.Cyl's
-- cylinder is computed is a variable, or a coherence over a pure
-- pasting context with a pure type of dimension 1 (whose arguments are
-- again good): the coherences that CaTTExp.Naturality.DimOne's K₁
-- fills. Touched binder terms are not good (their cylinder is junk).
--
-- `goodTy-[]`: substituting a locally closed σ for the free variables
-- does not change it.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
open import CaTTExp.Naturality.Raw using (anyL)
open import CaTTExp.Naturality.DimOne using (K₁)

module CaTTExp.Binder.CylOK (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.Pasting 𝕊 using (toPure; toPureTy)
open import CaTTExp.Binder.Cyl 𝕊 K₁ using (occTm; occSub)
open import CaTTExp.Binder.CylLaws 𝕊 K₁ using (occ-lcTm; module Subst)

pureCB : Ctx → Ty → Bool
pureCB Q B = is-just (toPure Q) ∧ is-just (toPureTy B)

mutual
  goodTm : (Nat → Bool) → Tm → Bool
  goodTm s (var _)       = true
  goodTm s (bvar _ _)    = true
  goodTm s (coh Q B γ)   = if anyL s (occSub 0 γ) then (pureCB Q B ∧ (dim B ==ℕ 1)) ∧ goodSub s γ else true
  goodTm s (cst _)       = true
  goodTm s t@(bnd _ _ _ _) = not (anyL s (occTm 0 t))

  goodSub : (Nat → Bool) → Sub → Bool
  goodSub s ⟨⟩       = true
  goodSub s (γ ,ₛ t) = goodSub s γ ∧ goodTm s t

goodTy : (Nat → Bool) → Ty → Bool
goodTy s ⋆           = true
goodTy s (arr A t u) = goodTy s A ∧ goodTm s t ∧ goodTm s u

------------------------------------------------------------------------
-- Stability.

private
  anyL-[] : ∀ s → anyL s [] ≡ false
  anyL-[] s = refl

-- A locally closed term touches nothing, so it is good.
good-lc : ∀ s u → T (lcTm? 0 u) → goodTm s u ≡ true
good-lc s (var _)       _ = refl
good-lc s (bvar _ _)    _ = refl
good-lc s (coh Q B γ)   p rewrite occ-lcTm 0 0 (coh Q B γ) p = refl
good-lc s (cst _)       _ = refl
good-lc s (bnd b y Δ γ) p rewrite occ-lcTm 0 0 (bnd b y Δ γ) p = refl

module _ (σ : Sub) (l : LC σ) where
  open Subst σ l using (occ-[]tm; occ-[]sub)

  mutual
    goodTm-[] : ∀ s t → goodTm s (t [ σ ]tm) ≡ goodTm s t
    goodTm-[] s (var i)       = good-lc s (lookupₛ σ i) (lc-lookup σ i l)
    goodTm-[] s (bvar _ _)    = refl
    goodTm-[] s (coh Q B γ)   rewrite occ-[]sub 0 γ | goodSub-[] s γ = refl
    goodTm-[] s (cst _)       = refl
    goodTm-[] s (bnd b y Δ γ) = cong (λ z → not (anyL s z)) (occ-[]tm 0 (bnd b y Δ γ))

    goodSub-[] : ∀ s γ → goodSub s (γ ∘ σ) ≡ goodSub s γ
    goodSub-[] s ⟨⟩       = refl
    goodSub-[] s (γ ,ₛ t) rewrite goodSub-[] s γ | goodTm-[] s t = refl

  goodTy-[] : ∀ s A → goodTy s (A [ σ ]ty) ≡ goodTy s A
  goodTy-[] s ⋆           = refl
  goodTy-[] s (arr A t u) rewrite goodTy-[] s A | goodTm-[] s t | goodTm-[] s u = refl
