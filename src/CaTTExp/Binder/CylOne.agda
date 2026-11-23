------------------------------------------------------------------------
-- The dimension-1 filler family K₁ (CaTTExp.Naturality.DimOne) is
-- scoped in the cylinder context also after its embedding in binder
-- syntax, so CaTTExp.Binder.CylLaws applies to the binder cylinders
-- built with it.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Pure as P
open import CaTTExp.Naturality.DimOne using (K₁; K₁-sc; sc-complete)
import CaTTExp.Naturality.DimOne as D1

module CaTTExp.Binder.CylOne (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Binder.Pasting 𝕊 using (embTm; embSub)
open import CaTTExp.Binder.CylLaws 𝕊 K₁ using (KScoped)

mutual
  sc-embTm : ∀ n t → scTm? n (embTm t) ≡ D1.scTm? n t
  sc-embTm n (P.var i)     = refl
  sc-embTm n (P.coh _ _ γ) = sc-embSub n γ
  sc-embTm n (P.cst ())

  sc-embSub : ∀ n γ → scSub? n (embSub γ) ≡ D1.scSub? n γ
  sc-embSub n P.⟨⟩       = refl
  sc-embSub n (γ P.,ₛ t) = cong₂ _∧_ (sc-embSub n γ) (sc-embTm n t)

K₁-scB : KScoped
K₁-scB Q B Y =
  subst T (sym (trans (sc-embTm _ (K₁ Q B Y)) (sc-complete _ (K₁ Q B Y) (K₁-sc Q B Y)))) tt
