------------------------------------------------------------------------
-- Hypotheses on a signature with binders under which substitution is
-- admissible (CaTTExp.Binder.Subst).
--
--  * Closed: constants have closed types (as in CaTTExp.Subst).
--  * BinderLaws: the binder interface commutes with substitution of
--    the parameters by locally closed terms, and the result type is
--    scoped where the telescope is. These are the binder analogue of
--    "the coh side condition only sees the coh's own data".
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature

module CaTTExp.Binder.Laws (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B

Closed : Set
Closed = ∀ k → T (scTy? 0 (ty k))

record BinderLaws : Set where
  field
    side-stable : ∀ b y Δ σ → LC σ → T (bside b y Δ) → T (bside b y (Δ [ σ ]tel))
    args-stable : ∀ b y Δ σ → LC σ → T (bside b y Δ) →
                  bargs b y (Δ [ σ ]tel) ≡ (bargs b y Δ) [ σ ]tel
    res-stable  : ∀ b y Δ σ → LC σ → T (bside b y Δ) →
                  bres b y (Δ [ σ ]tel) ≡ (bres b y Δ) [ σ ]ty
    res-sc      : ∀ b y Δ n → T (bside b y Δ) → T (scTel? n Δ) → T (scTy? n (bres b y Δ))
