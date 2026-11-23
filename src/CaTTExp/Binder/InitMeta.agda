------------------------------------------------------------------------
-- The metatheory of CaTT with INIT (spec §9.3), as instances of the
-- generic results for binders: for every base signature whose constants
-- have closed types, and every coh side condition,
--
--   * substitution is admissible (CaTTExp.Binder.Subst with the laws of
--     CaTTExp.Binder.InitLaws);
--   * the certified checker is complete, and all judgments are
--     decidable (CaTTExp.Binder.Completeness), given that equality of
--     base constants is reflexive and `valid?` succeeds on valid
--     constants.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Init
open import CaTTExp.Binder.Signature

module CaTTExp.Binder.InitMeta
  (bs : Base)
  (side : Signature.Ctx (initSig bs) → Signature.Ty (initSig bs) →
          Signature.Tm (initSig bs) → Signature.Tm (initSig bs) → Bool)
  where

open Base bs using (_==K_; Valid; valid?)
open Signature (initSig bs) using (Ctx; Ty; Tm; Sub; _[_]ty; _[_]tm; _∘_)
open import CaTTExp.Binder.Laws (initSig bs) using (Closed)
open import CaTTExp.Binder.InitLaws bs using (initLaws)

module Substitution (closed : Closed) where
  open import CaTTExp.Binder.Subst (initSig bs) side
  open import CaTTExp.Binder.TypingWith (initSig bs) side

  tm-subst : ∀ {Γ Δ t A σ} → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Δ ⊢tm t [ σ ]tm ∶ A [ σ ]ty
  tm-subst = tm[] closed initLaws

  ty-subst : ∀ {Γ Δ A σ} → Γ ⊢ty A → Δ ⊢sub σ ∶ Γ → Δ ⊢ty A [ σ ]ty
  ty-subst = ty[] closed initLaws

  sub-subst : ∀ {Θ Γ Δ τ σ} → Θ ⊢ctx → Γ ⊢sub τ ∶ Θ → Δ ⊢sub σ ∶ Γ → Δ ⊢sub τ ∘ σ ∶ Θ
  sub-subst = sub∘ closed initLaws

module Decidability
  (==K-refl : ∀ k → T (k ==K k))
  (valid?-complete : ∀ k → Valid k → T (is-just (valid? k)))
  where
  open import CaTTExp.Binder.Completeness (initSig bs) side ==K-refl ==F-refl valid?-complete public
    using (Dec; dec-ctx; dec-ty; dec-tm; dec-sub; dec-args; ctx?-complete; infer-complete)
