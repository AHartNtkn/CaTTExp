------------------------------------------------------------------------
-- The metatheory of CaTT with INIT (spec §9.3), as instances of the
-- generic results for binders: for every base signature whose constants
-- have closed types, every coh side condition and every mark judgment,
--
--   * substitution is admissible (CaTTExp.Binder.Subst with the laws of
--     CaTTExp.Binder.InitLaws), given that the mark judgment is stable
--     (MarkRen, MarkSub, MarkVar; CaTTExp.Binder.VarMark proves them
--     for the judgment with rule (MARK) only);
--   * the certified checker is complete, and all judgments are
--     decidable (CaTTExp.Binder.Completeness), given that equality of
--     base constants is reflexive and `valid?` succeeds on valid
--     constants.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Init
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM

module CaTTExp.Binder.InitMeta
  (bs : Base)
  (side : Signature.Ctx (initSig bs) → Signature.Ty (initSig bs) →
          Signature.Tm (initSig bs) → Signature.Tm (initSig bs) → Bool)
  (mark : Signature.Ctx (initSig bs) → BM.Mark → Signature.Tm (initSig bs) → Bool)
  where

open Base bs using (_==K_; Valid; valid?)
open Signature (initSig bs) using (Ctx; Ty; Tm; Sub; _[_]ty; _[_]tm; _∘_)
open import CaTTExp.Binder.Laws (initSig bs) using (Closed)
open import CaTTExp.Binder.InitLaws bs using (initLaws)

open import CaTTExp.Binder.Rename (initSig bs) side mark using (MarkRen)
open import CaTTExp.Binder.Subst (initSig bs) side mark using (MarkSub; MarkVar)

module Substitution (closed : Closed) (mren : MarkRen) (msub : MarkSub) (mvar : MarkVar) where
  open import CaTTExp.Binder.Subst (initSig bs) side mark
  open import CaTTExp.Binder.TypingWith (initSig bs) side mark

  tm-subst : ∀ {Γ Δ t A σ} → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Δ ⊢tm t [ σ ]tm ∶ A [ σ ]ty
  tm-subst = tm[] closed initLaws mren msub mvar

  ty-subst : ∀ {Γ Δ A σ} → Γ ⊢ty A → Δ ⊢sub σ ∶ Γ → Δ ⊢ty A [ σ ]ty
  ty-subst = ty[] closed initLaws mren msub mvar

  sub-subst : ∀ {Θ Γ Δ τ σ} → Θ ⊢ctx → Γ ⊢sub τ ∶ Θ → Δ ⊢sub σ ∶ Γ → Δ ⊢sub τ ∘ σ ∶ Θ
  sub-subst = sub∘ closed initLaws mren msub mvar

module Decidability
  (==K-refl : ∀ k → T (k ==K k))
  (valid?-complete : ∀ k → Valid k → T (is-just (valid? k)))
  where
  open import CaTTExp.Binder.Completeness (initSig bs) side mark ==K-refl ==F-refl valid?-complete public
    using (Dec; dec-ctx; dec-ty; dec-tm; dec-sub; dec-args; ctx?-complete; infer-complete)
