------------------------------------------------------------------------
-- The metatheorems instantiated for pure CaTT (the empty signature,
-- Finster–Mimram's side condition): substitution admissibility (A1)
-- and completeness / decidability of the checker (A2). The signature
-- hypotheses hold vacuously.
------------------------------------------------------------------------
module CaTTExp.PureMetatheory where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Subst ∅ cattSide as S
import CaTTExp.Completeness ∅ cattSide (λ ()) (λ ()) as C

closed : S.Closed
closed ()

tm[] : ∀ {Γ Δ t A σ} → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Δ ⊢tm t [ σ ]tm ∶ A [ σ ]ty
tm[] = S.tm[] closed

ty[] : ∀ {Γ Δ A σ} → Γ ⊢ty A → Δ ⊢sub σ ∶ Γ → Δ ⊢ty A [ σ ]ty
ty[] = S.ty[] closed

sub∘ : ∀ {Θ Γ Δ τ σ} → Θ ⊢ctx → Γ ⊢sub τ ∶ Θ → Δ ⊢sub σ ∶ Γ → Δ ⊢sub τ ∘ σ ∶ Θ
sub∘ = S.sub∘ closed

open C public using (Dec; yes; no; dec-ctx; dec-ty; dec-tm; dec-sub; tm-unique;
                     checkCtx-complete; checkTy-complete; inferTm-complete; checkSub-complete)
