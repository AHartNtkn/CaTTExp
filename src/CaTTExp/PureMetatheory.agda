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

------------------------------------------------------------------------
-- Constant substitutions (C8.2): every pure context Γ has
-- (c : ⋆) ⊢ !_Γ ∶ Γ.

import CaTTExp.ConstSub ∅ as K
open K public using (D₀; fill)

! : Ctx → Sub
! = K.! closed

private
  mutual
    nc-ty : ∀ A → K.NcTy A
    nc-ty ⋆           = tt
    nc-ty (arr A t u) = nc-ty A , nc-tm t , nc-tm u

    nc-tm : ∀ t → K.NcTm t
    nc-tm (var _)     = tt
    nc-tm (coh _ _ σ) = nc-sub σ
    nc-tm (cst ())

    nc-sub : ∀ σ → K.NcSub σ
    nc-sub ⟨⟩       = tt
    nc-sub (σ ,ₛ t) = nc-sub σ , nc-tm t

  nc-ctx : ∀ Γ → K.NcCtx Γ
  nc-ctx ε       = tt
  nc-ctx (Γ ▸ A) = nc-ctx Γ , nc-ty A

!-wf : ∀ {Γ} → Γ ⊢ctx → D₀ ⊢sub ! Γ ∶ Γ
!-wf {Γ} w = fst (K.!-wf closed w (nc-ctx Γ))

------------------------------------------------------------------------
-- Suspension and elements elaboration (C8.1), with no hypothesis.

import CaTTExp.Suspension ∅ as Σs
open Σs public using (Σty; Σtm; Σsub; Σctx)

private
  mutual
    fnc-ty : ∀ A → Σs.FNcTy A
    fnc-ty ⋆           = tt
    fnc-ty (arr A t u) = fnc-ty A , fnc-tm t , fnc-tm u

    fnc-tm : ∀ t → Σs.FNcTm t
    fnc-tm (var _)     = tt
    fnc-tm (coh Θ A σ) = fnc-ctx Θ , fnc-ty A , fnc-sub σ
    fnc-tm (cst ())

    fnc-sub : ∀ σ → Σs.FNcSub σ
    fnc-sub ⟨⟩       = tt
    fnc-sub (σ ,ₛ t) = fnc-sub σ , fnc-tm t

    fnc-ctx : ∀ Γ → Σs.FNcCtx Γ
    fnc-ctx ε       = tt
    fnc-ctx (Γ ▸ A) = fnc-ctx Γ , fnc-ty A

Σctx-wf : ∀ {Γ} → Γ ⊢ctx → Σctx Γ ⊢ctx
Σctx-wf {Γ} w = Σs.Σctx-wf w (fnc-ctx Γ)

Σty-wf : ∀ {Γ A} → Γ ⊢ty A → Σctx Γ ⊢ty Σty A
Σty-wf {Γ} {A} a = Σs.Σty-wf a (fnc-ctx Γ) (fnc-ty A)

Σtm-wf : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Σctx Γ ⊢tm Σtm t ∶ Σty A
Σtm-wf {Γ} {t} d = Σs.Σtm-wf d (fnc-ctx Γ) (fnc-tm t)

Σsub-wf : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → Σctx Γ ⊢sub Σsub σ ∶ Σctx Δ
Σsub-wf {Γ} {σ} s = Σs.Σsub-wf s (fnc-ctx Γ) (fnc-sub σ)

elements : ∀ {Γ Δ t A γ} → Γ ⊢tm t ∶ A → Δ ⊢sub γ ∶ Σctx Γ →
           Δ ⊢tm Σtm t [ γ ]tm ∶ Σty A [ γ ]ty
elements {Γ} {t = t} d g = Σs.elements closed d (fnc-ctx Γ) (fnc-tm t) g
