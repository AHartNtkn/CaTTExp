------------------------------------------------------------------------
-- The typing rules of CaTT (Finster–Mimram 2017), relative to a
-- signature of closed constants.
--
-- Differences from the paper, all standard:
--  * de Bruijn levels instead of names;
--  * the "operation" side condition asks t : A to be typed in Γ with
--    Var(t:A) = Var(∂⁻Γ), rather than typed in ∂⁻Γ itself;
--  * side conditions are booleans lifted with T, so they are decidable
--    by construction.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Typing (𝕊 : Signature) where

open Signature 𝕊

infix 4 _⊢ctx _⊢ty_ _⊢tm_∶_ _⊢sub_∶_ _⊢ps_∶_ _⊢ps

------------------------------------------------------------------------
-- Pasting contexts: Γ ⊢ps x ∶ A says Γ is a pasting context under
-- construction whose current "dangling" cell is the variable x of type A.

data _⊢ps_∶_ : Ctx → Nat → Ty → Set where
  pss : ε ▸ ⋆ ⊢ps 0 ∶ ⋆
  pse : ∀ {Γ x A} → Γ ⊢ps x ∶ A →
        (Γ ▸ A ▸ arr A (var x) (var (len Γ))) ⊢ps suc (len Γ) ∶ arr A (var x) (var (len Γ))
  psd : ∀ {Γ f A x y} → Γ ⊢ps f ∶ arr A (var x) (var y) → Γ ⊢ps y ∶ A

data _⊢ps : Ctx → Set where
  ps : ∀ {Γ x} → Γ ⊢ps x ∶ ⋆ → Γ ⊢ps

------------------------------------------------------------------------
-- Side conditions of the coh rule.

-- Full coherence: both sides use every variable of Γ.
isCoh : Ctx → Ty → Tm → Tm → Bool
isCoh Γ A t u = ≈? (fvTmTy t A) (varsCtx Γ) ∧ ≈? (fvTmTy u A) (varsCtx Γ)

-- Operation (composite): the source uses exactly ∂⁻Γ, the target ∂⁺Γ.
isOp : Ctx → Ty → Tm → Tm → Bool
isOp Γ A t u = ≈? (fvTmTy t A) (∂⁻ Γ) ∧ ≈? (fvTmTy u A) (∂⁺ Γ)

------------------------------------------------------------------------
-- The judgments.

mutual
  data _⊢ctx : Ctx → Set where
    ε-wf : ε ⊢ctx
    ▸-wf : ∀ {Γ A} → Γ ⊢ctx → Γ ⊢ty A → Γ ▸ A ⊢ctx

  data _⊢ty_ (Γ : Ctx) : Ty → Set where
    ⋆-wf   : Γ ⊢ctx → Γ ⊢ty ⋆
    arr-wf : ∀ {A t u} → Γ ⊢tm t ∶ A → Γ ⊢tm u ∶ A → Γ ⊢ty arr A t u

  data _⊢tm_∶_ (Γ : Ctx) : Tm → Ty → Set where
    var-wf : ∀ {i A} → Γ ⊢ctx → lookup Γ i ≡ just A → Γ ⊢tm var i ∶ A
    coh-wf : ∀ {Δ A t u σ} →
             Δ ⊢ps → Δ ⊢ctx → Δ ⊢ty arr A t u →
             T (isCoh Δ A t u ∨ isOp Δ A t u) →
             Γ ⊢sub σ ∶ Δ →
             Γ ⊢tm coh Δ (arr A t u) σ ∶ (arr A t u) [ σ ]ty
    cst-wf : ∀ {k} → Γ ⊢ctx → Valid k → Γ ⊢tm cst k ∶ ty k

  data _⊢sub_∶_ (Γ : Ctx) : Sub → Ctx → Set where
    ⟨⟩-wf : Γ ⊢ctx → Γ ⊢sub ⟨⟩ ∶ ε
    ,-wf  : ∀ {σ Δ t A} → Γ ⊢sub σ ∶ Δ → Γ ⊢tm t ∶ A [ σ ]ty →
            Γ ⊢sub σ ,ₛ t ∶ Δ ▸ A
