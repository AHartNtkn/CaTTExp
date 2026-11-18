------------------------------------------------------------------------
-- The typing rules of CaTT-style theories, relative to a signature of
-- closed constants and to the *side condition* of the coh rule.
--
-- `side Δ A t u` decides whether coh_{Δ, t →_A u} is allowed. It sees
-- only the coh's own pasting context Δ and its type, never the
-- context the coh is used in. Plain CaTT (Finster–Mimram) is the
-- instance in CaTTExp.Typing; the Gray-style theory "two-tier L" is
-- the instance in CaTTExp.Gray.Typing. Metatheory proved here once
-- (CaTTExp.Subst) therefore holds for both.
--
-- Differences from the paper, all standard:
--  * de Bruijn levels instead of names;
--  * side conditions are booleans lifted with T, so they are decidable
--    by construction.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.TypingWith
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊 public

infix 4 _⊢ctx _⊢ty_ _⊢tm_∶_ _⊢sub_∶_

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
             T (side Δ A t u) →
             Γ ⊢sub σ ∶ Δ →
             Γ ⊢tm coh Δ (arr A t u) σ ∶ (arr A t u) [ σ ]ty
    cst-wf : ∀ {k} → Γ ⊢ctx → Valid k → Γ ⊢tm cst k ∶ ty k

  data _⊢sub_∶_ (Γ : Ctx) : Sub → Ctx → Set where
    ⟨⟩-wf : Γ ⊢ctx → Γ ⊢sub ⟨⟩ ∶ ε
    ,-wf  : ∀ {σ Δ t A} → Γ ⊢sub σ ∶ Δ → Γ ⊢tm t ∶ A [ σ ]ty →
            Γ ⊢sub σ ,ₛ t ∶ Δ ▸ A
