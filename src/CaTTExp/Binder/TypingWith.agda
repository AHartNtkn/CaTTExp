------------------------------------------------------------------------
-- The typing rules of CaTT with binding formers, relative to a
-- signature (constants and a binder interface) and to the side
-- condition of the coh rule.
--
-- The rules of CaTTExp.TypingWith, plus one generic rule for binders:
--
--   Δ's free variables are below len Γ    Δ is locally closed
--   Γ ⧺ openTel (len Γ) Δ ⊢               bside b y Δ
--   Γ ⊢ ts ∶ bargs b y Δ   (args)
--   ─────────────────────────────────────────────────────────────── (bnd)
--            Γ ⊢ bnd b y Δ ts ∶ opTy 0 ts (bres b y Δ)
--
-- The telescope premise opens Δ with the variables that follow Γ, so
-- Δ is a well-formed context extension of Γ. The argument judgment
-- types the j-th argument at the j-th entry of the argument telescope,
-- instantiated with the arguments before it. The two Boolean scoping
-- premises say Δ mentions no variable of a longer context and no bound
-- variable of an enclosing binder (the second follows from the
-- telescope premise for any reasonable interface, but stating it keeps
-- the metatheory free of hypotheses on result types). No rule types a
-- `bvar`, so well-typed terms are locally closed.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature

module CaTTExp.Binder.TypingWith
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.Binder.Pasting 𝕊 public

infix 4 _⊢ctx _⊢ty_ _⊢tm_∶_ _⊢sub_∶_ _⊢args_∶_

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
    bnd-wf : ∀ {b y Δ ts} →
             T (scTel? (len Γ) Δ) → T (lcTel? 1 Δ) →
             (Γ ⧺ openTel (len Γ) Δ) ⊢ctx →
             T (bside b y Δ) →
             Γ ⊢args ts ∶ bargs b y Δ →
             Γ ⊢tm bnd b y Δ ts ∶ opTy 0 ts (bres b y Δ)

  data _⊢sub_∶_ (Γ : Ctx) : Sub → Ctx → Set where
    ⟨⟩-wf : Γ ⊢ctx → Γ ⊢sub ⟨⟩ ∶ ε
    ,-wf  : ∀ {σ Δ t A} → Γ ⊢sub σ ∶ Δ → Γ ⊢tm t ∶ A [ σ ]ty →
            Γ ⊢sub σ ,ₛ t ∶ Δ ▸ A

  -- Arguments of a binder against a locally nameless telescope.
  data _⊢args_∶_ (Γ : Ctx) : Sub → Ctx → Set where
    ⟨⟩-a : Γ ⊢ctx → Γ ⊢args ⟨⟩ ∶ ε
    ,-a  : ∀ {ts Θ t A} → Γ ⊢args ts ∶ Θ → Γ ⊢tm t ∶ opTy 0 ts A →
           Γ ⊢args ts ,ₛ t ∶ Θ ▸ A
