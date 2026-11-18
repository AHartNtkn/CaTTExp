------------------------------------------------------------------------
-- Declared operations over contexts (ledger F9, notes/ordinary-math.md
-- §8): CaTT extended by a list of *declared operations* (Δ, B), each
-- usable as  coh Δ B σ  for any σ : Γ → Δ.
--
-- This is the syntax F9 asked for ("operations over a context applied
-- to a substitution, beyond coh"), and it needs no change to
-- CaTTExp.Syntax: a declared operation is a `coh` over a context that
-- is not a pasting context, admitted because it is declared. Rules of
-- the form "for every instance of the context Δ there is a term of
-- type B" (a recursor, a universal arrow, a filler) are of this shape;
-- their parameters are supplied by substitution, so every rule holds
-- over every parameter context at once. CaTTExp.Ops.Subst proves
-- substitution admissible, CaTTExp.Ops.Check is a certified checker,
-- and CaTTExp.Ops.Nat declares the recursor of the natural numbers.
--
-- A declaration is the user's responsibility in the same way as a
-- signature constant: each (Δ, B) must be well formed (Δ a context, B a
-- type in it) and sound in the intended semantics. Well-formedness is
-- decidable and is checked once per declaration (see Ops.Nat).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Ops.Typing
  (𝕊 : Signature)
  (ops : List (Σ (Signature.Ctx 𝕊) (λ _ → Signature.Ty 𝕊)))
  where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊 public
open import CaTTExp.Typing 𝕊 using (cattSide)

infix 4 _∈_ _⊢ctx _⊢ty_ _⊢tm_∶_ _⊢sub_∶_

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

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
             T (cattSide Δ A t u) →
             Γ ⊢sub σ ∶ Δ →
             Γ ⊢tm coh Δ (arr A t u) σ ∶ (arr A t u) [ σ ]ty
    cst-wf : ∀ {k} → Γ ⊢ctx → Valid k → Γ ⊢tm cst k ∶ ty k
    -- A declared operation, at any instance of its context.
    op-wf  : ∀ {Δ B σ} → (Δ , B) ∈ ops → Γ ⊢sub σ ∶ Δ →
             Γ ⊢tm coh Δ B σ ∶ B [ σ ]ty

  data _⊢sub_∶_ (Γ : Ctx) : Sub → Ctx → Set where
    ⟨⟩-wf : Γ ⊢ctx → Γ ⊢sub ⟨⟩ ∶ ε
    ,-wf  : ∀ {σ Δ t A} → Γ ⊢sub σ ∶ Δ → Γ ⊢tm t ∶ A [ σ ]ty →
            Γ ⊢sub σ ,ₛ t ∶ Δ ▸ A
