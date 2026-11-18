------------------------------------------------------------------------
-- Finster–Mimram's pasting-context judgments. They do not depend on
-- the side condition of the coh rule, so they live in their own module
-- and are shared by every instance of CaTTExp.TypingWith.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Pasting (𝕊 : Signature) where

open Signature 𝕊

infix 4 _⊢ps_∶_ _⊢ps

-- Γ ⊢ps x ∶ A says Γ is a pasting context under construction whose
-- current "dangling" cell is the variable x of type A.

data _⊢ps_∶_ : Ctx → Nat → Ty → Set where
  pss : ε ▸ ⋆ ⊢ps 0 ∶ ⋆
  pse : ∀ {Γ x A} → Γ ⊢ps x ∶ A →
        (Γ ▸ A ▸ arr A (var x) (var (len Γ))) ⊢ps suc (len Γ) ∶ arr A (var x) (var (len Γ))
  psd : ∀ {Γ f A x y} → Γ ⊢ps f ∶ arr A (var x) (var y) → Γ ⊢ps y ∶ A

data _⊢ps : Ctx → Set where
  ps : ∀ {Γ x} → Γ ⊢ps x ∶ ⋆ → Γ ⊢ps
