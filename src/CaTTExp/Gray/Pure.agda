------------------------------------------------------------------------
-- Pure two-tier L: the empty signature.
------------------------------------------------------------------------
module CaTTExp.Gray.Pure where

open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Pure using (∅; ⟪_⟫) public

open Signature ∅ public
open import CaTTExp.Gray.Support ∅ public
open import CaTTExp.Gray.Typing ∅ public
open import CaTTExp.PastingTrees ∅ public
open import CaTTExp.Gray.Check ∅ public

-- Substitution is admissible in pure two-tier L (CaTTExp.Subst, with
-- the trivially closed empty signature).
import CaTTExp.Subst ∅ graySide as Subst

substL : ∀ {Γ Δ t A σ} → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Δ ⊢tm t [ σ ]tm ∶ A [ σ ]ty
substL = Subst.tm[] (λ ())
