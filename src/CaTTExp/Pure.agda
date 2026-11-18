------------------------------------------------------------------------
-- Pure CaTT: the empty signature.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Pure where

∅ : Signature
∅ = record
  { K         = ⊥
  ; _==K_     = λ ()
  ; ==K-sound = λ ()
  ; ty        = λ ()
  ; Valid     = λ ()
  ; valid?    = λ ()
  }

open Signature ∅ public
open import CaTTExp.Typing ∅ public
open import CaTTExp.PastingTrees ∅ public
open import CaTTExp.Check ∅ public

-- Build a substitution from a left-to-right list of terms.
⟪_⟫ : List Tm → Sub
⟪ ts ⟫ = go ⟨⟩ ts
  where
  go : Sub → List Tm → Sub
  go σ []       = σ
  go σ (t ∷ ts) = go (σ ,ₛ t) ts
