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
-- (The fold is top level so that proofs can reason about it.)
subGo : Sub → List Tm → Sub
subGo σ []       = σ
subGo σ (t ∷ ts) = subGo (σ ,ₛ t) ts

⟪_⟫ : List Tm → Sub
⟪ ts ⟫ = subGo ⟨⟩ ts
