------------------------------------------------------------------------
-- Constant-free syntax (ledger item A3a).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Strict.ConstFree (𝕊 : Signature) where

open Signature 𝕊


mutual
  CFTy : Ty → Set
  CFTy ⋆           = ⊤
  CFTy (arr A t u) = CFTy A × CFTm t × CFTm u

  CFTm : Tm → Set
  CFTm (var _)     = ⊤
  CFTm (coh _ A σ) = CFTy A × CFSub σ
  CFTm (cst _)     = ⊥

  CFSub : Sub → Set
  CFSub ⟨⟩       = ⊤
  CFSub (σ ,ₛ t) = CFSub σ × CFTm t

