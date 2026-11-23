------------------------------------------------------------------------
-- Plain CaTT's side condition (Finster–Mimram) on the syntax with
-- binders, as in CaTTExp.Typing: the instance of
-- CaTTExp.Binder.TypingWith used by the examples.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature

module CaTTExp.Binder.Typing (𝕊 : Signature) where

open Signature 𝕊

isCoh : Ctx → Ty → Tm → Tm → Bool
isCoh Γ A t u = ≈? (fvTmTy t A) (varsCtx Γ) ∧ ≈? (fvTmTy u A) (varsCtx Γ)

isOp : Ctx → Ty → Tm → Tm → Bool
isOp Γ A t u = ≈? (fvTmTy t A) (∂⁻ Γ) ∧ ≈? (fvTmTy u A) (∂⁺ Γ)

cattSide : Ctx → Ty → Tm → Tm → Bool
cattSide Δ A t u = isCoh Δ A t u ∨ isOp Δ A t u

-- Marks are judged by rule (MARK) alone (CaTTExp.Binder.VarMark): only
-- a variable with that mark has it.
open import CaTTExp.Binder.TypingWith 𝕊 cattSide varMark public
