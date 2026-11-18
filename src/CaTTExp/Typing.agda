------------------------------------------------------------------------
-- The typing rules of CaTT (Finster–Mimram 2017), relative to a
-- signature of closed constants: the instance of CaTTExp.TypingWith
-- whose side condition is Finster–Mimram's.
--
-- Difference from the paper: the "operation" side condition asks
-- t : A to be typed in Γ with Var(t:A) = Var(∂⁻Γ), rather than typed
-- in ∂⁻Γ itself.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Typing (𝕊 : Signature) where

open Signature 𝕊

-- Full coherence: both sides use every variable of Γ.
isCoh : Ctx → Ty → Tm → Tm → Bool
isCoh Γ A t u = ≈? (fvTmTy t A) (varsCtx Γ) ∧ ≈? (fvTmTy u A) (varsCtx Γ)

-- Operation (composite): the source uses exactly ∂⁻Γ, the target ∂⁺Γ.
isOp : Ctx → Ty → Tm → Tm → Bool
isOp Γ A t u = ≈? (fvTmTy t A) (∂⁻ Γ) ∧ ≈? (fvTmTy u A) (∂⁺ Γ)

cattSide : Ctx → Ty → Tm → Tm → Bool
cattSide Δ A t u = isCoh Δ A t u ∨ isOp Δ A t u

open import CaTTExp.TypingWith 𝕊 cattSide public
