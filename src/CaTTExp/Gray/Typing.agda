------------------------------------------------------------------------
-- Two-tier L: the instance of CaTTExp.TypingWith whose coh side
-- condition is the Gray-support condition of CaTTExp.Gray.Support.
-- Substitution is admissible by CaTTExp.Subst 𝕊 graySide.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.Typing (𝕊 : Signature) where

open import CaTTExp.Gray.Support 𝕊 using (graySide)
open import CaTTExp.TypingWith 𝕊 graySide public
