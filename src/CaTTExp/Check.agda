------------------------------------------------------------------------
-- The certified checker for plain CaTT.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Check (𝕊 : Signature) where

open import CaTTExp.Typing 𝕊 using (cattSide)
open import CaTTExp.CheckWith 𝕊 cattSide public
