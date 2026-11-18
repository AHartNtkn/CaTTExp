------------------------------------------------------------------------
-- The certified checker for two-tier L.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.Check (𝕊 : Signature) where

open import CaTTExp.Gray.Support 𝕊 using (graySide)
open import CaTTExp.CheckWith 𝕊 graySide public
