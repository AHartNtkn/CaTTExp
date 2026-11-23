------------------------------------------------------------------------
-- Evaluation check: the whisker heads of plain CaTT (Derived's
-- BK k j / wK k j and LK k j / lK k j) are accepted by the side
-- condition of two-tier L (graySide), for k + j ≤ 3. Here k = 0 is
-- whiskering across objects, a two-hom pasting context.
--
-- This is evidence, not a proof for all k, j: it is the first step
-- towards Theorem B's whiskering interface for two-tier L (see
-- notes/surface-conservativity.md §7). The general statement needs
-- graySide on these heads for every k, j.
------------------------------------------------------------------------
module CaTTExp.Surface.WhiskerGrayCheck where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Gray.Support ∅ using (graySide)
open import CaTTExp.Derived using (BK; wK; LK; lK)

sideOf : Ctx → Ty → Bool
sideOf Δ (arr A t u) = graySide Δ A t u
sideOf Δ ⋆ = false

r : Nat → Nat → Bool
r k j = sideOf (BK k j) (wK k j)
l : Nat → Nat → Bool
l k j = sideOf (LK k j) (lK k j)

_ : r 0 0 ≡ true
_ = refl
_ : r 0 1 ≡ true
_ = refl
_ : r 0 2 ≡ true
_ = refl
_ : r 0 3 ≡ true
_ = refl
_ : r 1 0 ≡ true
_ = refl
_ : r 1 1 ≡ true
_ = refl
_ : r 1 2 ≡ true
_ = refl
_ : r 2 0 ≡ true
_ = refl
_ : r 2 1 ≡ true
_ = refl
_ : r 3 0 ≡ true
_ = refl
_ : l 0 0 ≡ true
_ = refl
_ : l 0 1 ≡ true
_ = refl
_ : l 0 2 ≡ true
_ = refl
_ : l 0 3 ≡ true
_ = refl
_ : l 1 0 ≡ true
_ = refl
_ : l 1 1 ≡ true
_ = refl
_ : l 1 2 ≡ true
_ = refl
_ : l 2 0 ≡ true
_ = refl
_ : l 2 1 ≡ true
_ = refl
_ : l 3 0 ≡ true
_ = refl
