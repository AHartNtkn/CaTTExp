------------------------------------------------------------------------
-- List helpers of the biclosed checker (moved out of Typing so that
-- Rows can use them).
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.ListOps where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax

------------------------------------------------------------------------
-- List helpers

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

length : ∀ {A : Set} → List A → Nat
length []       = 0
length (_ ∷ xs) = suc (length xs)

lookup : ∀ {A : Set} → List A → Nat → Maybe A
lookup []       _       = nothing
lookup (x ∷ _)  zero    = just x
lookup (_ ∷ xs) (suc n) = lookup xs n

take : ∀ {A : Set} → Nat → List A → List A
take zero    _        = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

setAt : ∀ {A : Set} → Nat → A → List A → List A
setAt _       _ []       = []
setAt zero    y (_ ∷ xs) = y ∷ xs
setAt (suc n) y (x ∷ xs) = x ∷ setAt n y xs

concatIns : List MTy → List Fm
concatIns []       = []
concatIns (m ∷ ms) = ins m ++ concatIns ms

sumIns : List MTy → Nat
sumIns ms = length (concatIns ms)

