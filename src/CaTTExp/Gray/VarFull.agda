------------------------------------------------------------------------
-- Var-fullness of a closed support (S30, notes/lax-sc-completeness.md §4):
-- every non-object variable of Θ is an entry of some tuple of ↓S.
--
-- The coherence clause of L^V (Gray.CohCaseVar, Gray.CohCaseVarSound)
-- asks this of both supp(t : A) and supp(u : A). Strict.G.SuppFV shows
-- that, over a pasting context and for A an arrow type, the variables
-- used by ↓supp(t : A) are exactly the non-object variables of t : A.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.VarFull (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Gray.Support 𝕊 using (TSet; down; objs; upto; any)

-- variable i occurs as an entry of some tuple of S
usesVar : Nat → TSet → Bool
usesVar i S = any (λ tup → any (λ j → i ==ℕ j) tup) S

isObj : Ctx → Nat → Bool
isObj Θ i = any (λ j → i ==ℕ j) (objs Θ)

-- every non-object variable of Θ occurs in the closed support
varFull : Ctx → TSet → Bool
varFull Θ S = all (λ i → isObj Θ i ∨ usesVar i (down Θ S)) (upto (len Θ ∸ 1))
