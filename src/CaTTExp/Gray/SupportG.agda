------------------------------------------------------------------------
-- Two-tier L with a coherence-case predicate as a parameter
-- (S30, notes/lax-sc-completeness.md §4).
--
-- CaTTExp.Gray.Support fixes the coherence case (full Gray support) and
-- its support function `topS` dispatches on that fixed predicate. Here
-- the predicate is a parameter
--
--     cc : Ctx → Ty → TSet → TSet → Bool      (Θ, A, supp t A, supp u A)
--
-- and `topS` dispatches on it: a coh in the cc-case has the identity
-- image (top chain empty), every other coh the total cell T(Θ). The
-- operation case is stated with *closure* comparisons (sameDownClosure),
-- the form in which lemma (B) is proved; the generator form used by
-- graySide agrees with it on every comparison it makes in a pasting
-- context (Gray.Graded), but that agreement is not used here.
--
-- Everything not involving topS (tuples, Gray unfoldings, the total
-- cell, downward closures) is Gray.Support's own definition.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.SupportG
  (𝕊 : Signature)
  (cc : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → List (List Nat) → List (List Nat) → Bool)
  where

open Signature 𝕊
open import CaTTExp.Gray.Support 𝕊 public
  hiding (topS; topsSub; suppTy; supp; cohCase; opCase; graySide; agreeSide)

mutual
  topS : Tm → TSet
  topS (var v)              = (v ∷ []) ∷ []
  topS (cst _)              = []
  topS (coh Θ ⋆ ρ)          = []
  topS (coh Θ (arr A t u) ρ) =
    applyF (topsSub ρ) (if cohG Θ A t u then [] else topT (homs Θ))

  topsSub : Sub → List TSet
  topsSub ⟨⟩       = []
  topsSub (ρ ,ₛ t) = topsSub ρ ++ (topS t ∷ [])

  suppTy : Ty → TSet
  suppTy ⋆                     = []
  suppTy (arr ⋆ _ _)           = []
  suppTy (arr (arr B s s') t u) = suppTy (arr B s s') ++ topS t ++ topS u

  supp : Tm → Ty → TSet
  supp t A = topS t ++ suppTy A

  -- the coherence case (never for A = ⋆)
  cohG : Ctx → Ty → Tm → Tm → Bool
  cohG Θ ⋆ t u = false
  cohG Θ A@(arr _ _ _) t u = cc Θ A (supp t A) (supp u A)

-- The operation case, closure form.
opCaseC : Ctx → Ty → Tm → Tm → Bool
opCaseC Θ ⋆ t u =
  (dimK (homs Θ) ==ℕ 0) ∧ isVarAt t (firstL (objs Θ)) ∧ isVarAt u (lastL (objs Θ))
opCaseC Θ A@(arr _ _ _) t u =
  endsOK Θ A ∧ (dim A ==ℕ dimK (homs Θ))
  ∧ sameDownClosure Θ (supp t A) (bdryT false (homs Θ))
  ∧ sameDownClosure Θ (supp u A) (bdryT true (homs Θ))

sideG : Ctx → Ty → Tm → Tm → Bool
sideG Θ A t u = cohG Θ A t u ∨ opCaseC Θ A t u
