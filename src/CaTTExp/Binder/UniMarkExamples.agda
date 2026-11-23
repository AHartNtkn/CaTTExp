------------------------------------------------------------------------
-- Examples for CaTTExp.Binder.UniMark, on the horns of
-- CaTTExp.Binder.UniHeadsExamples (the arrow, n = 0, 1): the comparison
-- components are inv, the filler uni^w is not, and the checker with
-- (UNI-inv) in its mark judgment still types the fillers and still
-- rejects an argument for m_f that is not inv. Every statement is
-- `refl`.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.UniHeads
open import CaTTExp.Binder.UniHeadsExamples
  using (coneShape; hornShape; Arr; H₀; H₁; uni₀; uni₁; L; unmark)
open import CaTTExp.Binder.UniMark coneShape hornShape

module CaTTExp.Binder.UniMarkExamples where

open Signature 𝕊
open import CaTTExp.Binder.Typing 𝕊 using (cattSide)
open import CaTTExp.Binder.CheckWith 𝕊 cattSide headMark

inferTy : Ctx → Tm → Maybe Ty
inferTy Γ t = infer Γ t >>= λ r → just (fst r)

-- (UNI-inv): the components are inv, uni^w is not, at n = 0 and 1.
comps-inv : (headMark H₀ minv (uni₀ 1) ∧ headMark H₀ minv (uni₀ 2) ∧ headMark H₀ minv (uni₀ 3)
           ∧ headMark H₁ minv (uni₁ 1) ∧ headMark H₁ minv (uni₁ 3)) ≡ true
comps-inv = refl

filler-not-inv : (headMark H₀ minv (uni₀ 0) ∨ headMark H₁ minv (uni₁ 0)) ≡ false
filler-not-inv = refl

-- Only inv: a component carries no other mark.
comp-not-ps : headMark H₀ mps (uni₀ 1) ≡ false
comp-not-ps = refl

-- The limit and the legs are not inv by (UNI-inv).
lim-not-inv : headMark H₀ minv L ≡ false
lim-not-inv = refl

-- Typing with this mark judgment: the fillers are typed as before.
uni₀-ty : inferTy H₀ (uni₀ 0) ≡ just (arr ⋆ (var 3) L)
uni₀-ty = refl

uni₁-ty : inferTy H₁ (uni₁ 0) ≡ just (arr (arr ⋆ (var 3) L) (var 4) (var 5))
uni₁-ty = refl

-- A variable for m_f that is not marked inv is still rejected.
no-uni₁-unmarked : inferTy (unmark H₁) (uni₁ 0) ≡ nothing
no-uni₁-unmarked = refl
