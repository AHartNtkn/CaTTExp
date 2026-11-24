------------------------------------------------------------------------
-- Checks for CaTTExp.Lim.HornGen: on the arrow it reproduces Lim/Horn's
-- hand-built horns exactly, and on a suite of diagrams of dimension
-- ≤ 1 its J2 contexts (n = 0, 1) pass the certified checker of plain
-- CaTT and of the L core. Every statement is `refl`.
------------------------------------------------------------------------
module CaTTExp.Lim.HornGenExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)
import CaTTExp.Gray.Pure as L
import CaTTExp.Lim.Horn as Horn
open import CaTTExp.Lim.HornGen

J2 : Ctx → Nat → Maybe Ctx
J2 Γ n = hornData Γ n >>= λ d → just (HornData.J2 d)

okP okL : Maybe Ctx → Bool
okP (just Γ) = is-just (checkCtx Γ)
okP nothing  = false
okL (just Γ) = is-just (L.checkCtx Γ)
okL nothing  = false

o : Ty
o = ⋆

a⟶ : Nat → Nat → Ty
a⟶ i j = arr ⋆ (var i) (var j)

Arr Pt Cospan Par Comp Loop : Ctx
Arr    = ε ▸ o ▸ o ▸ a⟶ 0 1
Pt     = ε ▸ o
Cospan = ε ▸ o ▸ o ▸ o ▸ a⟶ 0 2 ▸ a⟶ 1 2
Par    = ε ▸ o ▸ o ▸ a⟶ 0 1 ▸ a⟶ 0 1
Comp   = ε ▸ o ▸ o ▸ o ▸ a⟶ 0 1 ▸ a⟶ 1 2
Loop   = ε ▸ o ▸ a⟶ 0 0

-- The arrow: the hand-built horns are exactly Lim/Horn's.
arr₀ : hornDataHand Arr 0 ≡ just (hd Horn.J2₀ 4 [])
arr₀ = refl

arr₁ : hornDataHand Arr 1 ≡ just (hd Horn.J2₁ 6 Horn.marksP₁)
arr₁ = refl

-- The horns by cylinder lifts (every n) agree with them at n = 0. At
-- n = 1 F(U)_f is a different pasting of the same kind (the lift of
-- (u ∗₀ λ_f) ∗₁ assoc through the paste rule), so the contexts differ;
-- both are well formed in both cores (below, and Lim/Horn).
gen₀ : hornData Arr 0 ≡ hornDataHand Arr 0
gen₀ = refl

-- The suite, n = 0 and 1, in plain CaTT.
suiteP : (okP (J2 Pt 0) ∧ okP (J2 Pt 1) ∧ okP (J2 Cospan 0) ∧ okP (J2 Cospan 1)
          ∧ okP (J2 Par 0) ∧ okP (J2 Par 1) ∧ okP (J2 Comp 0) ∧ okP (J2 Comp 1)
          ∧ okP (J2 Loop 0) ∧ okP (J2 Loop 1)) ≡ true
suiteP = refl

-- And in the L core, n = 1 (the interchanger used is the forward one)
-- and n = 0.
suiteL : (okL (J2 Pt 1) ∧ okL (J2 Cospan 1) ∧ okL (J2 Par 1) ∧ okL (J2 Comp 1) ∧ okL (J2 Loop 1)) ≡ true
suiteL = refl

suiteL₀ : (okL (J2 Pt 0) ∧ okL (J2 Cospan 0) ∧ okL (J2 Par 0) ∧ okL (J2 Comp 0) ∧ okL (J2 Loop 0)) ≡ true
suiteL₀ = refl

-- The marked horn entries: the comparisons over the arrows.
marks-cospan : (hornData Cospan 1 >>= λ d → just (HornData.marked d)) ≡ just (17 ∷ 18 ∷ [])
marks-cospan = refl

-- 2-dimensional diagrams, n = 0: a 2-cell α : f ⇒ g (Mikhail's
-- Example 4.1) and an endo-2-cell on an arrow.
Two Endo2 : Ctx
Two   = ε ▸ o ▸ o ▸ a⟶ 0 1 ▸ a⟶ 0 1 ▸ arr (a⟶ 0 1) (var 2) (var 3)
Endo2 = Arr ▸ arr (a⟶ 0 1) (var 2) (var 2)

suite2P : (okP (J2 Two 0) ∧ okP (J2 Endo2 0)) ≡ true
suite2P = refl

suite2L : (okL (J2 Two 0) ∧ okL (J2 Endo2 0)) ≡ true
suite2L = refl

-- Not built: n ≥ 1 over 2-dimensional diagrams (S27 (e′): F(w)_α is a
-- depth-2 lift).
none : J2 Two 1 ≡ nothing
none = refl
