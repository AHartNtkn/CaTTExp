------------------------------------------------------------------------
-- The explicit vertical composition of VCompExplicit is the
-- elaborator's (VComp.compSub, on Cylinder.cyl sd 2), syntactically, on
-- every shape checked in Checks.VComp and more: D⁰–D², the composable
-- pair, the vertical and the horizontal pair of 2-cells, both
-- orientations.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Checks.VCompAgree where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.CylGen using (Side; right; left)
open import CaTTExp.GrayCtx.Cylinder using (cyl)
open import CaTTExp.GrayCtx.VComp using (compSub)
open import CaTTExp.GrayCtx.VCompExplicit
open import CaTTExp.GrayCtx.Checks.Base using (D; Comp₂; HComp; VComp)

------------------------------------------------------------------------
-- Agreement with the elaborator.

agreeC : Side → Ctx → Bool
agreeC sd Γ with cyl sd 2 Γ
... | just Γ' = Γ' ==Ctx cyl2E sd Γ
... | nothing = false

agreeS : Side → Ctx → Bool
agreeS sd Γ with compSub sd Γ
... | just (Γ' , σ) = (Γ' ==Ctx cyl2E sd Γ) ∧ (σ ==Sub compE sd Γ)
... | nothing = false

agree : Side → Ctx → Bool
agree sd Γ = agreeC sd Γ ∧ agreeS sd Γ

agree-D : T (agree right (D 0) ∧ agree left (D 0) ∧ agree right (D 1) ∧ agree left (D 1)
             ∧ agree right (D 2) ∧ agree left (D 2))
agree-D = tt

agree-pairs : T (agree right Comp₂ ∧ agree left Comp₂ ∧ agree right VComp ∧ agree left VComp
                 ∧ agree right HComp ∧ agree left HComp)
agree-pairs = tt
