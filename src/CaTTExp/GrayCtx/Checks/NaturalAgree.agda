------------------------------------------------------------------------
-- The disk-by-disk cylinder cylN (CaTTExp.GrayCtx.Natural) agrees
-- syntactically with `cyl sd 1`, the elaborator run on Γ itself, on
-- every globular context tested. Together with Checks.Natural this
-- certifies well-formedness of `cyl sd 1 Γ` on these contexts by the
-- general theorem, and ties cylN's disk types to the elaborator.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Checks.NaturalAgree where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Cylinder
open import CaTTExp.GrayCtx.Natural
open import CaTTExp.GrayCtx.Checks.Base using (D; VComp; HComp; trees≤)

------------------------------------------------------------------------
-- Agreement with the elaborator run on Γ itself.

eqJ : Ctx → Maybe Ctx → Bool
eqJ Γ (just Δ) = Γ ==Ctx Δ
eqJ Γ nothing  = false

agree : Side → Ctx → Bool
agree sd Γ = eqJ (cylN sd Γ) (cylGen sd 1 Γ)

Sphere₁ Loop Loop² : Ctx
Sphere₁ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ arr ⋆ (var 0) (var 1)
Loop    = ε ▸ ⋆ ▸ arr ⋆ (var 0) (var 0)
Loop²   = Loop ▸ arr (arr ⋆ (var 0) (var 0)) (var 1) (var 1)

agree-disks : T (all (λ n → agree right (D n) ∧ agree left (D n)) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []))
agree-disks = tt

agree-trees≤4 : T (all (λ t → agree right (ctxOf t) ∧ agree left (ctxOf t)) (trees≤ 4))
agree-trees≤4 = tt

agree-other : T (all (λ Γ → agree right Γ ∧ agree left Γ) (Sphere₁ ∷ Loop ∷ Loop² ∷ VComp ∷ HComp ∷ []))
agree-other = tt

-- Non-vacuity: the disk types are the elaborator's, not ⋆.
disk-dims : T (all (λ j → (dim (TsF right j) ==ℕ suc j) ∧ (dim (TsF left j) ==ℕ suc j))
                   (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []))
disk-dims = tt
