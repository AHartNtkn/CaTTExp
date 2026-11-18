------------------------------------------------------------------------
-- Gray cylinders Γ ⊗ Pₚ (right) and Pₚ ⊗ Γ (left).
--
-- For one edge and globular Γ (every pasting scheme, spheres, loops),
-- the cylinder is the disk-by-disk construction cylN of
-- CaTTExp.GrayCtx.Natural: each generator x⊗e is the top generator of
-- D^{dim x} ⊗ D¹ renamed along χ_x ⊗ D¹. CaTTExp.GrayCtx.NaturalWF
-- proves it well formed for every well-formed globular Γ, given the
-- disks; CaTTExp.GrayCtx.Checks.Natural certifies the disks up to
-- dimension 5. Otherwise (several edges, or composite boundaries as in
-- D¹ ⊗ D¹) it is the elaborator `cylGen` of CaTTExp.GrayCtx.CylGen run
-- on Γ itself. The two agree on every globular context tested
-- (CaTTExp.GrayCtx.Checks.NaturalAgree).
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Cylinder where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.CylGen public
open import CaTTExp.GrayCtx.Natural using (cylN; globular)

cyl : Side → Nat → Ctx → Maybe Ctx
cyl sd (suc zero) Γ = if globular Γ then just (cylN sd Γ) else cylGen sd 1 Γ
cyl sd p          Γ = cylGen sd p Γ

-- Γ ⊗ D¹ and D¹ ⊗ Γ.
_⊗D¹ D¹⊗_ : Ctx → Maybe Ctx
Γ ⊗D¹ = cyl right 1 Γ
D¹⊗ Γ = cyl left 1 Γ
