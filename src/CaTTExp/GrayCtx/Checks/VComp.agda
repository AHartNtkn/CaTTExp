module CaTTExp.GrayCtx.Checks.VComp where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Cylinder
open import CaTTExp.GrayCtx.Checks.Base
open import CaTTExp.GrayCtx.VComp

------------------------------------------------------------------------
-- 4. Vertical composition of lax transformations as a substitution
--    Γ ⊗ (D¹ ∨ D¹) ⊢ comp : Γ ⊗ D¹,  for Γ of dimension ≤ 2.

VC : Side → Ctx → Set
VC sd Γ = WFSub (compSub sd Γ) (fromJust (cyl sd 1 Γ))

comp-D¹-right : VC right (D 1)
comp-D¹-right = cert (wfSub? _ _) tt
comp-D¹-left : VC left (D 1)
comp-D¹-left = cert (wfSub? _ _) tt
comp-D²-right : VC right (D 2)
comp-D²-right = cert (wfSub? _ _) tt
comp-D²-left : VC left (D 2)
comp-D²-left = cert (wfSub? _ _) tt

-- Two more shapes: a composable pair of 1-cells, and a horizontal pair
-- of 2-cells (the shape of horizontal composition).
comp-Comp₂-right : VC right Comp₂
comp-Comp₂-right = cert (wfSub? _ _) tt
comp-Comp₂-left : VC left Comp₂
comp-Comp₂-left = cert (wfSub? _ _) tt
comp-HComp-right : VC right HComp
comp-HComp-right = cert (wfSub? _ _) tt
