module CaTTExp.GrayCtx.Checks.Prune where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Cylinder
open import CaTTExp.GrayCtx.Prune
open import CaTTExp.GrayCtx.Checks.Base

------------------------------------------------------------------------
-- 6. D6 datum: the cylinder of the pruning D¹ → D² (α ↦ id f) is a
--    well-typed substitution D¹ ⊗ D¹ ⊢ π ⊗ D¹ : D² ⊗ D¹, in both
--    orientations (CaTTExp.GrayCtx.Prune).

prune-right : WFSub (prunedCyl right) (fromJust (D 2 ⊗D¹))
prune-right = cert (wfSub? _ _) tt

prune-left : WFSub (prunedCyl left) (fromJust (D¹⊗ D 2))
prune-left = cert (wfSub? _ _) tt
