module CaTTExp.GrayCtx.Checks.Cylinders where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Cylinder
open import CaTTExp.GrayCtx.Checks.Base

------------------------------------------------------------------------
-- 1. Γ ⊗ D¹ and D¹ ⊗ Γ for named pasting schemes.
D¹⊗D¹ : WF (D 1 ⊗D¹)
D¹⊗D¹ = cert (wf? _) tt
D²⊗D¹ : WF (D 2 ⊗D¹)
D²⊗D¹ = cert (wf? _) tt
D³⊗D¹ : WF (D 3 ⊗D¹)
D³⊗D¹ = cert (wf? _) tt
D⁴⊗D¹ : WF (D 4 ⊗D¹)
D⁴⊗D¹ = cert (wf? _) tt
D⁵⊗D¹ : WF (D 5 ⊗D¹)
D⁵⊗D¹ = cert (wf? _) tt

D¹⊗D² : WF (D¹⊗ D 2)
D¹⊗D² = cert (wf? _) tt
D¹⊗D³ : WF (D¹⊗ D 3)
D¹⊗D³ = cert (wf? _) tt
D¹⊗D⁴ : WF (D¹⊗ D 4)
D¹⊗D⁴ = cert (wf? _) tt
D¹⊗D⁵ : WF (D¹⊗ D 5)
D¹⊗D⁵ = cert (wf? _) tt

HComp⊗D¹ : WF (HComp ⊗D¹)
HComp⊗D¹ = cert (wf? _) tt
D¹⊗HComp : WF (D¹⊗ HComp)
D¹⊗HComp = cert (wf? _) tt

-- Globular but not a pasting scheme: two parallel 1-cells (the 1-sphere).
Sphere₁ : Ctx
Sphere₁ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ arr ⋆ (var 0) (var 1)

Sphere₁⊗D¹ : WF (Sphere₁ ⊗D¹)
Sphere₁⊗D¹ = cert (wf? _) tt

------------------------------------------------------------------------
-- 2. Every pasting scheme with at most 4 edges (all 23 plane trees),
--    in both orientations.

private
  okR okL : Tree → Bool
  okR t = is-just (wf? (ctxOf t ⊗D¹))
  okL t = is-just (wf? (D¹⊗ ctxOf t))

  allR : T (all okR (trees≤ 4))
  allR = tt
  allL : T (all okL (trees≤ 4))
  allL = tt

cylR-≤4 : ∀ {t} → t ∈ trees≤ 4 → WF (ctxOf t ⊗D¹)
cylR-≤4 {t} m = cert (wf? (ctxOf t ⊗D¹)) (all-∈ okR (trees≤ 4) allR m)

cylL-≤4 : ∀ {t} → t ∈ trees≤ 4 → WF (D¹⊗ ctxOf t)
cylL-≤4 {t} m = cert (wf? (D¹⊗ ctxOf t)) (all-∈ okL (trees≤ 4) allL m)

