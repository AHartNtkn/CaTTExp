module CaTTExp.GrayCtx.Checks.G3 where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Cylinder
open import CaTTExp.GrayCtx.Checks.Base
open import CaTTExp.GrayCtx.VComp
open import CaTTExp.GrayCtx.Cube using (fromJust)

------------------------------------------------------------------------
-- 3. G3: Γ ⊗ (D¹ ∨ D¹) contains two copies of Γ ⊗ D¹, glued along the
-- middle copy of Γ. The inclusions are renamings; their images are
-- {copy 0, copy 1, edge i} and {copy 1, copy 2, edge j}, which cover all
-- variables and meet exactly in copy 1 (by the layout in Cylinder).
-- Well-typedness of a renaming says each generator of Γ ⊗ (D¹ ∨ D¹) has
-- literally the renamed type of the corresponding generator of Γ ⊗ D¹.

G3 : Side → Ctx → Set
G3 sd Γ = WFSub ((λ Δ → Δ , ι₁ (len Γ)) <$> cyl sd 2 Γ) (fromJust (cyl sd 1 Γ))
        × WFSub ((λ Δ → Δ , ι₂ (len Γ)) <$> cyl sd 2 Γ) (fromJust (cyl sd 1 Γ))

g3? : (sd : Side) (Γ : Ctx) → Maybe (G3 sd Γ)
g3? sd Γ = wfSub? _ _ >>= λ a → wfSub? _ _ >>= λ b → just (a , b)

private
  okG3 : Tree → Bool
  okG3 t = is-just (g3? right (ctxOf t)) ∧ is-just (g3? left (ctxOf t))
  allG3 : T (all okG3 (trees≤ 3))
  allG3 = tt

G3-≤3 : ∀ {t} → t ∈ trees≤ 3 → G3 right (ctxOf t) × G3 left (ctxOf t)
G3-≤3 {t} m =
  let h = all-∈ okG3 (trees≤ 3) allG3 m in
  cert (g3? right (ctxOf t)) (∧-fst h) , cert (g3? left (ctxOf t)) (∧-snd {is-just (g3? right (ctxOf t))} h)

