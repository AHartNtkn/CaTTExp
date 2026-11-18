module CaTTExp.GrayCtx.Checks.VComp where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Cylinder
open import CaTTExp.GrayCtx.Checks.Base
open import CaTTExp.GrayCtx.VComp
open import CaTTExp.GrayCtx.Cube using (fromJust)

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

-- All pasting schemes of dimension ≤ 2 with at most 3 edges.
private
  depth : Tree → Nat
  depth t = go 4 t
    where
    go : Nat → Tree → Nat
    go zero    _         = 0
    go (suc f) (node ts) = goL f ts
      where
      goL : Nat → List Tree → Nat
      goL f []       = 0
      goL f (t ∷ ts) = max (suc (go f t)) (goL f ts)

  dim≤2 : List Tree
  dim≤2 = filter (λ t → depth t <ℕ 3) (trees≤ 3)

  okVC : Tree → Bool
  okVC t = is-just (wfSub? (compSub right (ctxOf t)) (fromJust (cyl right 1 (ctxOf t))))
         ∧ is-just (wfSub? (compSub left (ctxOf t)) (fromJust (cyl left 1 (ctxOf t))))
  allVC : T (all okVC dim≤2)
  allVC = tt

_ : length dim≤2 ≡ 8
_ = refl

comp-≤3 : ∀ {t} → t ∈ dim≤2 → VC right (ctxOf t) × VC left (ctxOf t)
comp-≤3 {t} m =
  let h = all-∈ okVC dim≤2 allVC m in
  cert (wfSub? _ _) (∧-fst h) , cert (wfSub? _ _) (∧-snd {is-just (wfSub? (compSub right (ctxOf t)) (fromJust (cyl right 1 (ctxOf t))))} h)

