module CaTTExp.GrayCtx.Checks.G3 where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Cylinder
open import CaTTExp.GrayCtx.Checks.Base
open import CaTTExp.GrayCtx.VComp
open import Agda.Builtin.Nat using (_*_)

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


------------------------------------------------------------------------
-- Cover and meet. Γ ⊗ (D¹ ∨ D¹) has 5N variables (three copies of Γ,
-- two edge blocks), and the images of ι₁, ι₂ cover all of them and meet
-- exactly in copy 1 (levels N … 2N−1). The images depend only on N, so
-- this is checked for every N ≤ 12; the length 5N is checked on the
-- same trees as G3-≤3.

private
  inMid : Nat → Nat → Bool
  inMid N x = not (x <ℕ N) ∧ (x <ℕ (2 * N))
  coverMeet : Nat → Bool
  coverMeet N = all (λ x → let a = elem x (fvSub (ι₁ N)) ; b = elem x (fvSub (ι₂ N)) in
                           (a ∨ b) ∧ (if a ∧ b then inMid N x else not (inMid N x)))
                    (upto (5 * N))
              ∧ all (λ x → x <ℕ (5 * N)) (fvSub (ι₁ N) ++ fvSub (ι₂ N))
  len5 : Nat → Maybe Ctx → Bool
  len5 N (just Δ) = len Δ ==ℕ 5 * N
  len5 N nothing  = false

G3-cover-meet : T (all coverMeet (upto 13))
G3-cover-meet = tt

G3-length : T (all (λ t → len5 (len (ctxOf t)) (cyl right 2 (ctxOf t))
                       ∧ len5 (len (ctxOf t)) (cyl left 2 (ctxOf t)))
                   (trees≤ 3))
G3-length = tt
