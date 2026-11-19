------------------------------------------------------------------------
-- Disk images for vertical composition in every dimension (ledger D15),
-- by naturality lifts (GrayCtx.Lift).
--
-- In Δ = D^{n+1} ⊗ (D¹ ∨ D¹) the top cell x : a → b gives five
-- travelling variables, the copies of a (copies 0, 1, 2 and a⊗i, a⊗j);
-- they move to the copies of b, with lifts the copies of x:
-- derivatives x₀, x₁, x₂ and squares x⊗i, x⊗j. The image of x⊗e is
-- the lift of the image of a⊗e, which is a term in the copies of a
-- and the generators below. Starting from the elaborator's images
-- (dimension ≤ 2), this defines an image for every dimension.
--
-- Uncertified: Checks.VCompLift runs the certified checker on the
-- result, compiled (tools/vcomp-check).
------------------------------------------------------------------------
module CaTTExp.GrayCtx.VCompLift where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.CylGen using (Side; right; left)
open import CaTTExp.GrayCtx.Natural using (Disk; dbl; dimV; chi)
open import CaTTExp.GrayCtx.VCompExplicit
open import CaTTExp.GrayCtx.Lift

-- The orientation of the squares, read off TsE sd m (checked for
-- m = 3, 4 by Checks.VCompLift).
orient : Side → Bool
orient right = false
orient left  = true

orVarR : Res Tm → Tm
orVarR (ok t)  = t
orVarR (err _) = var 0

-- In cyl2E sd (Disk (suc n)) (N = 2n+3 levels per block): the source
-- a of the top cell at level 2n, its target b at 2n+1, the top cell x
-- at 2n+2, in each of the five blocks (offsets N·k, k = 0 … 4).
module Step (n : Nat) where
  N : Nat
  N = suc (suc (suc (dbl n)))

  travels : Nat → Bool
  travels i = (i ==ℕ dbl n) ∨ (i ==ℕ N + dbl n) ∨ (i ==ℕ N + (N + dbl n))
            ∨ (i ==ℕ N + (N + (N + dbl n))) ∨ (i ==ℕ N + (N + (N + (N + dbl n))))

  env : Side → Env
  env sd = mkEnv (cyl2E sd (Disk (suc n))) travels
                 (λ i → if travels i then suc i else i)
                 (λ i → if travels i then just (var (suc (suc i))) else nothing)

  -- The image of x⊗e from the images below: lift comp(a).
  next : Side → (Nat → Tm) → Tm
  next sd img = orVarR (lift (orient sd) 64 (env sd) (genW img (Disk (suc n)) (dbl n)))

-- The disk images for every dimension: the elaborator's for m ≤ 2,
-- then iterated lifts.
imgs : Side → Nat → Nat → Tm
imgs sd zero    m = imgE sd m
imgs sd (suc k) m =
  if m <ℕ suc (suc (suc k)) then imgs sd k m else Step.next (suc (suc k)) sd (imgs sd k)

-- imgN sd m: the image for the m-disk (imgs is stable from k = m on).
imgN : Side → Nat → Tm
imgN sd m = imgs sd (m ∸ 2) m

-- compW (imgs sd k), written out (see compE).
genL : Side → Nat → Ctx → Nat → Tm
genL sd k Γ x = rnTm (h5 (len Γ) (suc (dbl (dimV Γ x))) (chi Γ x)) (imgs sd k (dimV Γ x))
  where open import CaTTExp.GrayCtx.Natural using (rnTm)

entL : Side → Nat → Ctx → Nat → Tm
entL sd k Γ i =
  if i <ℕ N then var i
  else (if i <ℕ (N + N) then var (N + i)
  else genL sd k Γ ((i ∸ N) ∸ N))
  where N = len Γ

compL : Side → Nat → Ctx → Sub
compL sd k Γ = mkSub (len Γ + (len Γ + len Γ)) (entL sd k Γ)
