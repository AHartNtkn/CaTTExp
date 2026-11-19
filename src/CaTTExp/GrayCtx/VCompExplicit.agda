------------------------------------------------------------------------
-- Vertical composition of lax transformations, reduced to the disks
-- (ledger D13, remaining part).
--
-- * cyl2E sd Γ: Γ ⊗ (D¹ ∨ D¹) (resp. (D¹ ∨ D¹) ⊗ Γ) for globular Γ,
--   built levelwise from the explicit disk types TsE, like cylE:
--   copies 0, 1, 2, then the edge blocks i and j; the generator x⊗i
--   (x⊗j) has the type TsE m renamed along χ_x ⊗ D¹ into copies 0, 1
--   and block i (copies 1, 2 and block j).
-- * imgE sd m: the image of the top generator of D^m ⊗ D¹ under the
--   elaborator's vertical composition (VComp.Comp.compGen), computed
--   once per disk (m ≤ 2).
-- * compE sd Γ: copy 0 ↦ copy 0, copy 1 ↦ copy 2, and x⊗e ↦ imgE (dim x)
--   renamed along χ_x ⊗ (D¹ ∨ D¹).
------------------------------------------------------------------------
module CaTTExp.GrayCtx.VCompExplicit where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.CylGen using (Side; right; left)
open import CaTTExp.GrayCtx.Natural
open import CaTTExp.GrayCtx.NaturalExplicit using (TsE)
open import CaTTExp.GrayCtx.VComp using (module Comp)

------------------------------------------------------------------------
-- Level maps. A cylinder over a disk D^m has blocks of M = 2m+1 levels.

-- Five blocks (Δ ⊗ (D¹ ∨ D¹)), block k sent to offset k·N.
h5 : Nat → Nat → (Nat → Nat) → Nat → Nat
h5 N M χ j =
  if j <ℕ M then χ j
  else (if j <ℕ (M + M) then N + χ (j ∸ M)
  else (if j <ℕ (M + (M + M)) then N + (N + χ ((j ∸ M) ∸ M))
  else (if j <ℕ (M + (M + (M + M))) then N + (N + (N + χ (((j ∸ M) ∸ M) ∸ M)))
  else (N + (N + (N + (N + χ ((((j ∸ M) ∸ M) ∸ M) ∸ M))))))))

------------------------------------------------------------------------
-- Γ ⊗ (D¹ ∨ D¹).

-- The two inclusions Δ ⊗ D¹ → Δ ⊗ (D¹ ∨ D¹) (N = len Δ): ιI onto copies
-- 0, 1 and block i, ιJ onto copies 1, 2 and block j.
ιI ιJ : Nat → Nat → Nat
ιI N j = if j <ℕ (N + N) then j else (N + j)
ιJ N j = if j <ℕ (N + N) then N + j else (N + (N + j))

-- Every level of Γ ⊗ (D¹ ∨ D¹) is the image of a level of Γ ⊗ D¹
-- under ιI or ιJ, with the renamed type.
g2 : (Nat → Ty) → Ctx → Nat → Ty
g2 Ts Γ i =
  if i <ℕ (N + N) then rnTy (ιI N) (gN Ts Γ i)
  else (if i <ℕ (N + (N + N)) then rnTy (ιJ N) (gN Ts Γ (i ∸ N))
  else (if i <ℕ (N + (N + (N + N))) then rnTy (ιI N) (gN Ts Γ (i ∸ N))
  else rnTy (ιJ N) (gN Ts Γ ((i ∸ N) ∸ N))))
  where N = len Γ

cyl2With : (Nat → Ty) → Ctx → Ctx
cyl2With Ts Γ = mkCtx (len Γ + (len Γ + (len Γ + (len Γ + len Γ)))) (g2 Ts Γ)

cyl2E : Side → Ctx → Ctx
cyl2E sd = cyl2With (TsE sd)

------------------------------------------------------------------------
-- The disk images.

orVar : Maybe Tm → Tm
orVar (just t) = t
orVar nothing  = var 0

imgE : Side → Nat → Tm
imgE sd m = orVar (Comp.compGen sd (Disk m) (cyl2E sd (Disk m)) (dbl m))

------------------------------------------------------------------------
-- Vertical composition for globular Γ.

-- Substitutions given entrywise.
mkSub : Nat → (Nat → Tm) → Sub
mkSub zero    e = ⟨⟩
mkSub (suc n) e = mkSub n e ,ₛ e n

-- Over an arbitrary image of the disk generators (the proofs in
-- VCompAll are about this generic form, so that they never unfold the
-- elaborator).
genW : (Nat → Tm) → Ctx → Nat → Tm
genW img Γ x = rnTm (h5 (len Γ) (suc (dbl (dimV Γ x))) (chi Γ x)) (img (dimV Γ x))

-- copy 0 ↦ copy 0, copy 1 ↦ copy 2, x ⊗ e ↦ genW x.
entW : (Nat → Tm) → Ctx → Nat → Tm
entW img Γ i =
  if i <ℕ N then var i
  else (if i <ℕ (N + N) then var (N + i)
  else genW img Γ ((i ∸ N) ∸ N))
  where N = len Γ

compW : (Nat → Tm) → Ctx → Sub
compW img Γ = mkSub (len Γ + (len Γ + len Γ)) (entW img Γ)

-- The instance, written out (not as genW (imgE sd) etc.: the two are
-- definitionally equal, but Agda evaluates the direct form much faster
-- when the checker runs on it).
genE : Side → Ctx → Nat → Tm
genE sd Γ x = rnTm (h5 (len Γ) (suc (dbl (dimV Γ x))) (chi Γ x)) (imgE sd (dimV Γ x))

entE : Side → Ctx → Nat → Tm
entE sd Γ i =
  if i <ℕ N then var i
  else (if i <ℕ (N + N) then var (N + i)
  else genE sd Γ ((i ∸ N) ∸ N))
  where N = len Γ

compE : Side → Ctx → Sub
compE sd Γ = mkSub (len Γ + (len Γ + len Γ)) (entE sd Γ)
