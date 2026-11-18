------------------------------------------------------------------------
-- D13: Γ ⊗ D¹ and D¹ ⊗ Γ are well formed for every well-formed
-- globular context Γ of dimension ≤ 5.
--
-- The general theorem (CaTTExp.GrayCtx.NaturalWF.cylN-wf) reduces this
-- to the disks D⁰ … D⁵, which are certified here by the checker. The
-- disk-by-disk construction cylN agrees syntactically with `cyl sd 1`
-- (the elaborator run on Γ itself) on every globular context tested.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Checks.Natural where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Cylinder
open import CaTTExp.GrayCtx.Natural
open import CaTTExp.GrayCtx.NaturalWF
open import CaTTExp.GrayCtx.Checks.Base using (cert; WF)

------------------------------------------------------------------------
-- The disks, certified.

private
  Ts5 : Side → Nat → Ty
  Ts5 sd = nth (diskTys sd 5)

  inv▸ : ∀ {Γ A} → (Γ ▸ A) ⊢ctx → Γ ⊢ty A
  inv▸ (▸-wf _ a) = a

  disk? : (sd : Side) (j : Nat) → Maybe ((diskPre (Ts5 sd) j ▸ Ts5 sd j) ⊢ctx)
  disk? sd j = checkCtx (diskPre (Ts5 sd) j ▸ Ts5 sd j)

  dr0 : diskPre (Ts5 right) 0 ⊢ty Ts5 right 0
  dr0 = inv▸ (cert (disk? right 0) tt)
  dr1 : diskPre (Ts5 right) 1 ⊢ty Ts5 right 1
  dr1 = inv▸ (cert (disk? right 1) tt)
  dr2 : diskPre (Ts5 right) 2 ⊢ty Ts5 right 2
  dr2 = inv▸ (cert (disk? right 2) tt)
  dr3 : diskPre (Ts5 right) 3 ⊢ty Ts5 right 3
  dr3 = inv▸ (cert (disk? right 3) tt)
  dr4 : diskPre (Ts5 right) 4 ⊢ty Ts5 right 4
  dr4 = inv▸ (cert (disk? right 4) tt)
  dr5 : diskPre (Ts5 right) 5 ⊢ty Ts5 right 5
  dr5 = inv▸ (cert (disk? right 5) tt)
  dl0 : diskPre (Ts5 left) 0 ⊢ty Ts5 left 0
  dl0 = inv▸ (cert (disk? left 0) tt)
  dl1 : diskPre (Ts5 left) 1 ⊢ty Ts5 left 1
  dl1 = inv▸ (cert (disk? left 1) tt)
  dl2 : diskPre (Ts5 left) 2 ⊢ty Ts5 left 2
  dl2 = inv▸ (cert (disk? left 2) tt)
  dl3 : diskPre (Ts5 left) 3 ⊢ty Ts5 left 3
  dl3 = inv▸ (cert (disk? left 3) tt)
  dl4 : diskPre (Ts5 left) 4 ⊢ty Ts5 left 4
  dl4 = inv▸ (cert (disk? left 4) tt)
  dl5 : diskPre (Ts5 left) 5 ⊢ty Ts5 left 5
  dl5 = inv▸ (cert (disk? left 5) tt)

  -- Dispatch on j without matching numerals against the certified
  -- types: matching makes Agda normalise them, which exhausts the heap.
  below6 : (P : Nat → Set) → P 0 → P 1 → P 2 → P 3 → P 4 → P 5 → ∀ j → T (j <ℕ 6) → P j
  below6 P a b c d e f zero                                _ = a
  below6 P a b c d e f (suc zero)                          _ = b
  below6 P a b c d e f (suc (suc zero))                    _ = c
  below6 P a b c d e f (suc (suc (suc zero)))              _ = d
  below6 P a b c d e f (suc (suc (suc (suc zero))))        _ = e
  below6 P a b c d e f (suc (suc (suc (suc (suc zero))))) _ = f

  DP : Side → Nat → Set
  DP sd j = diskPre (Ts5 sd) j ⊢ty Ts5 sd j

  disk5 : ∀ sd j → T (j <ℕ 6) → DP sd j
  disk5 right = below6 (DP right) dr0 dr1 dr2 dr3 dr4 dr5
  disk5 left  = below6 (DP left)  dl0 dl1 dl2 dl3 dl4 dl5

-- The top generator of D^j ⊗ D¹ is well typed, j ≤ 5, both orientations.
disks : ∀ sd j → T (j <ℕ 6) → diskPre (TsF sd) j ⊢ty TsF sd j
disks sd j p =
  subst (_⊢ty TsF sd j) (diskPre-TsF sd (Ts5 sd) 5 (nth-diskTys sd 5) j p)
    (subst (diskPre (Ts5 sd) j ⊢ty_) (nth-diskTys sd 5 j p) (disk5 sd j p))

------------------------------------------------------------------------
-- The theorem.

cylN-wf≤5 : ∀ sd Γ → Γ ⊢ctx → T (globular Γ) → T (dimCtx Γ <ℕ 6) → cylN sd Γ ⊢ctx
cylN-wf≤5 sd = cylN-wf sd 5 (disks sd)

-- For globular Γ, `cyl sd 1 Γ` is cylN.
cyl-cylN : ∀ sd Γ → T (globular Γ) → cyl sd 1 Γ ≡ just (cylN sd Γ)
cyl-cylN sd Γ g rewrite T-≡ g = refl

-- D13 up to dimension 5: Γ ⊗ D¹ and D¹ ⊗ Γ are well formed for every
-- well-formed globular Γ (in particular every pasting scheme) of
-- dimension ≤ 5. All dimensions: `cylN-wf-all`, given every disk.
cyl-wf : ∀ sd Γ → Γ ⊢ctx → T (globular Γ) → T (dimCtx Γ <ℕ 6) → WF (cyl sd 1 Γ)
cyl-wf sd Γ w g d = cylN sd Γ , cyl-cylN sd Γ g , cylN-wf≤5 sd Γ w g d

