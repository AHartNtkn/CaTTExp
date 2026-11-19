------------------------------------------------------------------------
-- D15: the disk hypothesis of VCompAll.compW-wf for the lifted disk
-- images (GrayCtx.VCompLift), as Boolean runs of the certified checker.
--
-- `diskOK sd m` runs Check (checkCtx, inferTm, castTy) on
--   cyl2E sd (Disk m) ⊢ imgN sd m : TsE sd m [ compL sd (m ∸ 2) (Disk m) ]
-- and `diskOK? sd m ≡ just (…)` would be the certificate (Checks.Base.cert).
--
-- For m = 3 the image is a term of about 110 MB (unshared), and Agda's
-- type checker does not finish evaluating the checker on it (killed
-- after 30 min). These functions are therefore *run compiled*
-- (tools/vcomp-check: MAlonzo + GHC), where they return true for both
-- sides in a few seconds. That is a computation with the certified
-- checker, not an Agda-checked certificate; see notes/gray-cylinders.md
-- §3b.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Checks.VCompLift where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.CylGen using (Side; right; left)
open import CaTTExp.GrayCtx.Natural using (Disk)
open import CaTTExp.GrayCtx.NaturalExplicit using (TsE)
open import CaTTExp.GrayCtx.VCompExplicit
open import CaTTExp.GrayCtx.VCompLift

isJust : ∀ {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing  = false

DiskCertL : Side → Nat → Set
DiskCertL sd m = (cyl2E sd (Disk m) ⊢ctx)
               × (cyl2E sd (Disk m) ⊢tm imgN sd m ∶ (TsE sd m [ compL sd (m ∸ 2) (Disk m) ]ty))

diskOK? : ∀ sd m → Maybe (DiskCertL sd m)
diskOK? sd m =
  checkCtx Γ >>= λ w → inferTm Γ w (imgN sd m) >>= λ { (B , d) →
  castTy B (TsE sd m [ compL sd (m ∸ 2) (Disk m) ]ty) d >>= λ e → just (w , e) }
  where Γ = cyl2E sd (Disk m)

diskOK : Side → Nat → Bool
diskOK sd m = isJust (diskOK? sd m)

-- A cheaper test: the raw type of the image is the required type
-- (no derivation; Elab.tyOf).
open import CaTTExp.GrayCtx.Elab using (tyOf)

typeOK : Side → Nat → Bool
typeOK sd m with tyOf (cyl2E sd (Disk m)) (imgN sd m)
... | just B  = B ==Ty (TsE sd m [ compL sd (m ∸ 2) (Disk m) ]ty)
... | nothing = false

------------------------------------------------------------------------
-- Vertical composition for every globular Γ of dimension ≤ 3, given the
-- certificate for D³ (which the compiled run above produces; Agda's
-- type checker does not finish producing it).

open import CaTTExp.GrayCtx.Natural using (globular)
open import CaTTExp.GrayCtx.NaturalAll using (cylE)
open import CaTTExp.GrayCtx.VCompAll using (DiskCertW; compW-wf)
open import CaTTExp.GrayCtx.Checks.VCompAll using (d0f; d1f; d2f)
open import CaTTExp.GrayCtx.NaturalWF using (≡-T; <suc-≢)

private
  c0 : ∀ sd → DiskCertW sd (imgs sd 1) 0
  c0 sd = d0f sd
  c1 : ∀ sd → DiskCertW sd (imgs sd 1) 1
  c1 sd = d1f sd
  c2 : ∀ sd → DiskCertW sd (imgs sd 1) 2
  c2 sd = d2f sd

  lt0 : ∀ j → T (j <ℕ 0) → ⊥
  lt0 zero    ()
  lt0 (suc j) ()

  pick4 : ∀ sd → DiskCertW sd (imgs sd 1) 3 → ∀ j → T (j <ℕ 4) →
          ∀ b3 → (j ==ℕ 3) ≡ b3 → ∀ b2 → (j ==ℕ 2) ≡ b2 → ∀ b1 → (j ==ℕ 1) ≡ b1 →
          ∀ b0 → (j ==ℕ 0) ≡ b0 → DiskCertW sd (imgs sd 1) j
  pick4 sd h j p true e3 _ e2 _ e1 _ e0 =
    subst (DiskCertW sd (imgs sd 1)) (sym (==ℕ-sound j 3 (≡-T e3))) h
  pick4 sd h j p false e3 true e2 _ e1 _ e0 =
    subst (DiskCertW sd (imgs sd 1)) (sym (==ℕ-sound j 2 (≡-T e2))) (c2 sd)
  pick4 sd h j p false e3 false e2 true e1 _ e0 =
    subst (DiskCertW sd (imgs sd 1)) (sym (==ℕ-sound j 1 (≡-T e1))) (c1 sd)
  pick4 sd h j p false e3 false e2 false e1 true e0 =
    subst (DiskCertW sd (imgs sd 1)) (sym (==ℕ-sound j 0 (≡-T e0))) (c0 sd)
  pick4 sd h j p false e3 false e2 false e1 false e0 =
    ⊥-elim (lt0 j (<suc-≢ j 0 (<suc-≢ j 1 (<suc-≢ j 2 (<suc-≢ j 3 p e3) e2) e1) e0))

vcomp3-wf : ∀ sd → DiskCertW sd (imgs sd 1) 3 →
            ∀ Γ → Γ ⊢ctx → T (globular Γ) → T (dimCtx Γ <ℕ 4) →
            (cyl2E sd Γ ⊢ctx) × (cyl2E sd Γ ⊢sub compW (imgs sd 1) Γ ∶ cylE sd Γ)
vcomp3-wf sd h = compW-wf sd (imgs sd 1) 3 (λ j p → pick4 sd h j p _ refl _ refl _ refl _ refl)
