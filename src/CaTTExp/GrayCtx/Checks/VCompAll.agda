------------------------------------------------------------------------
-- D13, remaining part: vertical composition for every globular Γ of
-- dimension ≤ 2.
--
-- * The disk hypothesis of VCompAll.compE-wf, certified for D⁰, D¹, D²
--   in both orientations.
-- * The corollary: Γ ⊗ (D¹ ∨ D¹) ⊢ compE : Γ ⊗ D¹ (and the same for
--   D¹ ⊗ Γ) for every well-formed globular Γ of dimension ≤ 2.
-- * Agreement with the elaborator: Checks.VCompAgree.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Checks.VCompAll where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.CylGen using (Side; right; left)
open import CaTTExp.GrayCtx.Natural using (Disk; globular)
open import CaTTExp.GrayCtx.NaturalExplicit using (TsE)
open import CaTTExp.GrayCtx.NaturalAll using (cylE)
open import CaTTExp.GrayCtx.Cylinder using (cyl)
open import CaTTExp.GrayCtx.VComp using (compSub)
open import CaTTExp.GrayCtx.VCompExplicit
open import CaTTExp.GrayCtx.VCompAll
open import CaTTExp.GrayCtx.NaturalWF using (≡-T; <suc-≢)
open import CaTTExp.GrayCtx.Checks.Base using (cert; D; Comp₂; HComp; VComp)

------------------------------------------------------------------------
-- The disks.

-- The certificate, stated with compE (the checker runs much faster on
-- it than on the definitionally equal compW (imgE sd) of DiskCert).
DiskCertE : Side → Nat → Set
DiskCertE sd m = (cyl2E sd (Disk m) ⊢ctx)
               × (cyl2E sd (Disk m) ⊢tm imgE sd m ∶ (TsE sd m [ compE sd (Disk m) ]ty))

diskCert? : ∀ sd m → Maybe (DiskCertE sd m)
diskCert? sd m =
  checkCtx Γ >>= λ w → inferTm Γ w (imgE sd m) >>= λ { (B , d) →
  castTy B (TsE sd m [ compE sd (Disk m) ]ty) d >>= λ e → just (w , e) }
  where Γ = cyl2E sd (Disk m)

toCert : ∀ sd m → DiskCertE sd m → DiskCert sd m
toCert sd m d = d

-- (Standalone and abstract: Agda type-checks this module much faster
-- than when the certificates are computed in the clauses of a
-- pattern-matching definition, or can be unfolded there.)
abstract
  dR0 : DiskCertE right 0
  dR0 = cert (diskCert? right 0) tt
  dR1 : DiskCertE right 1
  dR1 = cert (diskCert? right 1) tt
  dR2 : DiskCertE right 2
  dR2 = cert (diskCert? right 2) tt
  dL0 : DiskCertE left 0
  dL0 = cert (diskCert? left 0) tt
  dL1 : DiskCertE left 1
  dL1 = cert (diskCert? left 1) tt
  dL2 : DiskCertE left 2
  dL2 = cert (diskCert? left 2) tt

d0f : ∀ sd → DiskCertE sd 0
d0f right = dR0
d0f left  = dL0
d1f : ∀ sd → DiskCertE sd 1
d1f right = dR1
d1f left  = dL1
d2f : ∀ sd → DiskCertE sd 2
d2f right = dR2
d2f left  = dL2

private
  lt0 : ∀ j → T (j <ℕ 0) → ⊥
  lt0 zero    ()
  lt0 (suc j) ()

-- (By comparison with literals, without pattern matching on j or a
-- `with` on it: either makes Agda unfold the type DiskCertE sd j,
-- which is slow.)
pick : ∀ sd j → T (j <ℕ 3) → ∀ b2 → (j ==ℕ 2) ≡ b2 → ∀ b1 → (j ==ℕ 1) ≡ b1 →
       ∀ b0 → (j ==ℕ 0) ≡ b0 → DiskCertE sd j
pick sd j p true  e2 _     e1 _     e0 = subst (DiskCertE sd) (sym (==ℕ-sound j 2 (≡-T e2))) (d2f sd)
pick sd j p false e2 true  e1 _     e0 = subst (DiskCertE sd) (sym (==ℕ-sound j 1 (≡-T e1))) (d1f sd)
pick sd j p false e2 false e1 true  e0 = subst (DiskCertE sd) (sym (==ℕ-sound j 0 (≡-T e0))) (d0f sd)
pick sd j p false e2 false e1 false e0 =
  ⊥-elim (lt0 j (<suc-≢ j 0 (<suc-≢ j 1 (<suc-≢ j 2 p e2) e1) e0))

disksE : ∀ sd j → T (j <ℕ 3) → DiskCertE sd j
disksE sd j p = pick sd j p _ refl _ refl _ refl

disks : ∀ sd j → T (j <ℕ 3) → DiskCert sd j
disks sd j p = toCert sd j (disksE sd j p)

------------------------------------------------------------------------
-- Vertical composition for every globular Γ of dimension ≤ 2.

vcomp-wf : ∀ sd Γ → Γ ⊢ctx → T (globular Γ) → T (dimCtx Γ <ℕ 3) →
           (cyl2E sd Γ ⊢ctx) × (cyl2E sd Γ ⊢sub compE sd Γ ∶ cylE sd Γ)
vcomp-wf sd = compE-wf sd 2 (disks sd)

