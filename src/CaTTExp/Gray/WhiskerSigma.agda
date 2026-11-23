------------------------------------------------------------------------
-- The whisker heads of CaTTExp.Derived are suspensions.
--
--   Σ(BK k j) = BK (k+1) j     Σ(wK k j) = wK (k+1) j
--   Σ(LK k j) = LK (k+1) j     Σ(lK k j) = lK (k+1) j
--
-- So for k ≥ 1 every whisker head lives on a single hom (it is ΣΘ for
-- a pasting context Θ), and only k = 0 is a genuine multi-hom head.
-- This is step 2(a) of the two-tier L whiskering interface
-- (notes/surface-conservativity.md §7); the side condition of two-tier
-- L on single-hom heads is step 2(b).
------------------------------------------------------------------------
module CaTTExp.Gray.WhiskerSigma where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Suspension ∅ using (Σctx; Σty; Σtm; Σsub; Σty[])
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.Derived
  using (nB; zK; hTy; BK; wK; ρK; ρsK; ρtK; Sph; Dsk; sphSub; dskSub;
         renS; idS; tL; bLK; LPK; LK; λsK; λtK; lK)

private
  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

------------------------------------------------------------------------
-- Spheres and disks.

Σ-aL : ∀ k → Σty (aL k) ≡ aL (suc k)
Σ-aL zero    = refl
Σ-aL (suc k) rewrite Σ-aL k = refl

Σ-Sph : ∀ n → Σctx (Sph n) ≡ Sph (suc n)
Σ-Sph zero    = refl
Σ-Sph (suc n) rewrite Σ-Sph n | Σ-aL n = refl

Σ-Dsk : ∀ n → Σctx (Dsk n) ≡ Dsk (suc n)
Σ-Dsk n rewrite Σ-Sph n | Σ-aL n = refl

Σ-sphL : ∀ n → Σsub (sphSub (aL n)) ≡ sphSub (aL (suc n))
Σ-sphL zero    = refl
Σ-sphL (suc n) rewrite Σ-sphL n = refl

Σ-renS : ∀ n → Σsub (renS n (λ i → i)) ≡ renS (suc (suc n)) (λ i → i)
Σ-renS zero    = refl
Σ-renS (suc n) rewrite Σ-renS n = refl

Σ-idS : ∀ n → Σsub (idS n) ≡ idS (suc (suc n))
Σ-idS = Σ-renS

------------------------------------------------------------------------
-- Right whisker heads.

Σ-BK : ∀ k j → Σctx (BK k j) ≡ BK (suc k) j
Σ-BK k j rewrite Σ-Dsk (nB k j) | Σ-aL k | +-suc j k = refl

Σ-ρK : ∀ k j v → Σsub (ρK k j v) ≡ ρK (suc k) j (suc (suc v))
Σ-ρK k j v rewrite Σ-sphL (nB k j) | +-suc j k = refl

Σ-ρsK : ∀ k j → Σsub (ρsK k j) ≡ ρsK (suc k) j
Σ-ρsK k j rewrite Σ-ρK k j (dbl (nB k j)) | +-suc j k = refl

Σ-ρtK : ∀ k j → Σsub (ρtK k j) ≡ ρtK (suc k) j
Σ-ρtK k j rewrite Σ-ρK k j (suc (dbl (nB k j))) | +-suc j k = refl

Σ-wK : ∀ k j → Σty (wK k j) ≡ wK (suc k) j
Σ-wK k zero rewrite Σ-aL k = refl
Σ-wK k (suc j)
  rewrite Σty[] (wK k j) (ρsK k j) | Σ-wK k j | Σ-BK k j | Σ-ρsK k j | Σ-ρtK k j = refl

------------------------------------------------------------------------
-- Left whisker heads.

Σ-bLK : ∀ k m → Σty (bLK k m) ≡ bLK (suc k) m
Σ-bLK k zero          = Σ-aL k
Σ-bLK k (suc zero)    rewrite Σ-aL k = refl
Σ-bLK k (suc (suc m)) rewrite Σ-bLK k (suc m) | +-suc m k = refl

mutual
  Σ-LPK : ∀ k j → Σctx (LPK k j) ≡ LPK (suc k) j
  Σ-LPK k zero    rewrite Σ-Dsk (suc k) | Σ-aL k = refl
  Σ-LPK k (suc j) rewrite Σ-LK k j | Σ-bLK k (suc j) = refl

  Σ-LK : ∀ k j → Σctx (LK k j) ≡ LK (suc k) j
  Σ-LK k j rewrite Σ-LPK k j | Σ-bLK k (suc j) = refl

Σ-λsK : ∀ k j → Σsub (λsK k j) ≡ λsK (suc k) j
Σ-λsK k j rewrite Σ-idS (suc (tL k j)) | +-suc j k = refl

Σ-λtK : ∀ k j → Σsub (λtK k j) ≡ λtK (suc k) j
Σ-λtK k j rewrite Σ-idS (tL k j) | +-suc j k = refl

Σ-lK : ∀ k j → Σty (lK k j) ≡ lK (suc k) j
Σ-lK k zero    = Σ-wK k zero
Σ-lK k (suc j)
  rewrite Σty[] (lK k j) (λsK k j) | Σ-lK k j | Σ-LK k j | Σ-λsK k j | Σ-λtK k j = refl
