------------------------------------------------------------------------
-- Two-tier L accepts the coherences in DES's result types, in every
-- dimension: the side hypotheses of the kernel's presupposition for
-- the DES instance (CaTTExp.Binder.DesPresup), at L's side condition
-- on binder syntax (CaTTExp.Gray.DesSide), over pure L.
--
--   side-comp n : graySideD (compPC n) (tyD n) (var 2n) (var (2n+3))
--
-- The composite of two (n+1)-cells along an n-cell is, after erasure,
-- literally CaTTExp.Derived's composite head (BK n 0, wK n 0), which
-- two-tier L accepts for every n (Gray.WhiskerZeroSide for n = 0,
-- Gray.WhiskerSide for n ≥ 1).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Des
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (extend)
import CaTTExp.Gray.Pure as G
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
import CaTTExp.Derived as D
open import CaTTExp.Gray.WhiskerSide using (gside-BK0)
open import CaTTExp.Gray.WhiskerZeroSide using (gside-BK0-0)

module CaTTExp.Gray.DesSideL where

𝕊 : Signature
𝕊 = extend P.∅ (desBinders P.K)

open Signature 𝕊
open DesConstruction K DesF (λ b → b)
open import CaTTExp.Gray.DesSide P.∅ (desBinders P.K) cellArgD using (graySideD; dTy; dCtx)

private
  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

  dbl≡ : ∀ n → n + n ≡ dbl n
  dbl≡ zero    = refl
  dbl≡ (suc n) = cong suc (trans (+-suc n n) (cong suc (dbl≡ n)))

  d-tyD : ∀ n → dTy (tyD n) ≡ just (aL n)
  d-tyD zero = refl
  d-tyD (suc n) rewrite d-tyD n | dbl≡ n = refl

  d-diskD : ∀ n → dCtx (diskD n) ≡ just (D.Dsk n)
  d-diskD zero = refl
  d-diskD (suc n) rewrite d-diskD n | d-tyD n | dbl≡ n = refl

  d-compPC : ∀ n → dCtx (compPC n) ≡ just (D.BK n 0)
  d-compPC n rewrite d-diskD (suc n) | d-tyD n | dbl≡ n = refl

side-comp : ∀ n → T (graySideD (compPC n) (tyD n) (var (n + n)) (var (3 + (n + n))))
side-comp n rewrite d-compPC n | d-tyD n | dbl≡ n = go n
  where
  go : ∀ n → T (G.graySide (D.BK n 0) (aL n) (G.var (dbl n)) (G.var (D.zK n 0)))
  go zero    = gside-BK0-0
  go (suc k) = gside-BK0 k
