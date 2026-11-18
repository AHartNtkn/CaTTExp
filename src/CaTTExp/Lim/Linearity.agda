------------------------------------------------------------------------
-- Open issue D3b: Mikhail's linearity test (Def. 3.1) does not enforce
-- multiplicity one, and the strict test that repairs it.
--
--  L1  For a loop ℓ : x → x, the printed test accepts ℓ ∝ (ℓ·ℓ)·ℓ: in
--      the OP case only the number of *linear* arguments is counted,
--      and only the right argument is linear in ℓ. The strict test
--      (Conditions.linear₁) rejects it.
--  L2  Consequently the printed cone rule (KE) accepts the projection
--      p_ℓ : p_x ⇒ (p_x · (ℓ·ℓ)) · ℓ over the loop. The cone rule with
--      strict linearity rejects it.
--  L3  Strict linearity alone does not remove all non-canonical cones:
--      the D5 cone (whose extra use of r is in the *source*, which has
--      no linearity condition) is still accepted. So the specified
--      construction (Repaired.agda) is still needed.
--  L4  All the intended examples still pass with strict linearity
--      (cones, Example 4.1, and the cone morphisms).
------------------------------------------------------------------------
module CaTTExp.Lim.Linearity where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)
open import CaTTExp.Lim.Named
open import CaTTExp.Lim.Conditions
open import CaTTExp.Lim.Rules
open import CaTTExp.Lim.Terms
open import CaTTExp.Lim.Defects
open import CaTTExp.Lim.Repaired using (Γ41; coneC; coneQ; morC; Shape; Γpair)

private
  v : Nat → Tm
  v = var

  _⇒⋆_ : Nat → Nat → Ty
  a ⇒⋆ b = arr ⋆ (v a) (v b)

------------------------------------------------------------------------
-- L1.   x0  ℓ1 : x → x

Kℓ : NCtx
Kℓ = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ (0 ⇒⋆ 0)

ℓℓ ℓℓ-ℓ : Tm
ℓℓ   = comp (v 0) (v 0) (v 1) (v 0) (v 1)
ℓℓ-ℓ = comp (v 0) (v 0) ℓℓ (v 0) (v 1)

L1-printed : linear Kℓ 1 ℓℓ-ℓ ≡ true
L1-printed = refl

L1-strict : linear₁ Kℓ 1 ℓℓ-ℓ ≡ false
L1-strict = refl

-- Sanity: a single use is linear under both tests.
_ : linear₁ Kℓ 1 (v 1) ≡ true
_ = refl

------------------------------------------------------------------------
-- L2.   x0 ℓ1 | c2 | p_x3 p_ℓ4

Πℓ : NCtx
Πℓ = ∅ ▹ 3 ∶ (2 ⇒⋆ 0)
       ▹ 4 ∶ arr (2 ⇒⋆ 0) (v 3)
                 (comp (v 2) (v 0) (comp (v 2) (v 0) (v 3) (v 0) ℓℓ) (v 0) (v 1))

L2-printed : Cone Kℓ 2 Πℓ
L2-printed = from-just (cone? Kℓ 2 Πℓ)

private
  module S = ConeBy strictLin

L2-strict : S.Cone Kℓ 2 Πℓ → ⊥
L2-strict (S.KE _ _ _ ())

-- The canonical cone over the loop passes the strict rule.
_ : S.Cone Kℓ 2 (from-just (coneC Kℓ 2))
_ = from-just (S.cone? _ _ _)

------------------------------------------------------------------------
-- L3. The D5 non-canonical cone survives strict linearity.

L3 : S.Cone Γloop 3 Πnoncanonical
L3 = from-just (S.cone? Γloop 3 Πnoncanonical)

------------------------------------------------------------------------
-- L4. The intended examples with all three repairs.

_ : S.Cone Γarr 3 Parr
_ = from-just (S.cone? _ _ _)

_ : S.Cone Γloop 3 Πcanonical
_ = from-just (S.cone? _ _ _)

_ : S.Cone Γ41 5 (from-just (coneC Γ41 5))
_ = from-just (S.cone? _ _ _)

open Ctrf
open CtrfCheck
open Gray
open GrayCheck

_ : Ctrf1 fixedStrict Γarr 3 Parr Qarr Marr
_ = from-just (ctrf? fixedStrict _ _ _ _ _)

_ : Ctrf1 fixedStrict Γpair 5 (from-just (coneC Γpair 5)) (from-just (coneQ Γpair 5))
                              (Shape.M3 (from-just (morC Γpair 5)))
_ = from-just (ctrf? fixedStrict _ _ _ _ _)

_ : Gray1 fixedStrict G₁ G₂ ex41
_ = from-just (gray? fixedStrict _ _ _)
