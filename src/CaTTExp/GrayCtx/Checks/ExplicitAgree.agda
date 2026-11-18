------------------------------------------------------------------------
-- The explicit disk types TsE (CaTTExp.GrayCtx.NaturalExplicit, proved
-- well typed for every m in CaTTExp.GrayCtx.NaturalAll) are the
-- elaborator's TsF for m ≤ 5, both orientations. So the all-dimension
-- cylinder cylE is the elaborator's cylinder cylN on every globular
-- context of dimension ≤ 5.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Checks.ExplicitAgree where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.CylGen using (Side; right; left)
open import CaTTExp.GrayCtx.Natural
open import CaTTExp.GrayCtx.NaturalWF
open import CaTTExp.GrayCtx.NaturalExplicit
open import CaTTExp.GrayCtx.NaturalAll using (cylE)

TsE≡TsF : ∀ sd j → T (j <ℕ 6) → TsE sd j ≡ TsF sd j
TsE≡TsF right 0 _ = ==Ty-sound _ _ tt
TsE≡TsF right 1 _ = ==Ty-sound _ _ tt
TsE≡TsF right 2 _ = ==Ty-sound _ _ tt
TsE≡TsF right 3 _ = ==Ty-sound _ _ tt
TsE≡TsF right 4 _ = ==Ty-sound _ _ tt
TsE≡TsF right 5 _ = ==Ty-sound _ _ tt
TsE≡TsF left  0 _ = ==Ty-sound _ _ tt
TsE≡TsF left  1 _ = ==Ty-sound _ _ tt
TsE≡TsF left  2 _ = ==Ty-sound _ _ tt
TsE≡TsF left  3 _ = ==Ty-sound _ _ tt
TsE≡TsF left  4 _ = ==Ty-sound _ _ tt
TsE≡TsF left  5 _ = ==Ty-sound _ _ tt

cylE≡cylN : ∀ sd Γ → T (dimCtx Γ <ℕ 6) → cylE sd Γ ≡ cylN sd Γ
cylE≡cylN sd Γ dk =
  trans (mk-ext (len Γ + (len Γ + len Γ))
           (gN-ext (TsE sd) (TsF sd) Γ
              (λ x p → TsE≡TsF sd (dimV Γ x) (≤-<-trans (dimV Γ x) (dimCtx Γ) 6 (dimV-≤ Γ x p) dk))))
        (sym (cylN-TsF sd Γ))
