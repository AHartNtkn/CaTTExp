------------------------------------------------------------------------
-- Naturality cylinders in binder syntax, selecting free variables
-- (ledger S26i (2)): the construction of CaTTExp.Naturality.Raw,
-- clause by clause, over the syntax of any signature with binders.
--
-- CaTTExp.Binder.Cyl selects the bound variables of one binder (the
-- form in which INIT states its result types); this version selects
-- free variables of a context, as Raw does, which is the form typing
-- is about (a result type is typed after its telescope is opened).
-- That the two agree after opening is planned, not proved here
-- (ledger S26i (2)).
--
--   t⁻ = t [ mm ],  t⁺ = t [ mp ],
--   cyl D (var x)     = th D x,
--   cyl D (coh Q B γ) = K Q B Y' [ γ↑ ]   (Q, B pure; K embedded),
--
-- and constants and binder terms, never touched where the cylinder is
-- used (CaTTExp.Binder.CylOK), have the junk cylinder. The whiskers
-- and iterated boundaries are Binder.Cyl's.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Pure as P
open import CaTTExp.Naturality.Raw using (Sel; ◇; _◂_; Filler; anyL; lenSel; selAt; cnt)

module CaTTExp.Binder.VCyl (𝕊 : Signature) (KF : Filler) where

open Signature 𝕊
open import CaTTExp.Binder.Cyl 𝕊 KF public
  using (Datum; datum; mm; mp; sel; th; sphSub; dskSub; σR; rwT; hL; σLp; σL; lwT;
         rwI; lwI; liftOne; junk; fillK; baseAt; tgtAt; srcAt)

------------------------------------------------------------------------
-- The construction.

touched : Datum → Tm → Bool
touched D t = anyL (sel D) (fvTm t)

mask : Datum → Sub → Sel
mask D ⟨⟩       = ◇
mask D (γ ,ₛ t) = mask D γ ◂ touched D t

mutual
  cyl : Datum → Tm → Tm
  cyl D (var x)       = th D x
  cyl D (bvar _ _)    = junk
  cyl D (coh Q B γ)   = fillK Q B (mask D γ) [ liftS D γ ]tm
  cyl D (cst _)       = junk
  cyl D (bnd _ _ _ _) = junk

  liftS : Datum → Sub → Sub
  liftS D ⟨⟩       = ⟨⟩
  liftS D (γ ,ₛ t) = liftOne (liftS D γ) (t [ mm D ]tm) (t [ mp D ]tm) (cyl D t) (touched D t)

module _ (D : Datum) where
  mutual
    P : Nat → Tm → Ty → Tm
    P zero    t A = t [ mm D ]tm
    P (suc k) t A =
      rwI k (dim A) (P k t A) (TP k A) (L k (tgtAt k A) (baseAt k A))
          (cyl D (tgtAt k A)) (touched D (tgtAt k A))

    TP : Nat → Ty → Ty
    TP zero    A           = A [ mm D ]ty
    TP (suc k) ⋆           = ⋆
    TP (suc k) (arr A s u) =
      if k ==ℕ dim A
      then arr (TP k A) (P k s A) (L k u A)
      else arr (TP (suc k) A) (P (suc k) s A) (P (suc k) u A)

    L : Nat → Tm → Ty → Tm
    L zero    t A = t [ mp D ]tm
    L (suc k) t A =
      lwI k (dim A) (cyl D (srcAt k A)) (P k (srcAt k A) (baseAt k A))
          (L k t A) (TL k A) (touched D (srcAt k A))

    TL : Nat → Ty → Ty
    TL zero    A           = A [ mp D ]ty
    TL (suc k) ⋆           = ⋆
    TL (suc k) (arr A s u) =
      if k ==ℕ dim A
      then arr (TP k A) (P k s A) (L k u A)
      else arr (TL (suc k) A) (L (suc k) s A) (L (suc k) u A)

  aT bT : Tm → Ty → Tm
  aT t A = P (dim A) t A
  bT t A = L (dim A) t A

  cylTy : Tm → Ty → Ty
  cylTy t A = arr (TP (dim A) A) (aT t A) (bT t A)
