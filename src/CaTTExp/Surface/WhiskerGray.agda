------------------------------------------------------------------------
-- The two-tier L instance of CaTTExp.Surface.WhiskerWith (and of
-- CaTTExp.DerivedWith): graySide accepts Derived's whisker heads for
-- every k and j, so the derived whiskers are well typed in two-tier L.
--
--   k ≥ 1: CaTTExp.Gray.WhiskerSide (the heads live on one hom);
--   k = 0: CaTTExp.Gray.WhiskerZeroSide (right whiskers) and
--          CaTTExp.Gray.WhiskerZeroLeftSide (left whiskers).
--
-- This is the typing half (Wh-wf) of the whiskering interface of
-- Surface.TheoremB for two-tier L; Wh-≈ is a separate hypothesis
-- there, as for plain CaTT.
------------------------------------------------------------------------
module CaTTExp.Surface.WhiskerGray where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
import CaTTExp.Derived as D
open D using (BK; wK; zK; LK; lK; ρsK; ρtK; λsK; λtK)
import CaTTExp.Subst as SubstM
import CaTTExp.Gray.WhiskerSide as WS
import CaTTExp.Gray.WhiskerZeroSide as WZ
import CaTTExp.Gray.WhiskerZeroLeftSide as WL
import CaTTExp.Surface.WhiskerWith as WW

private
  closedL : SubstM.Closed ∅ graySide
  closedL ()

gside-BK0 : ∀ k → T (graySide (BK k 0) (aL k) (var (dbl k)) (var (zK k 0)))
gside-BK0 zero    = WZ.gside-BK0-0
gside-BK0 (suc k) = WS.gside-BK0 k

gside-BK : ∀ k j → T (graySide (BK k (suc j)) (wK k j [ ρsK k j ]ty)
                      (coh (BK k j) (wK k j) (ρsK k j)) (coh (BK k j) (wK k j) (ρtK k j)))
gside-BK zero    j = WZ.gside-BK-0 j
gside-BK (suc k) j = WS.gside-BK k j

gside-LK : ∀ k j → T (graySide (LK k (suc j)) (lK k j [ λsK k j ]ty)
                      (coh (LK k j) (lK k j) (λsK k j)) (coh (LK k j) (lK k j) (λtK k j)))
gside-LK zero    j = WL.gside-LK-0 j
gside-LK (suc k) j = WS.gside-LK k j

open WW graySide closedL gside-BK0 gside-BK gside-LK public
