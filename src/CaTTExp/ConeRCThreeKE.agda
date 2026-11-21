------------------------------------------------------------------------
-- (KE) for the 3-dimensional cones from the RC-oracle route.
--
-- CaTTExp.Generated.RCThreeCones (thread RC) checks that ConeRC, with
-- the certified table RCConeThree over RC(1), builds cones over the
-- 3-dimensional unitor and vertical-composite shapes of
-- CaTTExp.ConeShapesThree that pass the certified checker. This module
-- runs the independent (KE) check on the same cones.
------------------------------------------------------------------------
module CaTTExp.ConeRCThreeKE where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)
open import CaTTExp.Cones
open import CaTTExp.ConeRC
open import CaTTExp.ConeShapesThree using (closedThree)
import CaTTExp.Generated.RCConeThree as T

keRC : RC → ExCtx → Bool
keRC rc Γ with ConeRC.cone rc Γ
... | nothing = false
... | just K  = KE.okConeAll (evCtx K) (length Γ)

_ : all (keRC (T.rc orRC rc1)) closedThree ≡ true
_ = refl
