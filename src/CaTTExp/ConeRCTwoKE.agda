------------------------------------------------------------------------
-- The 2-dimensional cones from the RC-oracle route also satisfy (KE).
--
-- CaTTExp.Generated.RCTwoCones (thread RC) checks that the cones over
-- the eight 2-dimensional shapes of ConesExamples §11, built by
-- CaTTExp.ConeRC with the certified table RCConeTwo plus RC(1), pass
-- the certified checker. This module runs the independent (KE) check
-- (KE.okConeAll) on the same cones. Slow (several minutes), so it is
-- kept apart from ConeRCExamples.
------------------------------------------------------------------------
module CaTTExp.ConeRCTwoKE where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)
open import CaTTExp.Cones
open import CaTTExp.ConeRC
open import CaTTExp.ConesExamples using (module TermCones2)
import CaTTExp.Generated.RCConeTwo as T

keRC : RC → ExCtx → Bool
keRC rc Γ with ConeRC.cone rc Γ
... | nothing = false
... | just K  = KE.okConeAll (evCtx K) (length Γ)

_ : all (keRC (T.rc orRC rc1)) TermCones2.twoTerm ≡ true
_ = refl
