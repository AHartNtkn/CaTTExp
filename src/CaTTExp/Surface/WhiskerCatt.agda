------------------------------------------------------------------------
-- The plain-CaTT instance of CaTTExp.Surface.WhiskerWith (and of
-- CaTTExp.DerivedWith): its side-condition hypotheses are discharged
-- by CaTTExp.Derived's sideK and sideLK. This checks that the
-- side-generic development's hypotheses are dischargeable for plain
-- CaTT, where it is the same construction as WhiskerPure (no equation
-- between the two is checked); the two-tier L instance additionally needs graySide
-- on the same heads for every k, j.
------------------------------------------------------------------------
module CaTTExp.Surface.WhiskerCatt where

open import CaTTExp.Prelude
open import CaTTExp.Pure using (∅; cattSide)
import CaTTExp.Derived as D
import CaTTExp.Surface.WhiskerWith as WW

open WW cattSide D.closed (λ k → D.sideK k 0) (λ k j → D.sideK k (suc j)) (λ k j → D.sideLK k (suc j)) public
