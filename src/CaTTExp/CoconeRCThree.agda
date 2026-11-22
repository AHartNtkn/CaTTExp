------------------------------------------------------------------------
-- Cocones over the closed 3-dimensional shapes (the 3-dimensional
-- unitor and vertical composite of CaTTExp.ConeShapesThree), built by
-- CoconeRC (the cone construction on the O_odd dual, ConeRC) with the
-- certified table RCCoconeThree layered over RC(1). Every cocone
-- context is run through the certified checker (okM).
------------------------------------------------------------------------
module CaTTExp.CoconeRCThree where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)
open import CaTTExp.Cones
open import CaTTExp.ConeRC
open import CaTTExp.ConesExamples using (okM)
open import CaTTExp.ConeShapesThree using (closedThree)
import CaTTExp.Generated.RCCoconeThree as C

cocones : all (λ Γ → okM (CoconeRC.cocone (C.rc orRC rc1) Γ)) closedThree ≡ true
cocones = refl
