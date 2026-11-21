module CaTTExp.Generated.RCThreeCones where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)
open import CaTTExp.Cones
open import CaTTExp.ConeRC
open import CaTTExp.ConesExamples
open import CaTTExp.ConeShapesThree
import CaTTExp.Generated.RCConeThree as T

cones : all (λ Γ → okM (ConeRC.cone (T.rc orRC rc1) Γ)) closedThree ≡ true
cones = refl
