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

-- Open (rc-generator.md §6): the cone over the horizontal composite of two
-- 3-globes is not yet built with this table. This flips when it closes.
horizOpen : is-just (ConeRC.cone (T.rc orRC rc1) Horiz3) ≡ false
horizOpen = refl
