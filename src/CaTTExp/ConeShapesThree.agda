module CaTTExp.ConeShapesThree where

-- Three cones over 3-dimensional coherence boundaries (ledger B19, C1c):
-- each shape ends in a 4-cell θ whose two faces are parallel 3-terms.
-- The unitor and vertical-composite shapes are closed by Generated/RCConeThree;
-- the horizontal composite still has an open rank-3 query (rc-generator.md §6).

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)
open import CaTTExp.Cones
open import CaTTExp.ConesExamples

T2 : ExTy
T2 = hom (hom ob (v 0) (v 1)) (v 2) (v 3)

Unit3 : ExCtx
Unit3 = DiskEx 3 ++ (hom (diskTy 3) (v 6) (bn 2 (v 6) (idn (v 5))) ∷ [])

VComp3 : ExCtx
VComp3 = DiskEx 2 ++ (T2 ∷ T2 ∷ hom T2 (v 4) (v 5) ∷ hom T2 (v 5) (v 6) ∷ hom T2 (v 4) (v 6)
       ∷ hom (hom T2 (v 4) (v 6)) (bn 2 (v 7) (v 8)) (v 9) ∷ [])

H2 : ExTy
H2 = hom (hom ob (v 0) (v 7)) (bn 0 (v 2) (v 8)) (bn 0 (v 3) (v 9))

Horiz3 : ExCtx
Horiz3 = DiskEx 3 ++ (ob ∷ hom ob (v 1) (v 7) ∷ hom ob (v 1) (v 7)
       ∷ hom (hom ob (v 1) (v 7)) (v 8) (v 9) ∷ hom (hom ob (v 1) (v 7)) (v 8) (v 9)
       ∷ hom (hom (hom ob (v 1) (v 7)) (v 8) (v 9)) (v 10) (v 11)
       ∷ hom H2 (bn 0 (v 4) (v 10)) (bn 0 (v 5) (v 11))
       ∷ hom (hom H2 (bn 0 (v 4) (v 10)) (bn 0 (v 5) (v 11))) (bn 0 (v 6) (v 12)) (v 13) ∷ [])

threeTerm : List ExCtx
threeTerm = Unit3 ∷ VComp3 ∷ Horiz3 ∷ []

closedThree : List ExCtx
closedThree = Unit3 ∷ VComp3 ∷ []

_ : all ok threeTerm ≡ true
_ = refl
