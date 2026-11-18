module CaTTExp.GrayCtx.Checks.Cube where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Cylinder
open import CaTTExp.GrayCtx.Checks.Base
open import CaTTExp.GrayCtx.Cube

------------------------------------------------------------------------
-- 5. The Gray cube.

cubeR-wf : WF CubeR
cubeR-wf = cert (wf? _) tt

cubeL-wf : WF CubeL
cubeL-wf = cert (wf? _) tt

-- G4 on the nose fails exactly at the cube cell (e,e,e) = (2,2,2):
-- every other generator's type agrees under the renaming.
G4-mismatches : mismatches ≡ ((2 , 2 , 2) ∷ [])
G4-mismatches = refl

-- ... and, directly: the renamed type of CubeR's cube cell is not
-- CubeL's (the cube cell is the last variable, level 26, in both).
G4-cube-differs : ((CubeR >>= λ Γ → lookup Γ 26) >>= λ A → just (A [ renRL ]ty))
                ≡ (CubeL >>= λ Γ → lookup Γ 26) → ⊥
G4-cube-differs ()

-- G4 up to coherence: substitutions in both directions, each the
-- renaming on the 26 lower generators.
G4-toL : WFSub toL (fromJust CubeL)
G4-toL = cert (wfSub? _ _) tt

G4-toR : WFSub toR (fromJust CubeR)
G4-toR = cert (wfSub? _ _) tt

-- The two orientations of the cylinder agree on the square.
square-orientations : squareMismatches ≡ []
square-orientations = refl
