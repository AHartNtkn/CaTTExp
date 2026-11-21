------------------------------------------------------------------------
-- Degree-five computations on suspended grids (ledger S3b;
-- spec/02-lax-core.md §2.3 example (b)).
--
-- Example (b), the strip (2 × 1 grid). u = W(a₁a₂, b) is the direct
-- crossing, v the paste of the crossings of a₁ and a₂.
--   * In V and in V + R: u ≠ v, and neither reaches the other by a
--     5-cell, so SC fails between them in both directions. (On the
--     strip no two edges have disjoint windows, since every edge moves
--     the single b; so there is no 5-letter at all.)
--   * In V + inner law and in T₁₂: u = v, and SC holds (coherence case).
--
-- The 2 × 2 grid. X and Y are the two 4-paths that cross b₂ past a₁,
-- then do the two independent crossings b₂a₂ and b₁a₁ in the two
-- orders, then b₁ past a₂. The positional square goes X ⇛ Y.
--   * In V: X ≠ Y, X reaches Y and Y does not reach X.
--   * In T₁₂ ({inner law, R}): X = Y, so the square is a 5-loop at the
--     single 4-cell of the grid. It is the suspension of the loop H of
--     (K34): X and Y are the two split orders of the full crossing of
--     b₁b₂ past a₁a₂. So 5-paths here have unbounded length, and SC
--     must be decided without a length bound (RuleFin).
------------------------------------------------------------------------
module CaTTExp.Uniform.GridFiveExamples where

open import CaTTExp.Prelude
open import CaTTExp.Join.Finite using (_∈L_)
open import CaTTExp.Join.SwitchLaws using (Switches; vS; iccS; rspS; allS)
open import CaTTExp.Uniform.Rule
open import CaTTExp.Uniform.Grid
open import CaTTExp.Uniform.GridFive
open import CaTTExp.Join.Quiver using (Dec; yes; no)

isYes′ : ∀ {P : Set} → Dec P → Bool
isYes′ (yes _) = true
isYes′ (no _)  = false

------------------------------------------------------------------------
-- Example (b): the strip.

module StripB where
  open OnGrid 2 1

  u v : RawPath
  u = ⟨ 0 , 0 , 1 ⟩ ∷ []
  v = ⟨ 0 , 0 , 0 ⟩ ∷ ⟨ 1 , 0 , 0 ⟩ ∷ []

  vu : Valid u
  vu = refl

  vv : Valid v
  vv = refl

  module InV = Five 2 1 vS
  module InR = Five 2 1 rspS
  module InI = Five 2 1 iccS
  module InT = Five 2 1 allS

  -- No 5-letter on the strip.
  no-letters-u : InV.out (InV.cellOf u vu) ≡ []
  no-letters-u = refl

  no-letters-v : InV.out (InV.cellOf v vv) ≡ []
  no-letters-v = refl

  -- Settings ∅ and {R}: SC fails in both directions.
  noSC-V-uv : ¬ SC InV.layer (InV.cellOf u vu) (InV.cellOf v vv)
  noSC-V-uv s = InV.reach5-complete vu (InV.sc→⇛ s)

  noSC-V-vu : ¬ SC InV.layer (InV.cellOf v vv) (InV.cellOf u vu)
  noSC-V-vu s = InV.reach5-complete vv (InV.sc→⇛ s)

  noSC-R-uv : ¬ SC InR.layer (InR.cellOf u vu) (InR.cellOf v vv)
  noSC-R-uv s = InR.reach5-complete vu (InR.sc→⇛ s)

  noSC-R-vu : ¬ SC InR.layer (InR.cellOf v vv) (InR.cellOf u vu)
  noSC-R-vu s = InR.reach5-complete vv (InR.sc→⇛ s)

  -- Settings {inner law} and {inner law, R}: the same cell, and SC
  -- holds in both directions (coherence case).
  same-I : InI.cellOf u vu ≡ InI.cellOf v vv
  same-I = refl

  same-T : InT.cellOf u vu ≡ InT.cellOf v vv
  same-T = refl

  SC-I-uv : SC InI.layer (InI.cellOf u vu) (InI.cellOf v vv)
  SC-I-uv = InI.⇛→sc {InI.cellOf u vu} {InI.cellOf v vv} (InI.reach5-sound _ _ tt)

  SC-I-vu : SC InI.layer (InI.cellOf v vv) (InI.cellOf u vu)
  SC-I-vu = InI.⇛→sc {InI.cellOf v vv} {InI.cellOf u vu} (InI.reach5-sound _ _ tt)

  SC-T-uv : SC InT.layer (InT.cellOf u vu) (InT.cellOf v vv)
  SC-T-uv = InT.⇛→sc {InT.cellOf u vu} {InT.cellOf v vv} (InT.reach5-sound _ _ tt)

  -- The decision procedure agrees.
  decided : isYes′ (InV.sc? (InV.cellOf u vu) (InV.cellOf v vv)) ∷
            isYes′ (InR.sc? (InR.cellOf u vu) (InR.cellOf v vv)) ∷
            isYes′ (InI.sc? (InI.cellOf u vu) (InI.cellOf v vv)) ∷
            isYes′ (InT.sc? (InT.cellOf u vu) (InT.cellOf v vv)) ∷ []
          ≡ false ∷ false ∷ true ∷ true ∷ []
  decided = refl

------------------------------------------------------------------------
-- The 2 × 2 grid: a directed square in V, a 5-loop in T₁₂.

module Square22 where
  open OnGrid 2 2

  X Y : RawPath
  X = ⟨ 1 , 0 , 0 ⟩ ∷ ⟨ 2 , 0 , 0 ⟩ ∷ ⟨ 0 , 0 , 0 ⟩ ∷ ⟨ 1 , 0 , 0 ⟩ ∷ []
  Y = ⟨ 1 , 0 , 0 ⟩ ∷ ⟨ 0 , 0 , 0 ⟩ ∷ ⟨ 2 , 0 , 0 ⟩ ∷ ⟨ 1 , 0 , 0 ⟩ ∷ []

  vX : Valid X
  vX = refl

  vY : Valid Y
  vY = refl

  sqXY : Sq X Y
  sqXY = sq (⟨ 1 , 0 , 0 ⟩ ∷ []) ⟨ 0 , 0 , 0 ⟩ ⟨ 2 , 0 , 0 ⟩ (⟨ 1 , 0 , 0 ⟩ ∷ []) tt

  module InV = Five 2 2 vS
  module InT = Five 2 2 allS

  -- In V the square is directed: X ≠ Y, X ⇛ Y, and not Y ⇛ X.
  distinct-V : ¬ (InV.cellOf X vX ≡ InV.cellOf Y vY)
  distinct-V ()

  SC-V-XY : SC InV.layer (InV.cellOf X vX) (InV.cellOf Y vY)
  SC-V-XY = InV.⇛→sc {InV.cellOf X vX} {InV.cellOf Y vY} (InV.reach5-sound _ _ tt)

  noSC-V-YX : ¬ SC InV.layer (InV.cellOf Y vY) (InV.cellOf X vX)
  noSC-V-YX s = InV.reach5-complete vY (InV.sc→⇛ s)

  -- In T₁₂, X = Y and the square is a letter from the cell to itself.
  same-T : InT.cellOf X vX ≡ InT.cellOf Y vY
  same-T = refl

  loop-T : InT.cellOf X vX ∈L InT.out (InT.cellOf X vX)
  loop-T = InT.out-complete vX vY sqXY
