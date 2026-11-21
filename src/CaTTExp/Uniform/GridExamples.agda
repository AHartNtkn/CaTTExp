------------------------------------------------------------------------
-- The switch settings on suspended grids, computed
-- (spec/02-lax-core.md §2.3 table and example (b); ledger S3).
--
-- For each grid: `complete` (no run of more than m·n edges, so the
-- enumeration lists every valid path) and `nodup` (no repetition) are
-- checked by evaluation; with CaTTExp.Uniform.Grid.OnGrid.Classes they
-- make `reps sw` a repetition-free list of representatives of all the
-- 4-cells in setting sw. Its length is the number of 4-cells.
--
--   1 × 2 grid  (V, V + R, V + inner law, T₁₂):  2, 1, 2, 1
--   2 × 1 grid                                    2, 2, 1, 1
--   2 × 3 grid                                    49, 14, 29, 2
--
-- These agree with scripts/e6/interchange_fibre_decorations.py
-- (`check_switch_settings`) as it stands after the 2026-11-20 fix of
-- the inner-law bit. The 2 × 3 computation takes about two minutes.
--
-- Example (b) of spec §2.3, on the strip (the 2 × 1 grid): the direct
-- crossing u and the paste v of the two crossings are equal 4-cells
-- exactly in the settings with the inner law. The mirror statement for
-- R holds on the 1 × 2 grid.
------------------------------------------------------------------------
module CaTTExp.Uniform.GridExamples where

open import CaTTExp.Prelude
open import CaTTExp.Join.Finite using (lengthL; NoDup)
open import CaTTExp.Join.SwitchLaws using (Switches; vS; iccS; rspS; allS)
open import CaTTExp.Uniform.Arith
open import CaTTExp.Uniform.ListKit using (mapK; isYes; isYes-sound)
open import CaTTExp.Uniform.Grid

module Count (m n : Nat) where
  open OnGrid m n public

  raw : List RawPath
  raw = allPaths (m * n) start end

  -- Checked by evaluation for each grid below.
  Complete : Set
  Complete = runs (suc (m * n)) start ≡ []

  nodup : T (isYes (nodup? raw)) → NoDup raw
  nodup = isYes-sound (nodup? raw)

  counts : List Nat
  counts = mapK (λ sw → lengthL (Classes.reps (m * n) sw)) (vS ∷ rspS ∷ iccS ∷ allS ∷ [])

------------------------------------------------------------------------
-- 1 × 2

module G12 = Count 1 2

complete12 : G12.Complete
complete12 = refl

nodup12 : NoDup G12.raw
nodup12 = G12.nodup tt

counts12 : G12.counts ≡ 2 ∷ 1 ∷ 2 ∷ 1 ∷ []
counts12 = refl

------------------------------------------------------------------------
-- 2 × 1 (the strip of example (b))

module G21 = Count 2 1

complete21 : G21.Complete
complete21 = refl

nodup21 : NoDup G21.raw
nodup21 = G21.nodup tt

counts21 : G21.counts ≡ 2 ∷ 2 ∷ 1 ∷ 1 ∷ []
counts21 = refl

------------------------------------------------------------------------
-- 2 × 3

module G23 = Count 2 3

complete23 : G23.Complete
complete23 = refl

nodup23 : NoDup G23.raw
nodup23 = G23.nodup tt

raw23 : lengthL G23.raw ≡ 49
raw23 = refl

counts23 : G23.counts ≡ 49 ∷ 14 ∷ 29 ∷ 2 ∷ []
counts23 = refl

------------------------------------------------------------------------
-- Example (b): the inner law (left split) on the strip.

module ExampleB where
  open G21

  -- u: the b-cell crosses the composite a₁ a₂ at once;
  -- v: it crosses a₁, then a₂.
  u v : RawPath
  u = ⟨ 0 , 0 , 1 ⟩ ∷ []
  v = ⟨ 0 , 0 , 0 ⟩ ∷ ⟨ 1 , 0 , 0 ⟩ ∷ []

  valid-u : Valid u
  valid-u = refl

  valid-v : Valid v
  valid-v = refl

  distinct-V : ¬ (vS ⊢ u ≈ v)
  distinct-V e = Setting.conn-complete vS valid-u e

  distinct-R : ¬ (rspS ⊢ u ≈ v)
  distinct-R e = Setting.conn-complete rspS valid-u e

  equal-inner : iccS ⊢ u ≈ v
  equal-inner = Setting.conn-sound iccS u v tt

  equal-T12 : allS ⊢ u ≈ v
  equal-T12 = Setting.conn-sound allS u v tt

-- The mirror statement for R, on the 1 × 2 grid.
module ExampleR where
  open G12

  u v : RawPath
  u = ⟨ 0 , 1 , 0 ⟩ ∷ []
  v = ⟨ 1 , 0 , 0 ⟩ ∷ ⟨ 0 , 0 , 0 ⟩ ∷ []

  valid-u : Valid u
  valid-u = refl

  valid-v : Valid v
  valid-v = refl

  distinct-V : ¬ (vS ⊢ u ≈ v)
  distinct-V e = Setting.conn-complete vS valid-u e

  distinct-inner : ¬ (iccS ⊢ u ≈ v)
  distinct-inner e = Setting.conn-complete iccS valid-u e

  equal-R : rspS ⊢ u ≈ v
  equal-R = Setting.conn-sound rspS u v tt

  equal-T12 : allS ⊢ u ≈ v
  equal-T12 = Setting.conn-sound allS u v tt
