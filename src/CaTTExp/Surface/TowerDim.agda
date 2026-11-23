------------------------------------------------------------------------
-- The dimension of a tower (the number of boundary levels above its
-- base), and its invariance under ≈w.
------------------------------------------------------------------------
module CaTTExp.Surface.TowerDim where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Cell using (Tower; base; step; _≈w_)

tdim : Tower → Nat
tdim (base _)     = 0
tdim (step S _ _) = suc (tdim S)

tdim-≈w : ∀ X Y → X ≈w Y → tdim X ≡ tdim Y
tdim-≈w (base _)     (base _)     _       = refl
tdim-≈w (step S _ _) (step S′ _ _) (p , _) = cong suc (tdim-≈w S S′ p)
