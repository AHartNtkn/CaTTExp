------------------------------------------------------------------------
-- Examples for the total filler on cells of dimension ≥ 2
-- (CaTTExp.GraphFillerTotal.Higher).
--
-- The 3-cell and the 4-cell come from the theorem `totalN`, applied to
-- typing derivations of the two parallel cells, not from running a
-- checker on the output. The cells are the ones of
-- CaTTExp.GraphFillerExamples (dimensions 3 and 4 on the loop L), and
-- the structural filler gives the same terms as the fuel-based tactic.
------------------------------------------------------------------------
module CaTTExp.GraphFillerTotal.HigherExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GraphFillerTotal.Higher
import CaTTExp.GraphFiller as GF
open import CaTTExp.GraphFillerExamples
  using (L; G; hom; hom₂; hom₃; [ss]s; s[ss]; a₃; a₃'; a₄; a₄'; c₃₃)

-- A typing derivation found by the certified checker, at its own type.
typed : (Γ : Ctx) (t : Tm) → {ok : T (is-just (infer Γ t))} →
        Γ ⊢tm t ∶ fst (from-just (infer Γ t) {ok})
typed Γ t {ok} = snd (from-just (infer Γ t) {ok})

L-graph : Graph L
L-graph = isGraph-ok L tt

-- Dimension 3: the associator a₃ and a₃ composed with an identity.
three-cell : L ⊢tm fillN L a₃ a₃' hom₂ ∶ arr hom₂ a₃ a₃'
three-cell = totalN L-graph (typed L a₃) (typed L a₃')

-- A cell and itself.
three-cell-loop : L ⊢tm fillN L a₃ a₃ hom₂ ∶ arr hom₂ a₃ a₃
three-cell-loop = totalN L-graph (typed L a₃) (typed L a₃)

-- Dimension 4: two different 3-cells a₃ ⇛ a₃'.
four-cell : L ⊢tm fillN L a₄ a₄' hom₃ ∶ arr hom₃ a₄ a₄'
four-cell = totalN L-graph (typed L a₄) (typed L a₄')

-- They are the terms the fuel-based tactic finds.
_ : fillN L a₃ a₃' hom₂ ≡ fst (from-just (GF.fill L a₃ a₃' hom₂))
_ = refl

_ : fillN L a₄ a₄' hom₃ ≡ fst (from-just (GF.fill L a₄ a₄' hom₃))
_ = refl
