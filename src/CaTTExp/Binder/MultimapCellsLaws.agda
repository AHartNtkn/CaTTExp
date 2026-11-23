------------------------------------------------------------------------
-- The stability laws (CaTTExp.Binder.Laws.BinderLaws) of the Gray
-- object formers with the cell heads mmc (CaTTExp.Binder.MultimapCells),
-- over any binder-free signature 𝕊₀.
--
-- The family is a HeadSpec (`cellSpec`), so CaTTExp.Binder.HeadSpec
-- gives the laws, hence substitution and weakening for 𝕊₀ + ⊗, \, / +
-- mmc with every coh side condition and every stable mark judgment, the
-- certified checker and its completeness, and each valid head's rule is
-- (op). Conservativity over 𝕊₀ is CaTTExp.Binder.Embed.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
import CaTTExp.Binder.HeadSpec as HS
open import CaTTExp.Binder.MultimapCells using (cellSpec)

module CaTTExp.Binder.MultimapCellsLaws (𝕊₀ : Old.Signature) where

open HS.Laws 𝕊₀ (cellSpec (Old.Signature.K 𝕊₀)) public using (𝕊; spec-laws; spec-honest; spec-head)

gcLaws = spec-laws
