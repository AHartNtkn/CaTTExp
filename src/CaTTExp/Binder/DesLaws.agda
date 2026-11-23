------------------------------------------------------------------------
-- DES's binder interface satisfies the stability laws
-- (CaTTExp.Binder.Laws.BinderLaws), over any binder-free signature 𝕊₀.
-- So substitution and weakening are admissible for 𝕊₀ + DES with every
-- coh side condition and every stable mark judgment
-- (CaTTExp.Binder.Subst), the checker is complete
-- (CaTTExp.Binder.Completeness), and the extension is conservative
-- (CaTTExp.Binder.Embed; for plain CaTT, `Embed.CaTT 𝕊₀ (desBinders K)`,
-- and for L, CaTTExp.Gray.DesSide).
--
-- The laws are CaTTExp.Binder.DesLawsGen's, with B = DesF.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (Binders; extend)
open import CaTTExp.Binder.Des
import CaTTExp.Binder.Laws as Laws

module CaTTExp.Binder.DesLaws (𝕊₀ : Old.Signature) where

𝕊 : Signature
𝕊 = extend 𝕊₀ (desBinders (Old.Signature.K 𝕊₀))

open Signature 𝕊
open Laws 𝕊
open import CaTTExp.Binder.DesLawsGen K DesF (λ b → b)

desLaws : BinderLaws
desLaws = record
  { side-stable = side-stableD
  ; args-stable = args-stableD
  ; res-stable  = res-stableD
  ; res-sc      = res-scD
  }
