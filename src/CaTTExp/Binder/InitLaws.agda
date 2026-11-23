------------------------------------------------------------------------
-- INIT's binder interface satisfies the stability laws
-- (CaTTExp.Binder.Laws.BinderLaws), so substitution, renaming and
-- weakening are admissible for CaTT + INIT (CaTTExp.Binder.Subst,
-- CaTTExp.Binder.Rename), for every coh side condition.
--
-- Under a substitution σ of the parameters by locally closed terms:
--  * positivity is preserved (a sort stays that sort, and a parameter-only object
--    stays parameter-only; a non-⊤ target may become ⊤, never the
--    reverse), and the selector conditions are unchanged;
--  * the argument telescopes and result types commute with σ, because
--    each is built from Δ by opening and the naturality cylinders of
--    CaTTExp.Binder.Cyl, which commute with σ (CaTTExp.Binder.CylLaws:
--    σ acts on free variables only, and the cylinders' data commute
--    with it); σ does not change the number of sorts, nor which entries
--    the dimension-1 fillers cover (CaTTExp.Binder.CylOK.goodTy-[]).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Init
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Laws as Laws

module CaTTExp.Binder.InitLaws (bs : Base) where

open Base bs using (top?)

private
  𝕊 : Signature
  𝕊 = initSig bs

open Signature 𝕊
open Laws 𝕊
open import CaTTExp.Binder.InitLawsGen K Former (λ b → b) top? public

------------------------------------------------------------------------
-- The laws (CaTTExp.Binder.InitLawsGen, with B = Former).

initLaws : BinderLaws
initLaws = record
  { side-stable = side-stableI
  ; args-stable = args-stableI
  ; res-stable  = res-stableI
  ; res-sc      = res-scI
  }
