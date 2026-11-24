------------------------------------------------------------------------
-- Conical transfors at level 2 over a 2-dimensional diagram (ledger
-- B18), checked by the certified checker of CaTTExp.Check.
--
-- This module is slow (about 25 minutes per check on Agda 2.6.3 and
-- 2.7.0.1: the contexts evaluate to CaTT terms of several hundred
-- thousand nodes), so Everything does not import it. Typecheck it on
-- its own. The same checks for all three 2-dimensional shapes, cone
-- and cocone, run in seconds compiled: tools/agda-run/ConesTr2Run.agda.
------------------------------------------------------------------------
module CaTTExp.ConesTr2Slow where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)
open import CaTTExp.Cones

ok : ExCtx → Bool
ok K = is-just (checkCtx (evCtx K))

okM : Maybe Ctrf → Bool
okM nothing  = false
okM (just T) = ok (Ctrf.ctx T)

-- x, f : x → x, α : f ⇒ f.
Loop : ExCtx
Loop = ob ∷ hom ob (v 0) (v 0) ∷ hom (hom ob (v 0) (v 0)) (v 1) (v 1) ∷ []

_ : okM (ctrf 2 Loop) ≡ true
_ = refl

_ : okM (coctrf 2 Loop) ≡ true
_ = refl
