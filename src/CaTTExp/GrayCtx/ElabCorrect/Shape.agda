------------------------------------------------------------------------
-- Shape facts for a fixed tree, by computation (ledger S20 (ii)).
--
-- `shape? τ build` decides everything ShapeOK asks for a given tree τ
-- and builder: it runs the builder on ctxOf τ, types its output in
-- ctxOf τ with the certified checker, and decides the side condition
-- and the coverage. For a fixed shape, `cert (shape? τ build) tt` is a
-- proof once and for all; the instances (images in an arbitrary Γ) are
-- then covered by Coh.cohT-ok with no further check.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.ElabCorrect.Shape where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab using (tops)
open import CaTTExp.GrayCtx.ElabCorrect.Fill using (covers)
open import CaTTExp.GrayCtx.ElabCorrect.Coh

decT : (b : Bool) → Maybe (T b)
decT true  = just tt
decT false = nothing

shape? : ∀ τ build → Maybe (ShapeOK τ build)
shape? τ build with build (ctxOf τ) in eq
... | nothing        = nothing
... | just (s , u)   =
  checkCtx P >>= λ w →
  inferTm P w s >>= λ { (A , ds) →
  inferTm P w u >>= λ { (B , du) →
  castTy B A du >>= λ du' →
  decT (cattSide P A s u) >>= λ sd →
  decT (covers P (tops τ)) >>= λ cv →
  just (shapeOK s u A eq ds du' sd cv) } }
  where P = ctxOf τ

cert : ∀ {a} {A : Set a} (m : Maybe A) → T (is-just m) → A
cert (just x) _ = x
