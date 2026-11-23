------------------------------------------------------------------------
-- Chapter 6's colimit heads (spec §6.3; ledger S26g), as the second
-- instance of the limit heads of CaTTExp.Binder.LimHeads:
--
--   colim_Γ      arity Γ, type ⋆                               (colim)
--   q_{Γ,g}      arity Γ, type: the type of cell g of the
--                specified cocone over Γ (CaTTExp.Cones.CoconeOf),
--                with apex colim_Γ[id] and earlier cells
--                q_{Γ,g′}[id]                                 (ucocone)
--
-- Spec §6.3: full duality is not a symmetry of L, so colimits are not
-- obtained by dualising derivations; they are a separate instance of
-- the same construction over the cocone shape. That is what this file
-- does: LimConstruction is generic in the shape, and the cocone shape
-- is CaTTExp.Cones' specified cocone over a globular base. In
-- dimension 1 the cocone cell reverses the leg: for f : x → y,
-- q_f : q_x → f ∗ q_y (`ColimExamples`).
--
-- Limits and colimits are put in one family `limColimSpec` over the
-- former set LCF (a copy of LimF for each), so a signature can have
-- both. As a HeadSpec it gets BinderLaws and the (op) rule from
-- CaTTExp.Binder.HeadSpec, with no proof specific to colimits.
--
-- Like lim and λ, colim and q do not suspend in general (ledger S27
-- (g), notes/operation-heads.md §4): Σ colim would be a colimit inside
-- a hom.
--
-- Not here: the universal cofiller couni over the cocone-transfor
-- shape (§6.3), like uni for limits (ledger S27, HEADS); bases that
-- are not globular (the specified cocone is defined on globular
-- bases, as the cone is).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Cones using (ExCtx; evCtx; module CoconeOf)
open import CaTTExp.Binder.LimHeads
open import CaTTExp.Binder.LimHeadsExamples using (toExCtx; coneShape)
open import CaTTExp.Binder.HeadSpec using (HeadSpec)

module CaTTExp.Binder.Colim where

-- The specified cocone over a globular base.
coconeShape : P.Ctx → Maybe P.Ctx
coconeShape Γ = toExCtx Γ >>= λ E → just (evCtx (CoconeOf.cocone E))

-- Limit and colimit heads together.
data LCF : Set where
  limH   : LimF → LCF
  colimH : LimF → LCF

_==LC_ : LCF → LCF → Bool
limH a   ==LC limH b   = a ==L b
colimH a ==LC colimH b = a ==L b
_        ==LC _        = false

==LC-sound : ∀ a b → T (a ==LC b) → a ≡ b
==LC-sound (limH a)   (limH b)   p = cong limH (==L-sound a b p)
==LC-sound (colimH a) (colimH b) p = cong colimH (==L-sound a b p)
==LC-sound (limH _)   (colimH _) ()
==LC-sound (colimH _) (limH _)   ()

module LimColim (K : Set) where
  module Li = LimConstruction K LCF limH   coneShape
  module Co = LimConstruction K LCF colimH coconeShape

  open import CaTTExp.Binder.Syntax K LCF using (Ctx; Ty)

  hctxLC : LCF → Nat → Ctx
  hctxLC (limH h)   = Li.hctx h
  hctxLC (colimH h) = Co.hctx h

  htyLC : LCF → Nat → Ty
  htyLC (limH h)   = Li.hty h
  htyLC (colimH h) = Co.hty h

  hokLC : LCF → Nat → Bool
  hokLC (limH h)   = Li.hok h
  hokLC (colimH h) = Co.hok h

limColimSpec : (K : Set) → HeadSpec K
limColimSpec K = record
  { H = LCF ; _==H_ = _==LC_ ; ==H-sound = ==LC-sound
  ; hctx = hctxLC ; hty = htyLC ; hok = hokLC }
  where open LimColim K

------------------------------------------------------------------------
-- Substitution, weakening and the certified checker for limits and
-- colimits together, over any binder-free signature (HeadSpec.Laws).

import CaTTExp.Signature as Old
import CaTTExp.Binder.HeadSpec as HS

module LimColimLaws (𝕊₀ : Old.Signature) where
  open HS.Laws 𝕊₀ (limColimSpec (Old.Signature.K 𝕊₀)) public using (𝕊; spec-laws; spec-honest)
