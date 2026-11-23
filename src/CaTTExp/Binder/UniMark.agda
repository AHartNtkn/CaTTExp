------------------------------------------------------------------------
-- J2's conclusion that every comparison component of the universal
-- filler is invertible, as a clause of the mark judgment (ledger S27
-- (e″), spec §6.2):
--
--   (UNI-inv)  uni^{y}_{Γ,n}[σ] is inv, for every component y (selector
--              ≥ 1); uni^w (selector 0) gets no mark.
--
-- It is CaTTExp.Binder.HeadMark's (HEAD-inv) for the heads of
-- CaTTExp.Binder.UniHeads, over any cone shape and horn shape. The
-- judgment satisfies MarkRen, MarkSub and MarkVar, so substitution
-- (`tm[]`) and weakening hold for CaTT + lim + λ + uni with it, by
-- CaTTExp.Binder.Subst; the family's BinderLaws are HeadSpec's.
-- Presupposition (`uni-tm-ty`) holds with it too, by
-- CaTTExp.Binder.UniPresup, which is generic in the mark judgment.
--
-- (UNI-inv) has no premise: it is §6.2's J2 for selector ≥ 1 taken as
-- an axiom, and this module encodes that rule, nothing more. Its
-- semantic soundness rests on §6.2's certification line, which is
-- proved for 2-categories and is a claim in (∞,ω).
--
-- The premise side of §6.2 ("σ must supply inv derivations" for the
-- marked horn entries) is the kernel's mark premise on the arity
-- (UniHeads). With (UNI-inv), the components of one filler are
-- accepted where a later horn asks for an inv cell.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.UniHeads
import CaTTExp.Binder.HeadSpec as HS

module CaTTExp.Binder.UniMark
  (shape : P.Ctx → Maybe P.Ctx) (ushape : P.Ctx → Nat → Maybe UShape) where

open HS.Laws P.∅ (uniSpec P.K shape ushape) public using (𝕊; spec-laws)
open Signature 𝕊
open import CaTTExp.Binder.Laws 𝕊 using (Closed)

uniInv : LUF → Nat → Bool
uniInv (uniF _ _) (suc _) = true
uniInv _          _       = false

open import CaTTExp.Binder.Typing 𝕊 using (cattSide)
open import CaTTExp.Binder.HeadMark 𝕊 cattSide uniInv public
  using (headMark; markVar; markRen; markSub)

-- The base signature has no constants.
closed : Closed
closed ()

open import CaTTExp.Binder.Subst 𝕊 cattSide headMark using (tm[])

-- Substitution for CaTT with lim, the universal cone and uni, with
-- (UNI-inv) in the mark judgment.
uni-tm[] = tm[] closed spec-laws markRen markSub markVar

-- Presupposition with this mark judgment (CaTTExp.Binder.UniPresup,
-- generic in the mark judgment): every term of CaTT + lim + λ + uni,
-- typed with (MARK) + (HEAD-inv), has a well-formed type.
open import CaTTExp.Binder.UniPresup shape ushape headMark markRen markSub markVar public
  using (uni-presup; uni-tm-ty)
