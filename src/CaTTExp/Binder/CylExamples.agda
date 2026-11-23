------------------------------------------------------------------------
-- Binder cylinders agree with the pure construction (by `refl`).
--
-- On the torus T = (x, p q : x → x, l : p ; q ⇒ q ; p), with every
-- variable selected and the dimension-1 filler family K₁ of
-- CaTTExp.Naturality.DimOne: the type of l↑ computed by
-- CaTTExp.Binder.Cyl, with the entries of T as bound variables of a
-- binder and the generic datum of the cylinder context, is the
-- embedding of the pure one (CaTTExp.Naturality.Raw), the last entry of
-- the cylinder context T↑. Likewise for p↑ and for the cylinder of the
-- composite p ; q itself.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (extend)
open import CaTTExp.Binder.Des using (desBinders)
open import CaTTExp.Naturality.Raw using (Sel; ◇; _◂_; datum)
import CaTTExp.Naturality.Raw as R
open import CaTTExp.Naturality.DimOne using (K₁)
open import CaTTExp.GraphFillerTotal.Chains using (chainC)

module CaTTExp.Binder.CylExamples where

𝕊 : Signature
𝕊 = extend P.∅ (desBinders P.K)

open Signature 𝕊
open import CaTTExp.Binder.Pasting 𝕊 using (embTy; embTm; embSub; embCtx)
import CaTTExp.Binder.Cyl 𝕊 K₁ as B
module PC = R.Cyl K₁

-- Pure: the torus and its full selection.
pq qp : P.Tm
pq = P.coh (chainC 2) (P.arr P.⋆ (P.var 0) (P.var 3))
           (P.⟨⟩ P.,ₛ P.var 0 P.,ₛ P.var 0 P.,ₛ P.var 1 P.,ₛ P.var 0 P.,ₛ P.var 2)
qp = P.coh (chainC 2) (P.arr P.⋆ (P.var 0) (P.var 3))
           (P.⟨⟩ P.,ₛ P.var 0 P.,ₛ P.var 0 P.,ₛ P.var 2 P.,ₛ P.var 0 P.,ₛ P.var 1)

Al : P.Ty
Al = P.arr (P.arr P.⋆ (P.var 0) (P.var 0)) pq qp

Y4 : Sel
Y4 = ◇ ◂ true ◂ true ◂ true ◂ true

Dp : R.Datum
Dp = PC.gen Y4

-- Binder: the same with the entries as bound variables.
b : Nat → Tm
b i = bvar 0 i

pqB qpB : Tm
pqB = coh (embCtx (chainC 2)) (arr ⋆ (var 0) (var 3)) (⟨⟩ ,ₛ b 0 ,ₛ b 0 ,ₛ b 1 ,ₛ b 0 ,ₛ b 2)
qpB = coh (embCtx (chainC 2)) (arr ⋆ (var 0) (var 3)) (⟨⟩ ,ₛ b 0 ,ₛ b 0 ,ₛ b 2 ,ₛ b 0 ,ₛ b 1)

AlB : Ty
AlB = arr (arr ⋆ (b 0) (b 0)) pqB qpB

Db : B.Datum
Db = B.datum (embSub (R.mm Dp)) (embSub (R.mp Dp)) (λ _ → true) (λ i → embTm (R.th Dp i))

_ : B.cylTy Db (b 3) AlB ≡ embTy (PC.cylTy Dp (P.var 3) Al)
_ = refl

_ : B.cylTy Db (b 1) (arr ⋆ (b 0) (b 0)) ≡ embTy (PC.cylTy Dp (P.var 1) (P.arr P.⋆ (P.var 0) (P.var 0)))
_ = refl

_ : B.cyl Db pqB ≡ embTm (PC.cyl Dp pq)
_ = refl
