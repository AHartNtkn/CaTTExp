------------------------------------------------------------------------
-- The uni heads over the general horns of CaTTExp.Lim.HornGen (every
-- globular diagram of dimension ≤ 1, n = 0, 1; ledger S27 (e′)), in the
-- kernel with plain CaTT's side condition and rule (MARK). Every
-- statement is `refl`.
--
-- On the cospan a → c ← b (pullbacks) and the parallel pair
-- (equalisers): every uni head is valid, its arity is a well-formed
-- context, and uni^w has the type of J1.
------------------------------------------------------------------------
module CaTTExp.Binder.UniHornGenExamples where

open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.LimHeads
open import CaTTExp.Binder.UniHeads
open import CaTTExp.Binder.LimHeadsExamples using (coneShape)
import CaTTExp.Binder.HeadSpec as HS
import CaTTExp.Lim.HornGen as HG
open import CaTTExp.Lim.HornGenExamples using (Cospan; Par)

hornShape : P.Ctx → Nat → Maybe UShape
hornShape Γ n = HG.hornData Γ n >>= λ d → just (ush (HG.HornData.J2 d) (HG.HornData.horn d) (HG.HornData.marked d))

sp = uniSpec P.K coneShape hornShape
open HS.Laws P.∅ sp
open HS.HeadSpec sp using (hctx)
open Signature 𝕊
open import CaTTExp.Binder.Typing 𝕊
open import CaTTExp.Binder.CheckWith 𝕊 cattSide varMark

inferTy : Ctx → Tm → Maybe Ty
inferTy Γ t = infer Γ t >>= λ r → just (fst r)

valid : LUF → Nat → Bool
valid h y = bside h y ε

-- Pullbacks: the cospan has 5 variables; uni^w and the 5 components.
cospan-valid : (valid (uniF Cospan 0) 0 ∧ valid (uniF Cospan 0) 5
                ∧ valid (uniF Cospan 1) 0 ∧ valid (uniF Cospan 1) 5) ≡ true
cospan-valid = refl

cospan-arity : is-just (ctx? (hctx (uniF Cospan 1) 0)) ≡ true
cospan-arity = refl

-- uni^w over the cospan, n = 0 (arity: the 5 diagram variables, c, the
-- 5 cone cells): c → lim.
cospan-uni₀ : inferTy (hctx (uniF Cospan 0) 0) (bnd (uniF Cospan 0) 0 ε (fresh 0 11))
              ≡ just (arr ⋆ (var 5) (bnd (base (limF Cospan)) 0 ε (fresh 0 5)))
cospan-uni₀ = refl

-- Equalisers.
par-valid : (valid (uniF Par 0) 0 ∧ valid (uniF Par 1) 4) ≡ true
par-valid = refl

-- Out of range.
no-comp : valid (uniF Cospan 0) 6 ≡ false
no-comp = refl
