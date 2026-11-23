------------------------------------------------------------------------
-- A check of CaTTExp.PsRaiseCongr on the 2-disc x, y, f, g, α : f → g.
-- c = coh D2 (f → g) id is the unary composite of α (an operation).
-- Raising α gives the congruence cell c[incl⁻] → c[incl⁺], i.e. from
-- the composite of α to the composite of α′; its type and side
-- condition are computed here, and the general theorems instantiated.
------------------------------------------------------------------------
module CaTTExp.PsRaiseCongrExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PsRaise
open import CaTTExp.PsRaiseCongr
open import CaTTExp.GrayCtx.Lift using (raiseT)

private
  bs = true ∷ []
  t  = node (node [] ∷ [])
  B  = arr ⋆ (var 0) (var 1)

-- The side condition of the original coh and of the congruence cell.
_ : cattSide (ctxOf (node (t ∷ []))) B (var 2) (var 3) ≡ true
_ = refl

_ : cattSide (ctxOf (raiseT bs (node (t ∷ [])))) (A^ bs t [] B (var 2) (var 3))
             (c⁻ bs t [] B (var 2) (var 3)) (c⁺ bs t [] B (var 2) (var 3)) ≡ true
_ = refl

-- Its source and target: the composite of α and of α′.
_ : c⁻ bs t [] B (var 2) (var 3) ≡ coh (ctxOf (node (t ∷ []))) (arr B (var 2) (var 3))
                                       (⟨⟩ ,ₛ var 0 ,ₛ var 1 ,ₛ var 2 ,ₛ var 3 ,ₛ var 4)
_ = refl

_ : c⁺ bs t [] B (var 2) (var 3) ≡ coh (ctxOf (node (t ∷ []))) (arr B (var 2) (var 3))
                                       (⟨⟩ ,ₛ var 0 ,ₛ var 1 ,ₛ var 2 ,ₛ var 3 ,ₛ var 5)
_ = refl

-- c is an operation, so incl⁻ and incl⁺ agree on its type (no check
-- here: the general theorem, instantiated).
private
  top : TopOK 2 0 (t ∷ []) bs
  top = (refl , tt) , tt

_ : Agree bs t [] B (var 2) (var 3)
_ = agree-op bs t [] B (var 2) (var 3) 2 tt top tt
