------------------------------------------------------------------------
-- A check of CaTTExp.PsRaise on the 2-disc: raising its 2-cell α gives
-- the 3-disc-shaped context with α, α′ and a 3-cell α → α′; the two
-- inclusions send α to α and to α′, and the source and target of the
-- raised context (at k = 2) are their images; the raised context has
-- dimension 3.
------------------------------------------------------------------------
module CaTTExp.PsRaiseExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PsRaise
open import CaTTExp.GrayCtx.Lift using (raiseT)

D2 : Tree
D2 = node (node (node [] ∷ []) ∷ [])

top : TopOK 2 0 (node (node [] ∷ []) ∷ []) (true ∷ [])
top = (refl , tt) , tt

-- incl⁻ is the identity on levels 0–4; incl⁺ sends α (level 4) to α′ (5).
_ : img (inclM (true ∷ []) (node (node [] ∷ [])) []) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
_ = refl

_ : img (inclP (true ∷ []) (node (node [] ∷ [])) []) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ []
_ = refl

-- ∂⁻ and ∂⁺ of the raised context.
_ : ∂⁻ (ctxOf (raiseT (true ∷ []) D2)) ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
_ = refl

_ : ∂⁺ (ctxOf (raiseT (true ∷ []) D2)) ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ []
_ = refl

-- The general theorems at this instance.
_ = src-incl 2 (true ∷ []) (node (node [] ∷ [])) [] top
_ = tgt-incl 2 (true ∷ []) (node (node [] ∷ [])) [] top

-- The closed-form statements: D2 has dimension 2, so the raised
-- context has dimension 3 and its boundaries are the images of all of D2.
_ : dimCtx (ctxOf (raiseT (true ∷ []) D2)) ≡ 3
_ = dim-raise 2 (true ∷ []) (node (node [] ∷ [])) [] tt top tt

_ = src-raise 2 (true ∷ []) (node (node [] ∷ [])) [] tt top tt
_ = tgt-raise 2 (true ∷ []) (node (node [] ∷ [])) [] tt top tt
