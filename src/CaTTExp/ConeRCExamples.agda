------------------------------------------------------------------------
-- Machine checks for CaTTExp.ConeRC. Every `_ = refl` runs the
-- certified checker on the constructed cone context.
------------------------------------------------------------------------
module CaTTExp.ConeRCExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)
open import CaTTExp.Cones
open import CaTTExp.ConeRC
open import CaTTExp.ConesExamples using (ok; okM; shapes; module TermCones; module TermCones2)

coneRC : RC → ExCtx → Maybe ExCtx
coneRC rc Γ = ConeRC.cone rc Γ

-- Globular shapes need no oracle: every gluing is literal.
_ : all (λ Γ → okM (coneRC rcNone Γ)) shapes ≡ true
_ = refl

-- 1-dimensional composite boundaries, with RC(1) as the oracle.
_ : all (λ Γ → okM (coneRC rc1 Γ)) TermCones.termShapes ≡ true
_ = refl

-- …and they are cones in the sense of (KE).
keRC : RC → ExCtx → Bool
keRC rc Γ with coneRC rc Γ
... | nothing = false
... | just K  = KE.okConeAll (evCtx K) (length Γ)

_ : all (keRC rc1) TermCones.termShapes ≡ true
_ = refl

-- 2-dimensional boundaries need RC(2): with RC(1) alone the
-- construction stops at an unanswered query of a 2-dimensional type.
qdim : Maybe Query → Nat
qdim nothing            = 0
qdim (just (_ , A , _)) = dim A

_ : map (λ Γ → qdim (ConeRC.firstMiss rc1 Γ)) TermCones2.twoTerm ≡ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ []
_ = refl
