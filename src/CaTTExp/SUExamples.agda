------------------------------------------------------------------------
-- Checked examples for strictly unital normalisation (CaTTExp.SU).
------------------------------------------------------------------------
module CaTTExp.SUExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Examples
open import CaTTExp.SU ∅

x y f : Tm
x = v 0
y = v 1
f = v 2

-- The disc and identity contexts agree with the examples' trees.
_ : D₀ ≡ Dᵈ 0
_ = refl
_ : D₁ ≡ Dᵈ 1
_ = refl
_ : id x ≡ idTm ⋆ x
_ = refl

-- id(x) ; f  ⟶*  f   (pruning, then disc removal), and f ; id(y) too.
_ : T (comp x x (id x) y f ==su f)
_ = tt
_ : T (comp x y f y (id y) ==su f)
_ = tt

-- The left unitor is an identity: its type normalises to f ⇒ f.
_ : T (lunitor ==su idTm (arr ⋆ x y) f)
_ = tt

-- id(id x) is a normal form, distinct from id x.
_ : nf₀ (id (id x)) ≡ id (id x)
_ = refl
_ : T (not (id (id x) ==su id x))
_ = tt

-- The associator with its middle arrow an identity is the identity on
-- the composite of the other two.
private
  a b c d g h : Tm
  a = v 0
  b = v 1
  c = v 2
  d = v 3
  g = v 4
  h = v 5

-- In context (a, b, c : a → b, d, g : b → d): assoc(c, id b, g) is
-- an endo-coherence on c;g after pruning.
_ : T (coh Comp₃ assocTy ⟪ a ∷ b ∷ c ∷ b ∷ id b ∷ d ∷ g ∷ [] ⟫
       ==su idTm (arr ⋆ a d) (comp a b c d g))
_ = tt
