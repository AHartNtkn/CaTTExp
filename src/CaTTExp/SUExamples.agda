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

------------------------------------------------------------------------
-- Insertion (CaTT_sua).

private
  T₂ T₃ : Tree
  T₂ = node (leaf ∷ leaf ∷ [])
  T₃ = node (leaf ∷ leaf ∷ leaf ∷ [])

-- Standard types and coherences agree with the hand-written ones.
_ : stdTy 1 T₂ ≡ compTy
_ = refl
_ : stdCoh 1 T₂ ≡ comp (v 0) (v 1) (v 2) (v 3) (v 4)
_ = refl

-- Both bracketings of a ternary composite insert to the unbiased one.
_ : nf₀ fg-h ≡ stdCoh 1 T₃
_ = refl
_ : nf₀ f-gh ≡ stdCoh 1 T₃
_ = refl

-- Hence the associator is an identity in CaTT_sua.
_ : T (assoc ==su idTm (arr ⋆ (v 0) (v 5)) (stdCoh 1 T₃))
_ = tt

-- Vertical associativity: insertion along branches of height 1.
private
  V₂ V₃ : Tree
  V₂ = node (node (leaf ∷ leaf ∷ []) ∷ [])
  V₃ = node (node (leaf ∷ leaf ∷ leaf ∷ []) ∷ [])

  vc : List Tm → Tm
  vc ts = coh (ctxOf V₂) (stdTy 2 V₂) ⟪ ts ⟫

  -- in ⌊V₃⌋: x y f g α h β k γ = 0 … 8
  αβ-γ α-βγ : Tm
  αβ-γ = vc (v 0 ∷ v 1 ∷ v 2 ∷ v 5 ∷ vc (v 0 ∷ v 1 ∷ v 2 ∷ v 3 ∷ v 4 ∷ v 5 ∷ v 6 ∷ []) ∷ v 7 ∷ v 8 ∷ [])
  α-βγ = vc (v 0 ∷ v 1 ∷ v 2 ∷ v 3 ∷ v 4 ∷ v 7 ∷ vc (v 0 ∷ v 1 ∷ v 3 ∷ v 5 ∷ v 6 ∷ v 7 ∷ v 8 ∷ []) ∷ [])

_ : nf₀ αβ-γ ≡ stdCoh 2 V₃
_ = refl
_ : nf₀ α-βγ ≡ stdCoh 2 V₃
_ = refl

-- The terms above are well typed (so the checks are not vacuous).
_ : T (is-just (infer (ctxOf V₃) αβ-γ) ∧ is-just (infer (ctxOf V₃) α-βγ)
       ∧ is-just (infer (ctxOf V₃) (stdCoh 2 V₃)) ∧ is-just (infer Comp₃ (stdCoh 1 T₃)))
_ = tt
