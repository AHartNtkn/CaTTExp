------------------------------------------------------------------------
-- Decidable reachability under a length bound
-- (notes/design-decisions.md §1, Lemma J-dec).
--
-- The lax-interchange kernel decides its side condition by asking
-- whether a directed path of cells exists in the free object F_T(Γ)
-- of the chosen theory T on a finite pasting diagram Γ. For T₁₂ and
-- for every law setting J(S) of the decision, three facts give a
-- decision procedure:
--   (a) equality of cells is decidable,
--   (b) at fixed boundaries there are finitely many one-letter steps
--       out of a cell (finite contextual alphabet, (K50)),
--   (c) a positive grading bounds the length of every path between
--       two given cells ((K45), (K50)); J(S) has a subset of T₁₂'s
--       equations on the same signature, so T₁₂'s grading bounds its
--       paths too.
-- This module proves the abstract step: (a)–(c) imply that
-- reachability is decidable. It also proves the transport lemma used
-- for importing developments between law settings: a map that sends
-- steps to steps sends paths to paths (switching a law on is a
-- quotient map of free objects that is the identity on letters).
------------------------------------------------------------------------
module CaTTExp.Join.BoundedReach where

open import CaTTExp.Prelude

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

-- Paths of any length for a step function `next`.
infixr 5 _◅_
data Star {A : Set} (next : A → List A) : A → A → Set where
  ε   : ∀ {x} → Star next x x
  _◅_ : ∀ {x y z} → y ∈ next x → Star next y z → Star next x z

module Reach {A : Set} (_≟_ : (x y : A) → Dec (x ≡ y)) (next : A → List A) where

  -- Paths of length at most k.
  data Within : Nat → A → A → Set where
    now   : ∀ {k x} → Within k x x
    later : ∀ {k x y z} → y ∈ next x → Within k y z → Within (suc k) x z

  within→star : ∀ {k x z} → Within k x z → Star next x z
  within→star now         = ε
  within→star (later m w) = m ◅ within→star w

  mutual
    within? : ∀ k x z → Dec (Within k x z)
    within? zero x z with x ≟ z
    ... | yes refl = yes now
    ... | no x≠z   = no λ { now → x≠z refl }
    within? (suc k) x z with x ≟ z
    ... | yes refl = yes now
    ... | no x≠z with any? k z (next x)
    ...   | yes (y , m , w) = yes (later m w)
    ...   | no ¬r = no λ { now → x≠z refl ; (later m w) → ¬r (_ , m , w) }

    any? : ∀ k z (ys : List A) → Dec (Σ A λ y → (y ∈ ys) × Within k y z)
    any? k z [] = no λ { (_ , () , _) }
    any? k z (y ∷ ys) with within? k y z
    ... | yes w = yes (y , here , w)
    ... | no ¬w with any? k z ys
    ...   | yes (y′ , m , w) = yes (y′ , there m , w)
    ...   | no ¬r = no λ { (_ , here , w) → ¬w w
                         ; (y′ , there m , w) → ¬r (y′ , m , w) }

  -- (c): a bound on path length makes reachability decidable.
  module Bounded (bound : A → A → Nat)
                 (bounded : ∀ {x z} → Star next x z → Within (bound x z) x z) where

    reach? : ∀ x z → Dec (Star next x z)
    reach? x z with within? (bound x z) x z
    ... | yes w = yes (within→star w)
    ... | no ¬w = no λ s → ¬w (bounded s)

-- Transport: a map sending steps to steps sends paths to paths.
module Transport {A B : Set} (nextA : A → List A) (nextB : B → List B)
                 (f : A → B)
                 (step : ∀ {x y} → y ∈ nextA x → f y ∈ nextB (f x)) where

  transport : ∀ {x z} → Star nextA x z → Star nextB (f x) (f z)
  transport ε       = ε
  transport (m ◅ s) = step m ◅ transport s
