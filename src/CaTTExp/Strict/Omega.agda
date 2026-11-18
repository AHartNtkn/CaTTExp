------------------------------------------------------------------------
-- Strict ω-categories, single-set definition (ledger item A3a, general
-- case).
--
-- Street, "The algebra of oriented simplexes" (1987), §1; Steiner,
-- "Omega-categories and chain complexes" (2004), Def. 2.1. A strict
-- ω-category is a set C with boundary maps sₙ, tₙ : C → C and partial
-- compositions x #ₙ y, defined when tₙ x = sₙ y. Cells of every
-- dimension live in the same set; x is an identity in dimension n+1
-- when sₙ x = x. Composition takes its composability proof as an
-- argument, so no decidability or totality is assumed. Axiom (vii) of
-- Steiner (every cell has a finite dimension) is not assumed: nothing
-- below uses it, so the results hold without it.
--
-- The record lives in Set₁ as a structure of the metatheory, like
-- Signature; the object language (CaTT) has no universes.
------------------------------------------------------------------------
module CaTTExp.Strict.Omega where

open import CaTTExp.Prelude

------------------------------------------------------------------------
-- Order on Nat.

data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

≤-refl : ∀ n → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-suc : ∀ {m n} → m ≤ n → m ≤ suc n
≤-suc z≤n     = z≤n
≤-suc (s≤s p) = s≤s (≤-suc p)

≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

<→≤ : ∀ {m n} → m < n → m ≤ n
<→≤ p = ≤-trans (≤-suc (≤-refl _)) p

data Tri (m n : Nat) : Set where
  tri< : m < n → Tri m n
  tri≡ : m ≡ n → Tri m n
  tri> : n < m → Tri m n

tri : ∀ m n → Tri m n
tri zero    zero    = tri≡ refl
tri zero    (suc n) = tri< (s≤s z≤n)
tri (suc m) zero    = tri> (s≤s z≤n)
tri (suc m) (suc n) with tri m n
... | tri< p = tri< (s≤s p)
... | tri≡ p = tri≡ (cong suc p)
... | tri> p = tri> (s≤s p)

<-irrefl : ∀ {n} → n < n → ⊥
<-irrefl {suc n} (s≤s p) = <-irrefl p

≤-<-⊥ : ∀ {m n} → m ≤ n → n < m → ⊥
≤-<-⊥ z≤n     ()
≤-<-⊥ (s≤s p) (s≤s q) = ≤-<-⊥ p q

------------------------------------------------------------------------
-- Uniqueness of identity proofs (the library is --safe with K).

uip : ∀ {a} {A : Set a} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

------------------------------------------------------------------------
-- The structure.

record ωCat : Set₁ where
  field
    C    : Set
    src  : Nat → C → C
    tgt  : Nat → C → C
    comp : ∀ n (x y : C) → tgt n x ≡ src n y → C

    -- (i) boundaries of boundaries
    src-src-< : ∀ {m n} x → m < n → src m (src n x) ≡ src m x
    src-tgt-< : ∀ {m n} x → m < n → src m (tgt n x) ≡ src m x
    tgt-src-< : ∀ {m n} x → m < n → tgt m (src n x) ≡ tgt m x
    tgt-tgt-< : ∀ {m n} x → m < n → tgt m (tgt n x) ≡ tgt m x
    src-src-≥ : ∀ {m n} x → n ≤ m → src m (src n x) ≡ src n x
    tgt-src-≥ : ∀ {m n} x → n ≤ m → tgt m (src n x) ≡ src n x
    src-tgt-≥ : ∀ {m n} x → n ≤ m → src m (tgt n x) ≡ tgt n x
    tgt-tgt-≥ : ∀ {m n} x → n ≤ m → tgt m (tgt n x) ≡ tgt n x

    -- (iii) boundaries of composites
    src-comp : ∀ n x y p → src n (comp n x y p) ≡ src n x
    tgt-comp : ∀ n x y p → tgt n (comp n x y p) ≡ tgt n y
    src-comp-< : ∀ {m n} x y p → m < n → src m (comp n x y p) ≡ src m x
    tgt-comp-< : ∀ {m n} x y p → m < n → tgt m (comp n x y p) ≡ tgt m y
    src-comp-> : ∀ {m n} x y p → n < m → ∀ q → src m (comp n x y p) ≡ comp n (src m x) (src m y) q
    tgt-comp-> : ∀ {m n} x y p → n < m → ∀ q → tgt m (comp n x y p) ≡ comp n (tgt m x) (tgt m y) q

    -- (iv) units
    unit-l : ∀ n x p → comp n (src n x) x p ≡ x
    unit-r : ∀ n x p → comp n x (tgt n x) p ≡ x

    -- (v) associativity
    assoc : ∀ n x y z p q p′ q′ → comp n (comp n x y p) z q ≡ comp n x (comp n y z p′) q′

    -- (vi) interchange
    interchange : ∀ {m n} x y z w → m < n → ∀ p q r r₁ r₂ r₃ →
                  comp m (comp n x y p) (comp n z w q) r ≡ comp n (comp m x z r₁) (comp m y w r₂) r₃

------------------------------------------------------------------------
-- Basic consequences.

module Basics (𝒞 : ωCat) where
  open ωCat 𝒞

  comp-cong : ∀ n {x x′ y y′} (p : tgt n x ≡ src n y) (p′ : tgt n x′ ≡ src n y′) →
              x ≡ x′ → y ≡ y′ → comp n x y p ≡ comp n x′ y′ p′
  comp-cong n p p′ refl refl = cong (comp n _ _) (uip p p′)

  -- A cell of dimension ≤ k.
  Dim≤ : Nat → C → Set
  Dim≤ k x = src k x ≡ x

  tgt-of-dim : ∀ {k x} → Dim≤ k x → tgt k x ≡ x
  tgt-of-dim {k} {x} d = trans (cong (tgt k) (sym d)) (trans (tgt-src-≥ x (≤-refl k)) d)

  dim-up : ∀ {k j x} → k ≤ j → Dim≤ k x → Dim≤ j x
  dim-up {k} {j} {x} le d = trans (cong (src j) (sym d)) (trans (src-src-≥ x le) d)

  dim-tgt-up : ∀ {k j x} → k ≤ j → Dim≤ k x → tgt j x ≡ x
  dim-tgt-up {k} {j} {x} le d = trans (cong (tgt j) (sym d)) (trans (tgt-src-≥ x le) d)

  src-dim : ∀ k x → Dim≤ k (src k x)
  src-dim k x = src-src-≥ x (≤-refl k)

  tgt-dim : ∀ k x → Dim≤ k (tgt k x)
  tgt-dim k x = src-tgt-≥ x (≤-refl k)
