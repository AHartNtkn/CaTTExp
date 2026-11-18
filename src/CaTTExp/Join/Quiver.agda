------------------------------------------------------------------------
-- Paths in an arbitrary quiver, and injectivity of supports.
--
-- G is any quiver (V : Set, G : V → V → Set): no finiteness and no
-- decidable equality is assumed. The support of a path is the pair
-- (vertices it visits, generating arrows it uses), both as
-- proof-relevant memberships. The main result:
--
--   supp-inj : in an acyclic quiver, two paths with the same support
--              are equal (with the same endpoints).
--
-- This is the support claim (4) of the round-7 completion theorem
-- (notes/conjectures/answered/directed-interchange-every-level-r7-...
-- §1, "Injective supports"), for every acyclic quiver at once.
------------------------------------------------------------------------
open import CaTTExp.Prelude

module CaTTExp.Join.Quiver where

------------------------------------------------------------------------
-- Small logic kit (the prelude has none of these).

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : ¬ A → Dec A

------------------------------------------------------------------------
-- Paths, in diagrammatic order: g ∷ p is "g, then p".

module _ {V : Set} (G : V → V → Set) where

  infixr 5 _∷_
  data Path : V → V → Set where
    []  : ∀ {a} → Path a a
    _∷_ : ∀ {a b c} → G a b → Path b c → Path a c

module _ {V : Set} {G : V → V → Set} where

  infixr 5 _++ᵖ_
  _++ᵖ_ : ∀ {a b c} → Path G a b → Path G b c → Path G a c
  []      ++ᵖ q = q
  (g ∷ p) ++ᵖ q = g ∷ (p ++ᵖ q)

  ++ᵖ-[] : ∀ {a b} (p : Path G a b) → p ++ᵖ [] ≡ p
  ++ᵖ-[] []      = refl
  ++ᵖ-[] (g ∷ p) = cong (g ∷_) (++ᵖ-[] p)

  ++ᵖ-assoc : ∀ {a b c d} (p : Path G a b) (q : Path G b c) (r : Path G c d) →
              (p ++ᵖ q) ++ᵖ r ≡ p ++ᵖ (q ++ᵖ r)
  ++ᵖ-assoc []      q r = refl
  ++ᵖ-assoc (g ∷ p) q r = cong (g ∷_) (++ᵖ-assoc p q r)

  len : ∀ {a b} → Path G a b → Nat
  len []      = 0
  len (_ ∷ p) = suc (len p)

  -- Vertices visited: the source, and every vertex after it.
  data _∈V_ (x : V) : ∀ {a b} → Path G a b → Set where
    src  : ∀ {b} {p : Path G x b} → x ∈V p
    next : ∀ {a c b} {g : G a c} {p : Path G c b} → x ∈V p → x ∈V (g ∷ p)

  -- Generating arrows used.
  data _∈E_ {x y : V} (h : G x y) : ∀ {a b} → Path G a b → Set where
    here  : ∀ {b} {p : Path G y b} → h ∈E (h ∷ p)
    there : ∀ {a c b} {g : G a c} {p : Path G c b} → h ∈E p → h ∈E (g ∷ p)

  -- A visited vertex splits the path.
  split-V : ∀ {x a b} {p : Path G a b} → x ∈V p → Path G a x × Path G x b
  split-V {p = p} src = [] , p
  split-V {p = g ∷ p} (next m) with split-V m
  ... | p₁ , p₂ = g ∷ p₁ , p₂

  -- A used arrow splits the path.
  split-E : ∀ {x y a b} {h : G x y} {p : Path G a b} → h ∈E p →
            Path G a x × Path G y b
  split-E {p = _ ∷ p} here = [] , p
  split-E {p = g ∷ p} (there m) with split-E m
  ... | p₁ , p₂ = g ∷ p₁ , p₂

  -- A closed path that is empty forces its two halves' endpoints equal.
  ++ᵖ-nil : ∀ {a b} (p : Path G a b) (q : Path G b a) → p ++ᵖ q ≡ [] → a ≡ b
  ++ᵖ-nil []      q _  = refl
  ++ᵖ-nil (g ∷ p) q ()

------------------------------------------------------------------------
-- Acyclic quivers: every closed path is empty.

module Acyclic {V : Set} (G : V → V → Set)
               (acyc : ∀ {a} (p : Path G a a) → p ≡ []) where

  -- A nonempty closed path does not exist.
  no-loop : ∀ {a c} (g : G a c) (p : Path G c a) → ⊥
  no-loop g p with acyc (g ∷ p)
  ... | ()

  -- An arrow out of a is never followed by a return to a.
  back-V : ∀ {a c b} (g : G a c) {p : Path G c b} → a ∈V p → ⊥
  back-V g m = no-loop g (fst (split-V m))

  back-E : ∀ {a c b x} (g : G a c) {h : G a x} {p : Path G c b} → h ∈E p → ⊥
  back-E g m = no-loop g (fst (split-E m))

  Tot : Set
  Tot = Σ V λ a → Σ V λ b → Path G a b

  SameSupp : ∀ {a b a′ b′} → Path G a b → Path G a′ b′ → Set
  SameSupp p q =
    (∀ {x} → x ∈V p → x ∈V q) × (∀ {x} → x ∈V q → x ∈V p) ×
    (∀ {x y} {h : G x y} → h ∈E p → h ∈E q) ×
    (∀ {x y} {h : G x y} → h ∈E q → h ∈E p)

  -- Same source first.
  private
    inj-src : ∀ {a b b′} (p : Path G a b) (q : Path G a b′) → SameSupp p q →
              _≡_ {A = Tot} (a , b , p) (a , b′ , q)
    inj-src []      []      _ = refl
    inj-src []      (h ∷ q) (_ , _ , _ , eq) with eq here
    ... | ()
    inj-src (g ∷ p) []      (_ , _ , ep , _) with ep here
    ... | ()
    inj-src (g ∷ p) (h ∷ q) (vp , vq , ep , eq) with ep here
    ... | there m = ⊥-elim (back-E h m)
    ... | here with inj-src p q (vp′ , vq′ , ep′ , eq′)
      where
      vp′ : ∀ {x} → x ∈V p → x ∈V q
      vp′ m with vp (next m)
      ... | src     = ⊥-elim (back-V g m)
      ... | next m′ = m′
      vq′ : ∀ {x} → x ∈V q → x ∈V p
      vq′ m with vq (next m)
      ... | src     = ⊥-elim (back-V g m)
      ... | next m′ = m′
      ep′ : ∀ {x y} {k : G x y} → k ∈E p → k ∈E q
      ep′ m with ep (there m)
      ... | here     = ⊥-elim (back-E g m)
      ... | there m′ = m′
      eq′ : ∀ {x y} {k : G x y} → k ∈E q → k ∈E p
      eq′ m with eq (there m)
      ... | here     = ⊥-elim (back-E g m)
      ... | there m′ = m′
    ...   | refl = refl

  -- Supports determine paths: (4) of the completion theorem, generically.
  supp-inj : ∀ {a b a′ b′} (p : Path G a b) (q : Path G a′ b′) → SameSupp p q →
             _≡_ {A = Tot} (a , b , p) (a′ , b′ , q)
  supp-inj {a} {b} {a′} p q s@(vp , vq , _) with vp src | vq src
  ... | ma | ma′ with split-V ma | split-V ma′
  ...   | r , _ | r′ , _ with ++ᵖ-nil r r′ (acyc (r ++ᵖ r′))
  ...     | refl = inj-src p q s
