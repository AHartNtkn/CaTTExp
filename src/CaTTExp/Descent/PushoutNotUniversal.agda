------------------------------------------------------------------------
-- Ledger F10 (notes/universe-free-principles.md §3.2).
--
-- Why a descent rule for Cat_ω must be restricted: colimits in Cat
-- are not universal (stable under pullback) along arbitrary functors.
--
-- The standard example (Ayala–Francis, "Fibrations of ∞-categories",
-- Example 1.6): the poset [2] = {a0 < a1 < a2} is the pushout in Cat
-- of {a0 < a1} ← {a1} → {a1 < a2}.  Pull this back along the functor
-- f : [1] → [2], b0 ↦ a0, b1 ↦ a2.  The pullbacks of the three
-- pieces are {b0}, {b1} and ∅, whose pushout is the discrete poset
-- {b0, b1}.  The pullback of [2] itself is [1], which has the arrow
-- b0 ≤ b1.  So the comparison map  {b0} ⊔ {b1} → [1]  is not an
-- isomorphism, and pullback along f does not preserve this pushout.
--
-- What is machine-checked here (all by computation on finite posets,
-- no postulates):
--   (1) the pullbacks of the three pieces along f, as subsets of [1]
--       with the inherited order: {b0}, {b1}, ∅;
--   (2) the coproduct {b0} ⊔ {b1} (disjoint union, no order between
--       summands) admits no order-reflecting bijection to [1] (hence
--       a fortiori no order isomorphism); in particular the canonical
--       comparison map is not one;
--   (3) f fails the Conduché factorisation-lifting condition: b0 ≤ b1
--       and f b0 ≤ a1 ≤ f b1, but no z has f z ≡ a1.
--
-- What is NOT encoded (standard facts, cited): that [2] is the
-- pushout in Cat; that pullbacks along these full-subposet
-- inclusions are the preimage subposets (modelled as predicates);
-- that the pushout of {b0} ← ∅ → {b1} is the coproduct Disc; and the
-- general theorem that exponentiable = Conduché.
-- The positive side (descent for cocartesian fibrations) is a
-- semantic statement cited in the note, not formalised here.
------------------------------------------------------------------------
module CaTTExp.Descent.PushoutNotUniversal where

open import CaTTExp.Prelude

-- The base [2].
data Three : Set where
  a0 a1 a2 : Three

_≤3_ : Three → Three → Bool
a0 ≤3 _  = true
a1 ≤3 a0 = false
a1 ≤3 _  = true
a2 ≤3 a2 = true
a2 ≤3 _  = false

-- The domain [1].
data Two : Set where
  b0 b1 : Two

_≤2_ : Two → Two → Bool
b0 ≤2 _  = true
b1 ≤2 b0 = false
b1 ≤2 b1 = true

-- f : [1] → [2], monotone.
f : Two → Three
f b0 = a0
f b1 = a2

f-monotone : (x y : Two) → T (x ≤2 y) → T (f x ≤3 f y)
f-monotone b0 b0 _ = tt
f-monotone b0 b1 _ = tt
f-monotone b1 b1 _ = tt

-- The three pieces of the pushout, as predicates on [2].
P01 P12 P1 : Three → Bool
P01 a0 = true
P01 a1 = true
P01 a2 = false
P12 a0 = false
P12 a1 = true
P12 a2 = true
P1  a1 = true
P1  _  = false

-- Pullback of a piece along f: the subset of [1] lying over it,
-- with the order inherited from [1].
pb : (Three → Bool) → Two → Bool
pb P x = P (f x)

-- (1) The pullbacks are {b0}, {b1} and ∅.
pb-P01 : (pb P01 b0 ≡ true) × (pb P01 b1 ≡ false)
pb-P01 = refl , refl

pb-P12 : (pb P12 b0 ≡ false) × (pb P12 b1 ≡ true)
pb-P12 = refl , refl

pb-P1 : (pb P1 b0 ≡ false) × (pb P1 b1 ≡ false)
pb-P1 = refl , refl

-- The pushout of {b0} ← ∅ → {b1} is the coproduct {b0} ⊔ {b1}:
-- two points, ordered only within a summand.
data Disc : Set where
  inl-b0 inr-b1 : Disc

_≤D_ : Disc → Disc → Bool
inl-b0 ≤D inl-b0 = true
inr-b1 ≤D inr-b1 = true
_      ≤D _      = false

-- The canonical comparison map to the pullback of [2], i.e. to [1].
comparison : Disc → Two
comparison inl-b0 = b0
comparison inr-b1 = b1

-- An isomorphism of posets: a bijection preserving and reflecting ≤.
record PosetIso : Set where
  field
    to       : Disc → Two
    from     : Two → Disc
    to-from  : (y : Two) → to (from y) ≡ y
    from-to  : (x : Disc) → from (to x) ≡ x
    reflects : (x y : Disc) → T (to x ≤2 to y) → T (x ≤D y)

-- (2) No such isomorphism exists.  Whatever the bijection does, the
-- preimages of b0 and b1 are distinct points of Disc, and in [1]
-- b0 ≤ b1; reflection would make two distinct points of Disc
-- comparable, which never happens.
private
  distinct-incomparable : (x y : Disc) → T (x ≤D y) → x ≡ y
  distinct-incomparable inl-b0 inl-b0 _ = refl
  distinct-incomparable inr-b1 inr-b1 _ = refl

  b0≢b1 : b0 ≡ b1 → ⊥
  b0≢b1 ()

no-iso : PosetIso → ⊥
no-iso i = b0≢b1 b0≡b1
  where
  open PosetIso i
  -- to (from b0) = b0 ≤ b1 = to (from b1)
  le : T (to (from b0) ≤2 to (from b1))
  le = subst (λ u → T (u ≤2 to (from b1))) (sym (to-from b0))
         (subst (λ v → T (b0 ≤2 v)) (sym (to-from b1)) tt)
  same : from b0 ≡ from b1
  same = distinct-incomparable (from b0) (from b1) (reflects (from b0) (from b1) le)
  b0≡b1 : b0 ≡ b1
  b0≡b1 = trans (sym (to-from b0)) (trans (cong to same) (to-from b1))

-- In particular the comparison map is not an isomorphism.
comparison-not-iso : (i : PosetIso) → PosetIso.to i ≡ comparison → ⊥
comparison-not-iso i _ = no-iso i

-- (3) Conduché fails: the factorisation a0 ≤ a1 ≤ a2 of f b0 ≤ f b1
-- has no lift, because nothing in [1] lies over a1.
no-lift : (z : Two) → f z ≡ a1 → ⊥
no-lift b0 ()
no-lift b1 ()

conduche-fails :
  T (b0 ≤2 b1) × T (f b0 ≤3 a1) × T (a1 ≤3 f b1)
  × ((z : Two) → T (b0 ≤2 z) → T (z ≤2 b1) → f z ≡ a1 → ⊥)
conduche-fails = tt , tt , tt , (λ z _ _ → no-lift z)
