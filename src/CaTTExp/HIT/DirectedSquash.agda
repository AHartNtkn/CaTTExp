------------------------------------------------------------------------
-- Ledger F11f (notes/higher-inductive.md §4.2, Prop C′, and §2.3).
--
-- (1) Prop C′.  The context  Δ⃗_sq = (X, g : ⊤ → X, sq : π₁ ⇒ π₂),
--     with π₁, π₂ : X × X → X, has a model on the walking idempotent
--     Idem (one object ∗, endomorphisms {1, e}, e ∘ e = e) with
--     g = ∗ and sq = e, and there is NO strong model morphism from the
--     model on the terminal category ⊤ to it.  Hence ⊤ is not the
--     initial model (`one-not-initial`), although ⊤ is a model and
--     receives a morphism from Idem (`idem→one`).
--
-- (2) §2.3, the pseudo collapse.  Under the cartesian (pseudo) reading,
--     an external path constructor over the source A = [1] attaches the
--     commutative square [1] × [1].  Any functor from the commutative
--     square to a category that sends both horizontal edges to
--     identities sends the two vertical edges to the SAME arrow
--     (`collapse`).  So the two meridians are identified and Hom(n, s)
--     receives only one arrow from A; contrast the Gray (lax) square,
--     where they are related by a 2-cell instead.
--
-- Scope and honesty notes.
--   * 1-truncated: categories with hom-sets, strict naturality, and
--     strong model morphisms whose invertible cells are equalities
--     (between 1-categories the only invertible modification is an
--     identity, so the sq-cell is the equation F(sq) ≡ sq').  The
--     ambient statement is about (∞,ω)-categories; there the same
--     argument applies because Idem has no non-identity 2-cells and
--     e is not invertible.  That transfer is NOT formalised.
--   * Naturality of sq : π₁ ⇒ π₂ is stated componentwise: for f : x → x'
--     and g : y → y',  g ∘ sq x y ≡ sq x' y' ∘ f.  This is naturality on
--     C × C, written out; the product category is not built.
--   * NOT proved: that Idem IS the initial model (open, F11e).
--   * (2) encodes only the equations a functor out of the commutative
--     square must satisfy; that the pushout in Cat_ω is the stated
--     localisation is cited in the note, not formalised.
------------------------------------------------------------------------
module CaTTExp.HIT.DirectedSquash where

open import CaTTExp.Prelude
open import CaTTExp.Descent.CocartLemmas using (Cat; Functor)

------------------------------------------------------------------------
-- Models of Δ⃗_sq and strong model morphisms.

record SqModel (C : Cat) : Set where
  open Cat C
  field
    pt  : Ob
    sq  : (x y : Ob) → Hom x y
    nat : ∀ {x x' y y'} (f : Hom x x') (g : Hom y y')
        → g ∘ sq x y ≡ sq x' y' ∘ f

record IsIso (C : Cat) {x y : Cat.Ob C} (f : Cat.Hom C x y) : Set where
  open Cat C
  field
    inv   : Hom y x
    left  : inv ∘ f ≡ id
    right : f ∘ inv ≡ id

record StrongMor (C D : Cat) (M : SqModel C) (N : SqModel D) : Set where
  private
    module M = SqModel M
    module N = SqModel N
  field
    F      : Functor C D
    φ      : Cat.Hom D (Functor.F₀ F M.pt) N.pt
    φ-iso  : IsIso D φ
    sq-cell : ∀ x y → Functor.F₁ F (M.sq x y)
                     ≡ N.sq (Functor.F₀ F x) (Functor.F₀ F y)

------------------------------------------------------------------------
-- The terminal category and its unique model.

One : Cat
One = record
  { Ob = ⊤ ; Hom = λ _ _ → ⊤ ; id = tt ; _∘_ = λ _ _ → tt
  ; idl = λ _ → refl ; idr = λ _ → refl ; assoc = λ _ _ _ → refl }

one-model : SqModel One
one-model = record { pt = tt ; sq = λ _ _ → tt ; nat = λ _ _ → refl }

------------------------------------------------------------------------
-- The walking idempotent.

data IE : Set where
  i e : IE

_·_ : IE → IE → IE
i · f = f
e · _ = e

Idem : Cat
Idem = record
  { Ob = ⊤ ; Hom = λ _ _ → IE ; id = i ; _∘_ = _·_
  ; idl = λ _ → refl
  ; idr = idr' ; assoc = assoc' }
  where
    idr' : ∀ {x y : ⊤} (f : IE) → f · i ≡ f
    idr' i = refl
    idr' e = refl
    assoc' : ∀ {w x y z : ⊤} (h g f : IE) → (h · g) · f ≡ h · (g · f)
    assoc' i g f = refl
    assoc' e g f = refl

idem-model : SqModel Idem
idem-model = record { pt = tt ; sq = λ _ _ → e ; nat = nat' }
  where
    nat' : ∀ {x x' y y' : ⊤} (f g : IE) → g · e ≡ e · f
    nat' f i = refl
    nat' f e = refl

i≢e : i ≡ e → ⊥
i≢e ()

-- Prop C′: no strong morphism from the model on ⊤ to the model on Idem.
no-mor : StrongMor One Idem one-model idem-model → ⊥
no-mor m = i≢e (trans (sym (Functor.F-id F)) (sq-cell tt tt))
  where open StrongMor m

-- Hence the model on ⊤ is not initial: initiality would give a
-- morphism to every model, in particular to the one on Idem.
IsWeaklyInitial : (C : Cat) → SqModel C → Set₁
IsWeaklyInitial C M = (D : Cat) (N : SqModel D) → StrongMor C D M N

one-not-initial : IsWeaklyInitial One one-model → ⊥
one-not-initial h = no-mor (h Idem idem-model)

-- The other direction exists: Idem → ⊤ is a strong morphism.
idem→one : StrongMor Idem One idem-model one-model
idem→one = record
  { F = record { F₀ = λ _ → tt ; F₁ = λ _ → tt
               ; F-id = refl ; F-∘ = λ _ _ → refl }
  ; φ = tt
  ; φ-iso = record { inv = tt ; left = refl ; right = refl }
  ; sq-cell = λ _ _ → refl }

------------------------------------------------------------------------
-- (2) The pseudo collapse (§2.3).
--
-- A functor from the commutative square
--      (0,0) --h0--> (1,0)
--        |v0           |v1
--      (0,1) --h1--> (1,1)
-- to D is given on the generating arrows with the one relation
-- v1 ∘ h0 ≡ h1 ∘ v0 (both equal the diagonal).  Collapsing the ends
-- {0}×A ↦ n and {1}×A ↦ s means h0 ↦ id_n and h1 ↦ id_s.

module Collapse (D : Cat) where
  open Cat D

  collapse : ∀ {n s} (v0 v1 : Hom n s)
           → v1 ∘ id ≡ id ∘ v0          -- the commutative square, ends collapsed
           → v0 ≡ v1
  collapse v0 v1 sq = trans (sym (idl v0)) (trans (sym sq) (idr v1))
