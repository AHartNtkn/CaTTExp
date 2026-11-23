------------------------------------------------------------------------
-- Ledger F12c (notes/coinductive.md §4, Model D).
--
-- Universality of finite coproducts is not derivable from the non-DESC
-- rules.  The model is the Artin gluing Gl(T) of Set along the
-- finite-product-preserving functor  T : Set → 2,  T(X) = "X is
-- inhabited", which does not preserve pullbacks.  Concretely an object
-- is a set X with a flag y ∈ {false, true}, where y = true comes with a
-- witness of inhabitation; a map (X, y) → (X′, y′) is a function with
-- y ≤ y′.  With discrete homs (all higher cells identities) it is a
-- locally discrete model of the pattern of notes/descent-vs-init.md §3.
--
-- Machine-checked (no postulates, pointwise equality of maps):
--   * category laws;
--   * terminal object 𝟙 = (⊤, true) and binary products
--     (X × X′, y ∧ y′) with their universal property;
--   * cartesian closure: for objects A, B and a decision of whether
--     X_B^{X_A} is inhabited (classically always available; supplied
--     as an argument), an exponential with curry/uncurry inverse up to
--     pointwise equality;
--   * binary coproducts (X ⊎ X′, y ∨ y′) with their universal property;
--   * the counterexample to universality: z : 𝟙 → D₀ + 𝟙 hits the
--     first summand D₀ = (⊤, false).  The pullback of the first
--     injection along z is P₁ = (⊤, false), the pullback of the second
--     is P₂ = (⊥, false), each with its universal property, and the
--     comparison  P₁ + P₂ → 𝟙  has no inverse: there is no map
--     𝟙 → P₁ + P₂ at all (`not-universal`);
--   * disjointness, for all objects: an initial object 𝟘 = (⊥, false)
--     (`¡`, `¡-uni`), and for every A, B the pullback of ι₁ and ι₂ of
--     A ⊕ B is 𝟘: every cone factors through 𝟘 (`disjoint`), uniquely
--     (`disjoint-uni`).
--
-- Scope and honesty notes.
--   * NOT encoded: local presentability of Gl(T) (it is the gluing of
--     locally presentable categories along an accessible functor), and
--     hence INIT in this model, nor the other non-DESC rules; these are
--     argued in notes/coinductive.md §4 on the pattern of
--     notes/descent-vs-init.md §3, as for Descent.InitNotDesc.
--   * Equalisers, coequalisers and general pullbacks are not encoded;
--     only the two pullbacks used by the counterexample.
--   * Morphism equality is pointwise equality of the underlying
--     functions; the flag component is a proof of an implication
--     between T-propositions and carries no information.
------------------------------------------------------------------------
module CaTTExp.Descent.GlueNotUniversal where

open import CaTTExp.Prelude

------------------------------------------------------------------------
-- Small helpers

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : ¬ A → Dec A

∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
∧-intro {true} {true} _ _ = tt

∨-inl : ∀ {a b} → T a → T (a ∨ b)
∨-inl {true} _ = tt

∨-inr : ∀ {a b} → T b → T (a ∨ b)
∨-inr {true}  _ = tt
∨-inr {false} p = p

∨-elim : ∀ {a b c} → (T a → T c) → (T b → T c) → T (a ∨ b) → T c
∨-elim {true}  f g p = f tt
∨-elim {false} f g p = g p

inl≢inr : ∀ {A B : Set} {a : A} {b : B} → inl a ≡ inr b → ⊥
inl≢inr ()

------------------------------------------------------------------------
-- The category Gl(T)

record Ob : Set₁ where
  constructor ob
  field
    X : Set
    y : Bool
    w : T y → X
open Ob

record Hom (A B : Ob) : Set where
  constructor hom
  field
    fun  : X A → X B
    flag : T (y A) → T (y B)
open Hom

infix 4 _≈_
_≈_ : ∀ {A B} → Hom A B → Hom A B → Set
f ≈ g = ∀ a → fun f a ≡ fun g a

idH : ∀ {A} → Hom A A
idH = hom (λ a → a) (λ p → p)

infixr 9 _∘_
_∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
g ∘ f = hom (λ a → fun g (fun f a)) (λ p → flag g (flag f p))

idl : ∀ {A B} (f : Hom A B) → idH ∘ f ≈ f
idl f a = refl

idr : ∀ {A B} (f : Hom A B) → f ∘ idH ≈ f
idr f a = refl

assoc : ∀ {A B C D} (h : Hom C D) (g : Hom B C) (f : Hom A B) →
        (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
assoc h g f a = refl

------------------------------------------------------------------------
-- Terminal object and products

𝟙 : Ob
𝟙 = ob ⊤ true (λ _ → tt)

! : ∀ {A} → Hom A 𝟙
! = hom (λ _ → tt) (λ _ → tt)

!-uni : ∀ {A} (f : Hom A 𝟙) → f ≈ !
!-uni f a = refl

_⊗_ : Ob → Ob → Ob
A ⊗ B = ob (X A × X B) (y A ∧ y B)
           (λ p → w A (∧-fst p) , w B (∧-snd {y A} p))

π₁ : ∀ {A B} → Hom (A ⊗ B) A
π₁ = hom fst (λ p → ∧-fst p)

π₂ : ∀ {A B} → Hom (A ⊗ B) B
π₂ {A} = hom snd (λ p → ∧-snd {y A} p)

⟨_,_⟩ : ∀ {W A B} → Hom W A → Hom W B → Hom W (A ⊗ B)
⟨ f , g ⟩ = hom (λ v → fun f v , fun g v) (λ p → ∧-intro (flag f p) (flag g p))

π₁-β : ∀ {W A B} (f : Hom W A) (g : Hom W B) → π₁ {A} {B} ∘ ⟨ f , g ⟩ ≈ f
π₁-β f g v = refl

π₂-β : ∀ {W A B} (f : Hom W A) (g : Hom W B) → π₂ {A} {B} ∘ ⟨ f , g ⟩ ≈ g
π₂-β f g v = refl

pair-uni : ∀ {W A B} (h : Hom W (A ⊗ B)) → h ≈ ⟨ π₁ {A} {B} ∘ h , π₂ {A} {B} ∘ h ⟩
pair-uni h v = refl

------------------------------------------------------------------------
-- Exponentials.  The flag of B^A is  (y A ⇒ y B), cut down to false
-- when X_B^{X_A} is empty; deciding that is the classical input `d`.

imp : Bool → Bool → Bool
imp a b = not a ∨ b

imp-intro : ∀ {a b} → (T a → T b) → T (imp a b)
imp-intro {true}  f = f tt
imp-intro {false} f = tt

imp-elim : ∀ {a b} → T (imp a b) → T a → T b
imp-elim {true} p q = p

eflag : (A B : Ob) → Dec (X A → X B) → Bool
eflag A B (yes _) = imp (y A) (y B)
eflag A B (no  _) = false

ewit : (A B : Ob) (d : Dec (X A → X B)) → T (eflag A B d) → (X A → X B)
ewit A B (yes h) _ = h
ewit A B (no _) ()

evflag : (A B : Ob) (d : Dec (X A → X B)) → T (eflag A B d ∧ y A) → T (y B)
evflag A B (yes _) p = imp-elim {y A} (∧-fst p) (∧-snd {imp (y A) (y B)} p)
evflag A B (no _) ()

cflag : (A B W : Ob) (d : Dec (X A → X B)) (f : X W × X A → X B) →
        (T (y W ∧ y A) → T (y B)) → T (y W) → T (eflag A B d)
cflag A B W (yes _) f fl p = imp-intro {y A} (λ q → fl (∧-intro p q))
cflag A B W (no ¬h) f fl p = ⊥-elim (¬h (λ a → f (w W p , a)))

module Exp (A B : Ob) (d : Dec (X A → X B)) where

  E : Ob
  E = ob (X A → X B) (eflag A B d) (ewit A B d)

  ev : Hom (E ⊗ A) B
  ev = hom (λ { (h , a) → h a }) (evflag A B d)

  curry : ∀ {W} → Hom (W ⊗ A) B → Hom W E
  curry {W} f = hom (λ v a → fun f (v , a)) (cflag A B W d (fun f) (flag f))

  uncurry : ∀ {W} → Hom W E → Hom (W ⊗ A) B
  uncurry {W} g = ev ∘ ⟨ g ∘ π₁ {W} {A} , π₂ {W} {A} ⟩

  β : ∀ {W} (f : Hom (W ⊗ A) B) → uncurry {W} (curry {W} f) ≈ f
  β f (v , a) = refl

  -- η holds pointwise in the inner argument as well (no funext):
  η : ∀ {W} (g : Hom W E) (v : X W) (a : X A) →
      fun (curry {W} (uncurry {W} g)) v a ≡ fun g v a
  η g v a = refl

------------------------------------------------------------------------
-- Coproducts

_⊕_ : Ob → Ob → Ob
A ⊕ B = ob (X A ⊎ X B) (y A ∨ y B)
           (λ p → ∨-elim′ p)
  where
    ∨-elim′ : T (y A ∨ y B) → X A ⊎ X B
    ∨-elim′ p with y A | w A | w B
    ... | true  | wa | wb = inl (wa tt)
    ... | false | wa | wb = inr (wb p)

ι₁ : ∀ {A B} → Hom A (A ⊕ B)
ι₁ = hom inl (λ p → ∨-inl p)

ι₂ : ∀ {A B} → Hom B (A ⊕ B)
ι₂ {A} = hom inr (λ p → ∨-inr {y A} p)

[_,_] : ∀ {A B C} → Hom A C → Hom B C → Hom (A ⊕ B) C
[_,_] {A} f g = hom (λ { (inl a) → fun f a ; (inr b) → fun g b })
                    (∨-elim {y A} (flag f) (flag g))

ι₁-β : ∀ {A B C} (f : Hom A C) (g : Hom B C) → [ f , g ] ∘ ι₁ ≈ f
ι₁-β f g a = refl

ι₂-β : ∀ {A B C} (f : Hom A C) (g : Hom B C) → [ f , g ] ∘ ι₂ ≈ g
ι₂-β f g b = refl

copair-uni : ∀ {A B C} (h : Hom (A ⊕ B) C) → h ≈ [ h ∘ ι₁ , h ∘ ι₂ ]
copair-uni h (inl a) = refl
copair-uni h (inr b) = refl

------------------------------------------------------------------------
-- The counterexample.

D₀ : Ob                    -- (⊤, false)
D₀ = ob ⊤ false (λ ())

Sum : Ob                   -- D₀ + 𝟙 = (⊤ ⊎ ⊤, true)
Sum = D₀ ⊕ 𝟙

z : Hom 𝟙 Sum              -- the point of the first summand
z = hom (λ _ → inl tt) (λ _ → tt)

-- A cone over the cospan  𝟙 → Sum ← C  along a map k : C → Sum.
record Cone (k : ∀ {C} → Hom C Sum) (C W : Ob) : Set where
  field
    p : Hom W 𝟙
    q : Hom W C
    commutes : ∀ v → fun z (fun p v) ≡ fun (k {C}) (fun q v)

-- (1) The pullback of ι₁ : D₀ → Sum along z is P₁ = (⊤, false).
P₁ : Ob
P₁ = ob ⊤ false (λ ())

P₁-p : Hom P₁ 𝟙
P₁-p = hom (λ _ → tt) (λ ())

P₁-q : Hom P₁ D₀
P₁-q = hom (λ _ → tt) (λ ())

P₁-commutes : ∀ v → fun z (fun P₁-p v) ≡ fun (ι₁ {D₀} {𝟙}) (fun P₁-q v)
P₁-commutes v = refl

-- universal property: every cone factors uniquely through P₁
P₁-fact : ∀ {W} → Hom W 𝟙 → Hom W D₀ → Hom W P₁
P₁-fact p q = hom (λ _ → tt) (flag q)

P₁-fact-p : ∀ {W} (p : Hom W 𝟙) (q : Hom W D₀) → P₁-p ∘ P₁-fact p q ≈ p
P₁-fact-p p q v = refl

P₁-fact-q : ∀ {W} (p : Hom W 𝟙) (q : Hom W D₀) → P₁-q ∘ P₁-fact p q ≈ q
P₁-fact-q p q v = refl

P₁-uni : ∀ {W} (h h′ : Hom W P₁) → h ≈ h′
P₁-uni h h′ v = refl

-- (2) The pullback of ι₂ : 𝟙 → Sum along z is P₂ = (⊥, false).
P₂ : Ob
P₂ = ob ⊥ false (λ ())

P₂-fact : ∀ {W} (p : Hom W 𝟙) (q : Hom W 𝟙) →
          (∀ v → fun z (fun p v) ≡ fun (ι₂ {D₀} {𝟙}) (fun q v)) → Hom W P₂
P₂-fact {W} p q c = hom (λ v → ⊥-elim (inl≢inr (c v))) fl
  where
    fl : T (y W) → T false
    fl t = inl≢inr (c (w W t))

P₂-uni : ∀ {W} (h h′ : Hom W P₂) → h ≈ h′
P₂-uni h h′ v = ⊥-elim (fun h v)

-- (3) The comparison P₁ + P₂ → 𝟙 is not invertible: the codomain has
-- flag true, the domain flag false, so there is no map back.
comparison : Hom (P₁ ⊕ P₂) 𝟙
comparison = [ P₁-p , ! ]

not-universal : ¬ Hom 𝟙 (P₁ ⊕ P₂)
not-universal g = flag g tt

-- Initial object 𝟘 = (⊥, false).
𝟘 : Ob
𝟘 = ob ⊥ false (λ ())

¡ : ∀ {A} → Hom 𝟘 A
¡ = hom (λ ()) (λ ())

¡-uni : ∀ {A} (h : Hom 𝟘 A) → h ≈ ¡
¡-uni h ()

-- Coproducts are nonetheless disjoint, for all A and B: every cone
-- W → A, W → B over the two injections of A ⊕ B factors through 𝟘
-- (uniquely, by `¡-uni`-style vacuity), so the pullback of ι₁ and ι₂
-- is 𝟘.  This is the binary case; the nullary case is that 𝟘 is
-- initial (`¡`, `¡-uni`).
disjoint : ∀ {A B W} (a : Hom W A) (b : Hom W B) →
           (∀ v → fun (ι₁ {A} {B}) (fun a v) ≡ fun (ι₂ {A} {B}) (fun b v)) →
           Hom W 𝟘
disjoint {W = W} a b c =
  hom (λ v → inl≢inr (c v)) (λ t → inl≢inr (c (w W t)))

disjoint-uni : ∀ {W} (h h′ : Hom W 𝟘) → h ≈ h′
disjoint-uni h h′ v = ⊥-elim (fun h v)
