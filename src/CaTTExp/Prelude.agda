------------------------------------------------------------------------
-- A tiny self-contained prelude, so the development does not depend on
-- a particular version of agda-stdlib.
------------------------------------------------------------------------
module CaTTExp.Prelude where

open import Agda.Primitive public using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.Nat public
  using (Nat; zero; suc; _+_)
  renaming (_==_ to _==ℕ_; _-_ to _∸_; _<_ to _<ℕ_)
open import Agda.Builtin.Bool public using (Bool; true; false)
open import Agda.Builtin.Sigma public using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit public using (⊤; tt)
open import Agda.Builtin.List public using (List; []; _∷_)

data ⊥ : Set where

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()

infixr 2 _×_
_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

∃ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
∃ = Σ _

------------------------------------------------------------------------
-- Equality

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y} → x ≡ y → P x → P y
subst P refl px = px

------------------------------------------------------------------------
-- Booleans

infixr 6 _∧_
_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

infixr 5 _∨_
_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ b = b

not : Bool → Bool
not true  = false
not false = true

if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then x else _ = x
if false then _ else y = y

-- Lift a boolean to a proposition: side conditions are decidable by
-- construction.
T : Bool → Set
T true  = ⊤
T false = ⊥

∧-fst : ∀ {a b} → T (a ∧ b) → T a
∧-fst {true} _ = tt

∧-snd : ∀ {a b} → T (a ∧ b) → T b
∧-snd {true} p = p

------------------------------------------------------------------------
-- Natural numbers

max : Nat → Nat → Nat
max zero    n       = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)

==ℕ-sound : ∀ m n → T (m ==ℕ n) → m ≡ n
==ℕ-sound zero    zero    _ = refl
==ℕ-sound (suc m) (suc n) p = cong suc (==ℕ-sound m n p)

==ℕ-refl : ∀ n → T (n ==ℕ n)
==ℕ-refl zero    = tt
==ℕ-refl (suc n) = ==ℕ-refl n

------------------------------------------------------------------------
-- Lists (used as finite sets of de Bruijn levels)

infixr 5 _++_
_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

elem : Nat → List Nat → Bool
elem n []       = false
elem n (m ∷ ms) = (n ==ℕ m) ∨ elem n ms

all : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
all p []       = true
all p (x ∷ xs) = p x ∧ all p xs

filter : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
filter p []       = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

⊆? : List Nat → List Nat → Bool
⊆? xs ys = all (λ x → elem x ys) xs

-- Set equality of finite sets of naturals.
≈? : List Nat → List Nat → Bool
≈? xs ys = ⊆? xs ys ∧ ⊆? ys xs

------------------------------------------------------------------------
-- Maybe

data Maybe {a} (A : Set a) : Set a where
  nothing : Maybe A
  just    : A → Maybe A

infixl 1 _>>=_
_>>=_ : ∀ {a b} {A : Set a} {B : Set b} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= _ = nothing
just x  >>= f = f x

is-just : ∀ {a} {A : Set a} → Maybe A → Bool
is-just nothing  = false
is-just (just _) = true

-- Extract the result of a decision procedure at typechecking time.
from-just : ∀ {a} {A : Set a} (m : Maybe A) → {T (is-just m)} → A
from-just (just x) = x

guard : ∀ {a} {A : Set a} (b : Bool) → (T b → Maybe A) → Maybe A
guard true  k = k tt
guard false _ = nothing
