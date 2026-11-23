------------------------------------------------------------------------
-- Finite sums over lists, and finite types with an enumeration (S1).
--
-- `Enum A` lists every element of A exactly once (`count`), with a
-- decidable equality. The Kronecker delta δ a x of such a type picks
-- out one term of a sum (`Σ-δ`). Finite types are closed under ⊤,
-- Fin n and products.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Steiner.Sum where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith

------------------------------------------------------------------------
-- Sums.

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

Σl : ∀ {A : Set} → List A → (A → Nat) → Nat
Σl []       f = 0
Σl (x ∷ xs) f = f x + Σl xs f

module _ {A : Set} where
  Σ-cong : ∀ (xs : List A) {f g : A → Nat} → (∀ x → f x ≡ g x) → Σl xs f ≡ Σl xs g
  Σ-cong []       e = refl
  Σ-cong (x ∷ xs) e = cong₂ _+_ (e x) (Σ-cong xs e)

  Σ-0 : ∀ (xs : List A) → Σl xs (λ _ → 0) ≡ 0
  Σ-0 []       = refl
  Σ-0 (x ∷ xs) = Σ-0 xs

  Σ-+ : ∀ (xs : List A) (f g : A → Nat) → Σl xs (λ x → f x + g x) ≡ Σl xs f + Σl xs g
  Σ-+ []       f g = refl
  Σ-+ (x ∷ xs) f g = trans (cong (f x + g x +_) (Σ-+ xs f g)) (+-inter (f x) (g x) (Σl xs f) (Σl xs g))

  Σ-*ˡ : ∀ (xs : List A) a (f : A → Nat) → a * Σl xs f ≡ Σl xs (λ x → a * f x)
  Σ-*ˡ []       a f = *-zero a
  Σ-*ˡ (x ∷ xs) a f = trans (distribˡ a (f x) (Σl xs f)) (cong (a * f x +_) (Σ-*ˡ xs a f))

  Σ-*ʳ : ∀ (xs : List A) a (f : A → Nat) → Σl xs f * a ≡ Σl xs (λ x → f x * a)
  Σ-*ʳ xs a f = trans (*-comm (Σl xs f) a) (trans (Σ-*ˡ xs a f) (Σ-cong xs (λ x → *-comm a (f x))))

  Σ-++ : ∀ (xs ys : List A) (f : A → Nat) → Σl (xs ++ ys) f ≡ Σl xs f + Σl ys f
  Σ-++ []       ys f = refl
  Σ-++ (x ∷ xs) ys f = trans (cong (f x +_) (Σ-++ xs ys f)) (sym (+-assoc (f x) (Σl xs f) (Σl ys f)))

Σ-map : ∀ {A B : Set} (g : A → B) (xs : List A) (f : B → Nat) → Σl (map g xs) f ≡ Σl xs (λ x → f (g x))
Σ-map g []       f = refl
Σ-map g (x ∷ xs) f = cong (f (g x) +_) (Σ-map g xs f)

module _ {A B : Set} where

  Σ-swap : ∀ (xs : List A) (ys : List B) (f : A → B → Nat) →
           Σl xs (λ x → Σl ys (f x)) ≡ Σl ys (λ y → Σl xs (λ x → f x y))
  Σ-swap []       ys f = sym (Σ-0 ys)
  Σ-swap (x ∷ xs) ys f =
    trans (cong (Σl ys (f x) +_) (Σ-swap xs ys f))
          (sym (Σ-+ ys (f x) (λ y → Σl xs (λ x′ → f x′ y))))

  pairs : List A → List B → List (A × B)
  pairs []       ys = []
  pairs (x ∷ xs) ys = map (x ,_) ys ++ pairs xs ys

  Σ-pairs : ∀ (xs : List A) (ys : List B) (f : A × B → Nat) →
            Σl (pairs xs ys) f ≡ Σl xs (λ x → Σl ys (λ y → f (x , y)))
  Σ-pairs []       ys f = refl
  Σ-pairs (x ∷ xs) ys f =
    trans (Σ-++ (map (x ,_) ys) (pairs xs ys) f)
          (cong₂ _+_ (Σ-map (x ,_) ys f) (Σ-pairs xs ys f))

------------------------------------------------------------------------
-- Finite types.

record Enum (A : Set) : Set where
  field
    els      : List A
    eqb      : A → A → Bool
    eqb-sound : ∀ {x y} → T (eqb x y) → x ≡ y
    eqb-refl  : ∀ x → T (eqb x x)

  δ : A → A → Nat
  δ x y = if eqb x y then 1 else 0

  field
    count : ∀ a → Σl els (δ a) ≡ 1

  private
    δ-false : ∀ {x y} → x ≡ y → ∀ b → eqb x y ≡ b → T b
    δ-false {x} refl b e = subst T e (eqb-refl x)

  δ-refl : ∀ x → δ x x ≡ 1
  δ-refl x = go (eqb x x) (eqb-refl x)
    where go : ∀ b → T b → (if b then 1 else 0) ≡ 1
          go true _ = refl
          go false ()

  -- δ x y * f y ≡ δ x y * f x
  δ-shift : ∀ x y (f : A → Nat) → δ x y * f y ≡ δ x y * f x
  δ-shift x y f = go (eqb x y) refl
    where go : ∀ b → eqb x y ≡ b → (if eqb x y then 1 else 0) * f y ≡ (if eqb x y then 1 else 0) * f x
          go true  e with eqb-sound {x} {y} (subst T (sym e) tt)
          ... | refl = refl
          go false e rewrite e = refl

  δ-sym : ∀ x y → δ x y ≡ δ y x
  δ-sym x y = go (eqb x y) (eqb y x) refl refl
    where go : ∀ b c → eqb x y ≡ b → eqb y x ≡ c → (if eqb x y then 1 else 0) ≡ (if eqb y x then 1 else 0)
          go true  c e e′ with eqb-sound {x} {y} (subst T (sym e) tt)
          ... | refl = refl
          go false true  e e′ with eqb-sound {y} {x} (subst T (sym e′) tt)
          ... | refl = refl
          go false false e e′ rewrite e | e′ = refl

  Σ-δ : ∀ a (f : A → Nat) → Σl els (λ x → δ a x * f x) ≡ f a
  Σ-δ a f =
    trans (Σ-cong els (λ x → δ-shift a x f))
    (trans (sym (Σ-*ʳ els (f a) (δ a)))
    (trans (cong (_* f a) (count a)) (+-zero (f a))))

  Σ-δʳ : ∀ a (f : A → Nat) → Σl els (λ x → f x * δ x a) ≡ f a
  Σ-δʳ a f = trans (Σ-cong els (λ x → trans (*-comm (f x) (δ x a)) (cong (_* f x) (δ-sym x a)))) (Σ-δ a f)

open Enum public

-- The unit type.
enum⊤ : Enum ⊤
enum⊤ = record { els = tt ∷ [] ; eqb = λ _ _ → true ; eqb-sound = λ _ → refl
               ; eqb-refl = λ _ → tt ; count = λ _ → refl }

-- Fin n.
data Fin : Nat → Set where
  fz : ∀ {n} → Fin (suc n)
  fs : ∀ {n} → Fin n → Fin (suc n)

toℕ : ∀ {n} → Fin n → Nat
toℕ fz     = 0
toℕ (fs i) = suc (toℕ i)

allFin : ∀ n → List (Fin n)
allFin zero    = []
allFin (suc n) = fz ∷ map fs (allFin n)

eqFin : ∀ {n} → Fin n → Fin n → Bool
eqFin fz     fz     = true
eqFin fz     (fs _) = false
eqFin (fs _) fz     = false
eqFin (fs i) (fs j) = eqFin i j

eqFin-sound : ∀ {n} {i j : Fin n} → T (eqFin i j) → i ≡ j
eqFin-sound {i = fz}   {fz}   _ = refl
eqFin-sound {i = fz}   {fs j} ()
eqFin-sound {i = fs i} {fz}   ()
eqFin-sound {i = fs i} {fs j} p = cong fs (eqFin-sound p)

eqFin-refl : ∀ {n} (i : Fin n) → T (eqFin i i)
eqFin-refl fz     = tt
eqFin-refl (fs i) = eqFin-refl i

private
  δF : ∀ {n} → Fin n → Fin n → Nat
  δF i j = if eqFin i j then 1 else 0

  countFin : ∀ {n} (a : Fin n) → Σl (allFin n) (δF a) ≡ 1
  countFin {suc n} fz     = cong suc (trans (Σ-map fs (allFin n) (δF fz)) (Σ-0 (allFin n)))
  countFin {suc n} (fs a) = trans (Σ-map fs (allFin n) (δF (fs a))) (countFin a)

enumFin : ∀ n → Enum (Fin n)
enumFin n = record { els = allFin n ; eqb = eqFin ; eqb-sound = eqFin-sound
                   ; eqb-refl = eqFin-refl ; count = countFin }

-- Products.
module _ {A B : Set} (EA : Enum A) (EB : Enum B) where
  private
    module A = Enum EA
    module B = Enum EB

    eqP : A × B → A × B → Bool
    eqP (a , b) (a′ , b′) = A.eqb a a′ ∧ B.eqb b b′

    eqP-sound : ∀ {p q} → T (eqP p q) → p ≡ q
    eqP-sound {a , b} {a′ , b′} t with A.eqb-sound {a} {a′} (∧-fst t) | B.eqb-sound {b} {b′} (∧-snd {A.eqb a a′} t)
    ... | refl | refl = refl

    ∧I : ∀ {x y} → T x → T y → T (x ∧ y)
    ∧I {true} _ q = q

    eqP-refl : ∀ p → T (eqP p p)
    eqP-refl (a , b) = ∧I (A.eqb-refl a) (B.eqb-refl b)

    if∧ : ∀ x y → (if (x ∧ y) then 1 else 0) ≡ (if x then 1 else 0) * (if y then 1 else 0)
    if∧ true  true  = refl
    if∧ true  false = refl
    if∧ false y     = refl

  δ× : ∀ a b a′ b′ → (if eqP (a , b) (a′ , b′) then 1 else 0) ≡ A.δ a a′ * B.δ b b′
  δ× a b a′ b′ = if∧ (A.eqb a a′) (B.eqb b b′)

  private
    countP : ∀ p → Σl (pairs A.els B.els) (λ q → if eqP p q then 1 else 0) ≡ 1
    countP (a , b) =
      trans (Σ-pairs A.els B.els _)
      (trans (Σ-cong A.els (λ x → trans (Σ-cong B.els (λ y → δ× a b x y))
                                        (sym (Σ-*ˡ B.els (A.δ a x) (B.δ b)))))
      (trans (Σ-cong A.els (λ x → trans (cong (A.δ a x *_) (B.count b)) (*-one (A.δ a x))))
             (A.count a)))

  enum× : Enum (A × B)
  enum× = record { els = pairs A.els B.els ; eqb = eqP ; eqb-sound = eqP-sound
                 ; eqb-refl = eqP-refl ; count = countP }
