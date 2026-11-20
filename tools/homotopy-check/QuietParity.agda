{-# OPTIONS --safe --without-K #-}

module QuietParity where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

trans : ∀ {i j k} → i ≤ j → j ≤ k → i ≤ k
trans z≤n _ = z≤n
trans (s≤s p) (s≤s q) = s≤s (trans p q)

max : Nat → Nat → Nat
max zero n = n
max (suc m) zero = suc m
max (suc m) (suc n) = suc (max m n)

refl≤ : ∀ n → n ≤ n
refl≤ zero = z≤n
refl≤ (suc n) = s≤s (refl≤ n)

left : ∀ m n → m ≤ max m n
left zero n = z≤n
left (suc m) zero = refl≤ (suc m)
left (suc m) (suc n) = s≤s (left m n)

right : ∀ m n → n ≤ max m n
right zero n = refl≤ n
right (suc m) zero = z≤n
right (suc m) (suc n) = s≤s (right m n)

-- Scan the tested prefix in index order, giving the even witness priority
-- at an index shared by both sides. Without a candidate the parity is even.
pick : (Nat → Bool) → (Nat → Bool) → Nat → Bool
pick a b zero = true
pick a b (suc n) with a zero | b zero
... | true  | _     = true
... | false | true  = false
... | false | false = pick (λ k → a (suc k)) (λ k → b (suc k)) n

first-even : ∀ a b j n → suc j ≤ n → a j ≡ true →
             (∀ i → i ≤ j → b i ≡ false) → pick a b n ≡ true
first-even a b zero (suc n) _ yes no rewrite yes = refl
first-even a b (suc j) (suc n) (s≤s bound) yes no
  rewrite no zero z≤n with a zero
... | true  = refl
... | false = first-even _ _ j n bound yes (λ i p → no (suc i) (s≤s p))

first-odd : ∀ a b j n → suc j ≤ n → b j ≡ true →
            (∀ i → i ≤ j → a i ≡ false) → pick a b n ≡ false
first-odd a b zero (suc n) _ yes no rewrite no zero z≤n | yes = refl
first-odd a b (suc j) (suc n) (s≤s bound) yes no
  rewrite no zero z≤n with b zero
... | true  = refl
... | false = first-odd _ _ j n bound yes (λ i p → no (suc i) (s≤s p))

Eventually : (Nat → Bool) → Bool → Set
Eventually f value = Σ Nat (λ t → ∀ s → t ≤ s → f s ≡ value)

-- One cutoff simultaneously eliminates every contrary candidate up to j.
uniform : ∀ (b : Nat → Nat → Bool) → (∀ i → Eventually (b i) false) →
          ∀ j → Σ Nat (λ t → ∀ s → t ≤ s → ∀ i → i ≤ j → b i s ≡ false)
uniform b dead zero = fst (dead zero) , λ s p → λ { zero z≤n → snd (dead zero) s p }
uniform b dead (suc j) with uniform (λ i → b (suc i)) (λ i → dead (suc i)) j
... | t , prior = max (fst (dead zero)) t ,
  λ s p → λ { zero z≤n → snd (dead zero) s (trans (left _ t) p)
             ; (suc i) (s≤s q) → prior s (trans (right (fst (dead zero)) t) p) i q }

parity : (Nat → Nat → Bool) → (Nat → Nat → Bool) → Nat → Bool
parity a b s = pick (λ i → a i s) (λ i → b i s) s

quiet-even : ∀ a b j → (∀ s → a j s ≡ true) →
             (∀ i → Eventually (b i) false) → Eventually (parity a b) true
quiet-even a b j alive dead with uniform b dead j
... | t , cut = max (suc j) t , λ s p →
  first-even _ _ j s (trans (left (suc j) t) p) (alive s)
    (cut s (trans (right (suc j) t) p))

quiet-odd : ∀ a b j → (∀ s → b j s ≡ true) →
            (∀ i → Eventually (a i) false) → Eventually (parity a b) false
quiet-odd a b j alive dead with uniform a dead j
... | t , cut = max (suc j) t , λ s p →
  first-odd _ _ j s (trans (left (suc j) t) p) (alive s)
    (cut s (trans (right (suc j) t) p))
