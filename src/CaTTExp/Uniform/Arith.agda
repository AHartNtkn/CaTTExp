------------------------------------------------------------------------
-- Natural-number lemmas for the uniform-L checker.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (Dec; yes; no)
open import CaTTExp.Join.Finite using (_≤_; z≤n; s≤s)

module CaTTExp.Uniform.Arith where

open import Agda.Builtin.Nat using (_*_)
open Agda.Builtin.Nat using (_*_) public

_≟N_ : (a b : Nat) → Dec (a ≡ b)
zero  ≟N zero  = yes refl
zero  ≟N suc b = no λ ()
suc a ≟N zero  = no λ ()
suc a ≟N suc b with a ≟N b
... | yes refl = yes refl
... | no ne    = no λ { refl → ne refl }

+-zero : ∀ a → a + zero ≡ a
+-zero zero    = refl
+-zero (suc a) = cong suc (+-zero a)

+-suc : ∀ a b → a + suc b ≡ suc (a + b)
+-suc zero    b = refl
+-suc (suc a) b = cong suc (+-suc a b)

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

+-comm : ∀ a b → a + b ≡ b + a
+-comm zero    b = sym (+-zero b)
+-comm (suc a) b = trans (cong suc (+-comm a b)) (sym (+-suc b a))

swap-mid : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
swap-mid a b c d =
  trans (+-assoc a b (c + d))
    (trans (cong (a +_) (trans (sym (+-assoc b c d))
                          (trans (cong (_+ d) (+-comm b c)) (+-assoc c b d))))
           (sym (+-assoc a c (b + d))))

*-distribʳ : ∀ a b c → (a + b) * c ≡ a * c + b * c
*-distribʳ zero    b c = refl
*-distribʳ (suc a) b c = trans (cong (c +_) (*-distribʳ a b c)) (sym (+-assoc c (a * c) (b * c)))

*-distribˡ : ∀ a b c → a * (b + c) ≡ a * b + a * c
*-distribˡ zero    b c = refl
*-distribˡ (suc a) b c =
  trans (cong ((b + c) +_) (*-distribˡ a b c)) (swap-mid b c (a * b) (a * c))

≤-refl : ∀ {a} → a ≤ a
≤-refl {zero}  = z≤n
≤-refl {suc a} = s≤s ≤-refl

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-sucʳ : ∀ {a b} → a ≤ b → a ≤ suc b
≤-sucʳ z≤n     = z≤n
≤-sucʳ (s≤s p) = s≤s (≤-sucʳ p)

≤-+ʳ : ∀ a b → a ≤ a + b
≤-+ʳ zero    b = z≤n
≤-+ʳ (suc a) b = s≤s (≤-+ʳ a b)

≤-+ˡ : ∀ a b → b ≤ a + b
≤-+ˡ zero    b = ≤-refl
≤-+ˡ (suc a) b = ≤-sucʳ (≤-+ˡ a b)
