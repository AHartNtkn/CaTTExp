------------------------------------------------------------------------
-- Arithmetic on Nat for the Steiner-complex model (S1).
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Steiner.Arith where

open import CaTTExp.Prelude
open import Agda.Builtin.Nat public using (_*_)

infixr 1 _⊎_
data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

+-zero : ∀ a → a + 0 ≡ a
+-zero zero    = refl
+-zero (suc a) = cong suc (+-zero a)

+-suc : ∀ a b → a + suc b ≡ suc (a + b)
+-suc zero    b = refl
+-suc (suc a) b = cong suc (+-suc a b)

+-comm : ∀ a b → a + b ≡ b + a
+-comm zero    b = sym (+-zero b)
+-comm (suc a) b = trans (cong suc (+-comm a b)) (sym (+-suc b a))

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

+-cancelˡ : ∀ a {b c} → a + b ≡ a + c → b ≡ c
+-cancelˡ zero    e = e
+-cancelˡ (suc a) e = +-cancelˡ a (suc-inj e)
  where suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
        suc-inj refl = refl

+-cancelʳ : ∀ {a b} c → a + c ≡ b + c → a ≡ b
+-cancelʳ {a} {b} c e = +-cancelˡ c (trans (+-comm c a) (trans e (+-comm b c)))

-- (a + b) + (c + d) ≡ (a + c) + (b + d)
+-inter : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-inter a b c d =
  trans (+-assoc a b (c + d))
  (trans (cong (a +_) (trans (sym (+-assoc b c d)) (trans (cong (_+ d) (+-comm b c)) (+-assoc c b d))))
         (sym (+-assoc a c (b + d))))

*-zero : ∀ a → a * 0 ≡ 0
*-zero zero    = refl
*-zero (suc a) = *-zero a

*-one : ∀ a → a * 1 ≡ a
*-one zero    = refl
*-one (suc a) = cong suc (*-one a)

one-* : ∀ a → 1 * a ≡ a
one-* a = +-zero a

*-suc : ∀ a b → a * suc b ≡ a + a * b
*-suc zero    b = refl
*-suc (suc a) b = cong suc (trans (cong (b +_) (*-suc a b))
                   (trans (sym (+-assoc b a (a * b))) (trans (cong (_+ a * b) (+-comm b a)) (+-assoc a b (a * b)))))

*-comm : ∀ a b → a * b ≡ b * a
*-comm zero    b = sym (*-zero b)
*-comm (suc a) b = trans (cong (b +_) (*-comm a b)) (sym (*-suc b a))

distribʳ : ∀ a b c → (a + b) * c ≡ a * c + b * c
distribʳ zero    b c = refl
distribʳ (suc a) b c = trans (cong (c +_) (distribʳ a b c)) (sym (+-assoc c (a * c) (b * c)))

distribˡ : ∀ a b c → a * (b + c) ≡ a * b + a * c
distribˡ a b c = trans (*-comm a (b + c)) (trans (distribʳ b c a) (cong₂ _+_ (*-comm b a) (*-comm c a)))

*-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
*-assoc zero    b c = refl
*-assoc (suc a) b c = trans (distribʳ b (a * b) c) (cong (b * c +_) (*-assoc a b c))

-- Decidable equality of Nat, as a Bool with soundness.
==-sound : ∀ m n → T (m ==ℕ n) → m ≡ n
==-sound zero    zero    _ = refl
==-sound zero    (suc n) ()
==-sound (suc m) zero    ()
==-sound (suc m) (suc n) p = cong suc (==-sound m n p)

==-refl : ∀ n → T (n ==ℕ n)
==-refl zero    = tt
==-refl (suc n) = ==-refl n

==-false : ∀ m n → (m ==ℕ n) ≡ false → m ≡ n → ⊥
==-false m .m e refl = go (m ==ℕ m) (==-refl m) e
  where go : ∀ b → T b → b ≡ false → ⊥
        go true  _ ()
        go false () _

-- Irrelevance of T-proofs.
T-irr : ∀ {b} (p q : T b) → p ≡ q
T-irr {true}  p q = refl
T-irr {false} () q
