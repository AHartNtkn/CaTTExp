------------------------------------------------------------------------
-- List and arithmetic lemmas used by the semantics of the biclosed
-- kernel.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.ListLemmas where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-[] : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-[] []       = refl
++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ []       ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

map-++ : ∀ {A B : Set} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

length-map : ∀ {A B : Set} (f : A → B) (xs : List A) → length (map f xs) ≡ length xs
length-map f []       = refl
length-map f (x ∷ xs) = cong suc (length-map f xs)

-- moving the hinge of a split one step
snoc-hinge : ∀ {A : Set} (xs : List A) y zs → xs ++ y ∷ zs ≡ (xs ++ y ∷ []) ++ zs
snoc-hinge xs y zs = sym (++-assoc xs (y ∷ []) zs)

length-snoc : ∀ {A : Set} (xs : List A) y → length (xs ++ y ∷ []) ≡ suc (length xs)
length-snoc xs y = trans (length-++ xs (y ∷ [])) (+-one (length xs))
  where
  +-one : ∀ n → n + 1 ≡ suc n
  +-one zero    = refl
  +-one (suc n) = cong suc (+-one n)

concatIns-++ : ∀ xs ys → concatIns (xs ++ ys) ≡ concatIns xs ++ concatIns ys
concatIns-++ []       ys = refl
concatIns-++ (x ∷ xs) ys =
  trans (cong (ins x ++_) (concatIns-++ xs ys)) (sym (++-assoc (ins x) (concatIns xs) (concatIns ys)))

------------------------------------------------------------------------
-- Arithmetic

+-zero : ∀ n → n + 0 ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

+-comm : ∀ a b → a + b ≡ b + a
+-comm zero    b = sym (+-zero b)
+-comm (suc a) b = trans (cong suc (+-comm a b)) (sym (+-suc b a))

------------------------------------------------------------------------
-- Splitting a list at a position

-- Split g xs P Q: xs = P ++ Q with P of length g
record Split {A : Set} (g : Nat) (xs P Q : List A) : Set where
  constructor split
  field
    sp-eq  : P ++ Q ≡ xs
    sp-len : length P ≡ g
open Split public

