------------------------------------------------------------------------
-- Small self-contained facts used by the N/β/η metatheory (D18):
-- sums, natural-number order and arithmetic, list cancellation,
-- accessibility and the lexicographic order on pairs.
------------------------------------------------------------------------
module CaTTExp.Gray.NBE.Base where

open import CaTTExp.Prelude public

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

------------------------------------------------------------------------
-- Natural numbers

pred : Nat → Nat
pred zero    = zero
pred (suc n) = n

infix 4 _≤_ _<_
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step z≤n     = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s p) = p

≡→≤ : ∀ {m n} → m ≡ n → m ≤ n
≡→≤ refl = ≤-refl

m≤m+n : ∀ m n → m ≤ m + n
m≤m+n zero    n = z≤n
m≤m+n (suc m) n = s≤s (m≤m+n m n)

+-identityʳ : ∀ n → n + zero ≡ n
+-identityʳ zero    = refl
+-identityʳ (suc n) = cong suc (+-identityʳ n)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-assoc : ∀ l m n → (l + m) + n ≡ l + (m + n)
+-assoc zero    m n = refl
+-assoc (suc l) m n = cong suc (+-assoc l m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-identityʳ n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

n≤m+n : ∀ m n → n ≤ m + n
n≤m+n m n = subst (λ k → n ≤ k) (+-comm n m) (m≤m+n n m)

-- (a + b) + (c + d) ≡ (a + c) + (b + d)
+-interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-interchange a b c d =
  trans (+-assoc a b (c + d))
 (trans (cong (a +_) (trans (sym (+-assoc b c d))
                     (trans (cong (_+ d) (+-comm b c)) (+-assoc c b d))))
        (sym (+-assoc a c (b + d))))

+-monoˡ-≤ : ∀ {m n} k → m ≤ n → m + k ≤ n + k
+-monoˡ-≤ k z≤n     = n≤m+n _ k
+-monoˡ-≤ k (s≤s p) = s≤s (+-monoˡ-≤ k p)

+-monoʳ-≤ : ∀ k {m n} → m ≤ n → k + m ≤ k + n
+-monoʳ-≤ zero    p = p
+-monoʳ-≤ (suc k) p = s≤s (+-monoʳ-≤ k p)

+-monoʳ-< : ∀ k {m n} → m < n → k + m < k + n
+-monoʳ-< k {m} {n} p = subst (λ x → x ≤ k + n) (+-suc k m) (+-monoʳ-≤ k p)

+-monoˡ-< : ∀ k {m n} → m < n → m + k < n + k
+-monoˡ-< k p = +-monoˡ-≤ k p

-- Splitting a bound on a sum.
≤-+ˡ : ∀ a b {B} → a + b ≤ B → a ≤ B
≤-+ˡ a b p = ≤-trans (m≤m+n a b) p

≤-+ʳ : ∀ a b {B} → a + b ≤ B → b ≤ B
≤-+ʳ a b p = ≤-trans (n≤m+n a b) p

------------------------------------------------------------------------
-- Lists

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

map-++ : ∀ {A B : Set} (f : A → B) xs ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

map-∘ : ∀ {A B C : Set} (f : B → C) (g : A → B) xs → map f (map g xs) ≡ map (λ x → f (g x)) xs
map-∘ f g []       = refl
map-∘ f g (x ∷ xs) = cong (f (g x) ∷_) (map-∘ f g xs)

map-ext : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → ∀ xs → map f xs ≡ map g xs
map-ext h []       = refl
map-ext h (x ∷ xs) = cong₂ _∷_ (h x) (map-ext h xs)

map-id : ∀ {A : Set} {f : A → A} → (∀ x → f x ≡ x) → ∀ xs → map f xs ≡ xs
map-id h []       = refl
map-id h (x ∷ xs) = cong₂ _∷_ (h x) (map-id h xs)

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ []       = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

∷-injˡ : ∀ {A : Set} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷-injˡ refl = refl

∷-injʳ : ∀ {A : Set} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷-injʳ refl = refl

++-cancelˡ : ∀ {A : Set} (xs : List A) {ys zs} → xs ++ ys ≡ xs ++ zs → ys ≡ zs
++-cancelˡ []       p = p
++-cancelˡ (x ∷ xs) p = ++-cancelˡ xs (∷-injʳ p)

length : ∀ {A : Set} → List A → Nat
length []       = 0
length (_ ∷ xs) = suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ []       ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

suc≢0 : ∀ {n} → suc n ≡ zero → ⊥
suc≢0 ()

+-cancelʳ-0 : ∀ m n → m + n ≡ n → m ≡ zero
+-cancelʳ-0 zero    n p = refl
+-cancelʳ-0 (suc m) n p = ⊥-elim (lemma (suc m) n (s≤s z≤n) p)
  where
    lemma : ∀ k n → 1 ≤ k → k + n ≡ n → ⊥
    lemma (suc k) zero    _ p = suc≢0 (trans (sym (+-identityʳ (suc k))) p)
    lemma (suc k) (suc n) _ p =
      lemma (suc k) n (s≤s z≤n) (cong pred (trans (sym (+-suc (suc k) n)) p))

-- If xs ++ zs ≡ ys ++ zs then xs ≡ ys.
++-cancelʳ : ∀ {A : Set} (xs ys : List A) {zs} → xs ++ zs ≡ ys ++ zs → xs ≡ ys
++-cancelʳ []       []       p = refl
++-cancelʳ []       (y ∷ ys) {zs} p =
  ⊥-elim (suc≢0 (+-cancelʳ-0 (suc (length ys)) (length zs)
    (sym (trans (cong length p) (length-++ (y ∷ ys) zs)))))
++-cancelʳ (x ∷ xs) []       {zs} p =
  ⊥-elim (suc≢0 (+-cancelʳ-0 (suc (length xs)) (length zs)
    (trans (sym (length-++ (x ∷ xs) zs)) (cong length p))))
++-cancelʳ (x ∷ xs) (y ∷ ys) p =
  cong₂ _∷_ (∷-injˡ p) (++-cancelʳ xs ys (∷-injʳ p))

------------------------------------------------------------------------
-- Accessibility

data Acc {A : Set} (R : A → A → Set) (x : A) : Set where
  acc : (∀ y → R y x → Acc R y) → Acc R x

<-wf : ∀ n → Acc _<_ n
<-wf n = acc (go n)
  where
    go : ∀ n y → y < n → Acc _<_ y
    go (suc n) y (s≤s p) = acc (λ z q → go n z (≤-trans q p))

infix 4 _<lex_
data _<lex_ : Nat × Nat → Nat × Nat → Set where
  fst< : ∀ {a b c d} → a < c → (a , b) <lex (c , d)
  snd< : ∀ {a b d} → b < d → (a , b) <lex (a , d)

lex-wf : ∀ p → Acc _<lex_ p
lex-wf (a , b) = go a (<-wf a) b
  where
    go : ∀ a → Acc _<_ a → ∀ b → Acc _<lex_ (a , b)
    go a (acc ra) b = inner b (<-wf b)
      where
        inner : ∀ b → Acc _<_ b → Acc _<lex_ (a , b)
        inner b (acc rb) = acc helper
          where
            helper : ∀ y → y <lex (a , b) → Acc _<lex_ y
            helper (c , d)  (fst< p) = go c (ra c p) d
            helper (.a , d) (snd< p) = inner d (rb d p)

------------------------------------------------------------------------
-- Decisions

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : ¬ A → Dec A
