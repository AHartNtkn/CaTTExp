------------------------------------------------------------------------
-- Membership facts about the list-level set operations of
-- Gray.Support (map, concatMap, filter, upto, prod1, prodT), shared by
-- Gray.Fast and Gray.OrientRev.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.SetFacts (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Cover hiding (Tuple)

map≡ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) xs → map f xs ≡ mapL f xs
map≡ f []       = refl
map≡ f (x ∷ xs) = cong (f x ∷_) (map≡ f xs)

cm≡ : ∀ {a b} {A : Set a} {B : Set b} (f : A → List B) xs → concatMap f xs ≡ concatMapL f xs
cm≡ f []       = refl
cm≡ f (x ∷ xs) = cong (f x ++_) (cm≡ f xs)

cm-cong : ∀ {a b} {A : Set a} {B : Set b} {f g : A → List B} → (∀ x → f x ≡ g x) → ∀ xs →
          concatMapL f xs ≡ concatMapL g xs
cm-cong e []       = refl
cm-cong e (x ∷ xs) = cong₂ _++_ (e x) (cm-cong e xs)

anyS⇒ : ∀ {a} {A : Set a} (p : A → Bool) xs → T (any p xs) → Any (λ x → T (p x)) xs
anyS⇒ p (x ∷ xs) t with ∨-out {p x} t
... | inj₁ r = here r
... | inj₂ r = there (anyS⇒ p xs r)

anyS⇐ : ∀ {a} {A : Set a} (p : A → Bool) xs → Any (λ x → T (p x)) xs → T (any p xs)
anyS⇐ p (x ∷ xs) (here r)  = ∨-inl r
anyS⇐ p (x ∷ xs) (there r) = ∨-inr {p x} (anyS⇐ p xs r)

iff≡ : ∀ {a b} → (T a → T b) → (T b → T a) → a ≡ b
iff≡ {true}  {true}  f g = refl
iff≡ {true}  {false} f g = ⊥-elim (f tt)
iff≡ {false} {true}  f g = ⊥-elim (g tt)
iff≡ {false} {false} f g = refl

infix 4 _∈L_ _∈ᴺ_
_∈L_ : Tuple → TSet → Set
x ∈L S = Any (x ≡_) S

_∈ᴺ_ : Nat → List Nat → Set
x ∈ᴺ S = Any (x ≡_) S

lt-step : ∀ i n → T (i <ℕ suc n) → T (i <ℕ suc (suc n))
lt-step zero    n       _ = tt
lt-step (suc i) zero    ()
lt-step (suc i) (suc n) p = lt-step i n p

lt-refl : ∀ n → T (n <ℕ suc n)
lt-refl zero    = tt
lt-refl (suc n) = lt-refl n

lt-split : ∀ i n → T (i <ℕ suc (suc n)) → T (i <ℕ suc n) ⊎ (i ≡ suc n)
lt-split zero    n       _ = inj₁ tt
lt-split (suc i) zero    p with i
... | zero = inj₂ refl
lt-split (suc i) (suc n) p with lt-split i n p
... | inj₁ q = inj₁ q
... | inj₂ q = inj₂ (cong suc q)

upto⇒ : ∀ i n → i ∈ᴺ upto n → T (i <ℕ suc n)
upto⇒ i zero    (here refl) = tt
upto⇒ i (suc n) m with any-++⁻ (upto n) m
... | inj₁ a = lt-step i n (upto⇒ i n a)
... | inj₂ (here refl) = lt-refl (suc n)

upto⇐ : ∀ i n → T (i <ℕ suc n) → i ∈ᴺ upto n
upto⇐ zero    zero    _ = here refl
upto⇐ (suc i) zero    ()
upto⇐ i       (suc n) p with lt-split i n p
... | inj₁ q    = any-++l (upto⇐ i n q)
... | inj₂ refl = any-++r (upto n) (here refl)

filter⇒ : ∀ {a} {A : Set a} (p : A → Bool) xs {x} → Any (x ≡_) (filter p xs) → Any (x ≡_) xs × T (p x)
filter⇒ p (y ∷ ys) m with p y in e
filter⇒ p (y ∷ ys) (here refl) | true = here refl , subst T (sym e) tt
filter⇒ p (y ∷ ys) (there m)   | true = let a , b = filter⇒ p ys m in there a , b
... | false = let a , b = filter⇒ p ys m in there a , b

filter⇐ : ∀ {a} {A : Set a} (p : A → Bool) xs {x} → Any (x ≡_) xs → T (p x) → Any (x ≡_) (filter p xs)
filter⇐ p (y ∷ ys) (here refl) t with p y
... | true  = here refl
filter⇐ p (y ∷ ys) (there m) t with p y
... | true  = there (filter⇐ p ys m t)
... | false = filter⇐ p ys m t
prodT⇒ : ∀ A B {x} → x ∈L prodT A B → Σ Tuple λ y → Σ Tuple λ z → (x ≡ y ++ z) × y ∈L A × z ∈L B
prodT⇒ A B m rewrite cm≡ (λ x → map (x ++_) B) A with any-witness (any-cm⁻ _ A m)
... | y , my , m' rewrite map≡ (y ++_) B with any-witness (any-map⁻ (y ++_) B m')
...   | z , mz , refl = y , z , refl , my , mz

prodT⇐ : ∀ A B {y z} → y ∈L A → z ∈L B → (y ++ z) ∈L prodT A B
prodT⇐ A B {y} {z} my mz rewrite cm≡ (λ x → map (x ++_) B) A =
  any-cm⁺ _ (any-mono (λ { {y'} refl → subst (Any ((y ++ z) ≡_)) (sym (map≡ (y ++_) B)) (any-map⁺ (y ++_) (any-mono (λ { refl → refl }) mz)) }) my)

prod1⇒ : ∀ ws C {c} → c ∈L prod1 ws C → Σ Nat λ w → Σ Tuple λ c' → (c ≡ w ∷ c') × w ∈ᴺ ws × c' ∈L C
prod1⇒ ws C m rewrite cm≡ (λ x → map (x ∷_) C) ws with any-witness (any-cm⁻ _ ws m)
... | w , mw , m' rewrite map≡ (w ∷_) C with any-witness (any-map⁻ (w ∷_) C m')
...   | c' , mc , refl = w , c' , refl , mw , mc

prod1⇐ : ∀ ws C {w c'} → w ∈ᴺ ws → c' ∈L C → (w ∷ c') ∈L prod1 ws C
prod1⇐ ws C {w} {c'} mw mc rewrite cm≡ (λ x → map (x ∷_) C) ws =
  any-cm⁺ _ (any-mono (λ { refl → subst (Any ((w ∷ c') ≡_)) (sym (map≡ (w ∷_) C)) (any-map⁺ (w ∷_) (any-mono (λ { refl → refl }) mc)) }) mw)
