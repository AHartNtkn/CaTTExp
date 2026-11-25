------------------------------------------------------------------------
-- Boolean and list lemmas for the DAG checker's soundness proof.
------------------------------------------------------------------------
open import CaTTExp.Prelude

module CaTTExp.Dag.Lemmas where

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

-- `if b then just x else nothing ≡ just y` means b holds and x ≡ y.
if-just : ∀ {A : Set} b {x y : A} → (if b then just x else nothing) ≡ just y → T b × (x ≡ y)
if-just true  refl = tt , refl
if-just false ()

is-just-sound : ∀ {A : Set} (m : Maybe A) → T (is-just m) → Σ A (λ x → m ≡ just x)
is-just-sound (just x) _ = x , refl

T-true : ∀ {b} → T b → b ≡ true
T-true {true} _ = refl

true-T : ∀ {b} → b ≡ true → T b
true-T refl = tt

bool-ext : ∀ {a b} → (T a → T b) → (T b → T a) → a ≡ b
bool-ext {true}  {true}  f g = refl
bool-ext {true}  {false} f g = ⊥-elim (f tt)
bool-ext {false} {true}  f g = ⊥-elim (g tt)
bool-ext {false} {false} f g = refl

∨-inl : ∀ {a b} → T a → T (a ∨ b)
∨-inl {true} _ = tt

∨-inr : ∀ {a b} → T b → T (a ∨ b)
∨-inr {true}  _ = tt
∨-inr {false} p = p

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

∨-elim : ∀ {a b} → T (a ∨ b) → T a ⊎ T b
∨-elim {true}  _ = inl tt
∨-elim {false} p = inr p

∨-assoc : ∀ a b c → (a ∨ (b ∨ c)) ≡ ((a ∨ b) ∨ c)
∨-assoc true  b c = refl
∨-assoc false b c = refl

∨-swap : ∀ a b c → (a ∨ (b ∨ c)) ≡ (b ∨ (a ∨ c))
∨-swap true  true  c = refl
∨-swap true  false c = refl
∨-swap false true  c = refl
∨-swap false false c = refl

------------------------------------------------------------------------
-- Naturals

==ℕ-false : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
==ℕ-false zero    (suc n) _ = refl
==ℕ-false (suc i) (suc n) p = ==ℕ-false i n p

==ℕ-true : ∀ n → (n ==ℕ n) ≡ true
==ℕ-true zero    = refl
==ℕ-true (suc n) = ==ℕ-true n

<-tri : ∀ x y → (x <ℕ y) ≡ false → (y <ℕ x) ≡ false → x ≡ y
<-tri zero    zero    _ _ = refl
<-tri zero    (suc y) () _
<-tri (suc x) zero    _ ()
<-tri (suc x) (suc y) p q = cong suc (<-tri x y p q)

-- k < suc f: either k < f or k ≡ f.
<-suc-cases : ∀ k f → T (k <ℕ suc f) → T (k <ℕ f) ⊎ (k ≡ f)
<-suc-cases zero    zero    _ = inr refl
<-suc-cases zero    (suc f) _ = inl tt
<-suc-cases (suc k) zero    ()
<-suc-cases (suc k) (suc f) p with <-suc-cases k f p
... | inl q    = inl q
... | inr refl = inr refl

suc-inj : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

------------------------------------------------------------------------
-- Membership

elem-++ : ∀ x xs ys → elem x (xs ++ ys) ≡ (elem x xs ∨ elem x ys)
elem-++ x []       ys = refl
elem-++ x (y ∷ xs) ys rewrite elem-++ x xs ys = ∨-assoc (x ==ℕ y) (elem x xs) (elem x ys)

elem-respects : ∀ x y ys → T (x ==ℕ y) → elem x ys ≡ elem y ys
elem-respects x y ys p rewrite ==ℕ-sound x y p = refl

all-ext : ∀ (p q : Nat → Bool) xs → (∀ x → p x ≡ q x) → all p xs ≡ all q xs
all-ext p q []       h = refl
all-ext p q (x ∷ xs) h rewrite h x | all-ext p q xs h = refl

all→ : ∀ (p : Nat → Bool) xs x → T (all p xs) → T (elem x xs) → T (p x)
all→ p (y ∷ xs) x a e with ∨-elim {x ==ℕ y} e
... | inl q rewrite ==ℕ-sound x y q = ∧-fst a
... | inr q = all→ p xs x (∧-snd {p y} a) q

→all : ∀ (p : Nat → Bool) xs → (∀ x → T (elem x xs) → T (p x)) → T (all p xs)
→all p []       h = tt
→all p (y ∷ xs) h =
  ∧-intro′ (h y (∨-inl {y ==ℕ y} (true-T (==ℕ-true y))))
           (→all p xs (λ x e → h x (∨-inr {x ==ℕ y} e)))
  where
  ∧-intro′ : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-intro′ {true} _ q = q

-- ≈? only depends on the members of its first argument.
≈?-cong : ∀ xs xs' ys → (∀ x → elem x xs ≡ elem x xs') → ≈? xs ys ≡ ≈? xs' ys
≈?-cong xs xs' ys h = cong₂ _∧_ part1 part2
  where
  part1 : all (λ x → elem x ys) xs ≡ all (λ x → elem x ys) xs'
  part1 = bool-ext
    (λ a → →all _ xs' (λ x e → all→ _ xs x a (subst T (sym (h x)) e)))
    (λ a → →all _ xs  (λ x e → all→ _ xs' x a (subst T (h x) e)))
  part2 : all (λ y → elem y xs) ys ≡ all (λ y → elem y xs') ys
  part2 = all-ext _ _ ys h
