------------------------------------------------------------------------
-- Lists of variables as sets (ledger item A3a, general case).
--
-- Membership, inclusion and set equality for lists of naturals, on top
-- of the Boolean `elem` that the side conditions of CaTT use.
------------------------------------------------------------------------
module CaTTExp.Strict.LabelSets where

open import CaTTExp.Prelude

infix 4 _∈_ _⊆_ _≈_

_∈_ : Nat → List Nat → Set
v ∈ xs = elem v xs ≡ true

record _⊆_ (xs ys : List Nat) : Set where
  constructor sub
  field app : ∀ v → v ∈ xs → v ∈ ys
open _⊆_ public

_≈_ : List Nat → List Nat → Set
xs ≈ ys = (xs ⊆ ys) × (ys ⊆ xs)

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

private
  ==-r : ∀ n → (n ==ℕ n) ≡ true
  ==-r zero    = refl
  ==-r (suc n) = ==-r n

  ==-≡ : ∀ m n → (m ==ℕ n) ≡ true → m ≡ n
  ==-≡ zero    zero    _ = refl
  ==-≡ (suc m) (suc n) p = cong suc (==-≡ m n p)

  ∨-true : ∀ a → (a ∨ true) ≡ true
  ∨-true true  = refl
  ∨-true false = refl

elem-++′ : ∀ v xs ys → elem v (xs ++ ys) ≡ (elem v xs ∨ elem v ys)
elem-++′ v []       ys = refl
elem-++′ v (x ∷ xs) ys with v ==ℕ x
... | true  = refl
... | false = elem-++′ v xs ys

∈-hd : ∀ v xs → v ∈ (v ∷ xs)
∈-hd v xs rewrite ==-r v = refl

∈-tl : ∀ v w xs → v ∈ xs → v ∈ (w ∷ xs)
∈-tl v w xs p rewrite p = ∨-true (v ==ℕ w)

∈-∷⁻ : ∀ v w xs → v ∈ (w ∷ xs) → (v ≡ w) ⊎ (v ∈ xs)
∈-∷⁻ v w xs p with v ==ℕ w in e
... | true  = inj₁ (==-≡ v w e)
... | false = inj₂ p

∉[] : ∀ {v} → v ∈ [] → ⊥
∉[] ()

∈-++ˡ : ∀ v xs ys → v ∈ xs → v ∈ (xs ++ ys)
∈-++ˡ v xs ys p rewrite elem-++′ v xs ys | p = refl

∈-++ʳ : ∀ v xs ys → v ∈ ys → v ∈ (xs ++ ys)
∈-++ʳ v xs ys p rewrite elem-++′ v xs ys | p = ∨-true (elem v xs)

∈-++⁻ : ∀ v xs ys → v ∈ (xs ++ ys) → (v ∈ xs) ⊎ (v ∈ ys)
∈-++⁻ v xs ys p rewrite elem-++′ v xs ys with elem v xs
... | true  = inj₁ refl
... | false = inj₂ p

⊆-refl : ∀ {xs} → xs ⊆ xs
⊆-refl = sub λ v p → p

⊆-trans : ∀ {xs ys zs} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans f g = sub λ v p → app g v (app f v p)

≈-refl : ∀ {xs} → xs ≈ xs
≈-refl = ⊆-refl , ⊆-refl

≈-sym : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
≈-sym (f , g) = g , f

≈-trans : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans (f , g) (f′ , g′) = ⊆-trans f f′ , ⊆-trans g′ g

≡→≈ : ∀ {xs ys} → xs ≡ ys → xs ≈ ys
≡→≈ refl = ≈-refl

⊆-l : ∀ xs ys → xs ⊆ (xs ++ ys)
⊆-l xs ys = sub λ v p → ∈-++ˡ v xs ys p

⊆-r : ∀ xs ys → ys ⊆ (xs ++ ys)
⊆-r xs ys = sub λ v p → ∈-++ʳ v xs ys p

⊆-tl : ∀ w xs → xs ⊆ (w ∷ xs)
⊆-tl w xs = sub λ v p → ∈-tl v w xs p

⊆-[] : ∀ {xs} → [] ⊆ xs
⊆-[] = sub λ v ()

⊆-++ : ∀ {xs ys zs} → xs ⊆ zs → ys ⊆ zs → (xs ++ ys) ⊆ zs
⊆-++ {xs} {ys} f g = sub h
  where
  h : ∀ v → v ∈ (xs ++ ys) → _
  h v p with ∈-++⁻ v xs ys p
  ... | inj₁ q = app f v q
  ... | inj₂ q = app g v q

⊆-∷ : ∀ {w xs zs} → w ∈ zs → xs ⊆ zs → (w ∷ xs) ⊆ zs
⊆-∷ {w} {xs} m f = sub h
  where
  h : ∀ v → v ∈ (w ∷ xs) → _
  h v p with ∈-∷⁻ v w xs p
  ... | inj₁ refl = m
  ... | inj₂ q    = app f v q

⊆-++-mono : ∀ {xs xs′ ys ys′} → xs ⊆ xs′ → ys ⊆ ys′ → (xs ++ ys) ⊆ (xs′ ++ ys′)
⊆-++-mono {xs′ = xs′} {ys′ = ys′} f g = ⊆-++ (⊆-trans f (⊆-l xs′ ys′)) (⊆-trans g (⊆-r xs′ ys′))

≈-++ : ∀ {xs xs′ ys ys′} → xs ≈ xs′ → ys ≈ ys′ → (xs ++ ys) ≈ (xs′ ++ ys′)
≈-++ (f , g) (f′ , g′) = ⊆-++-mono f f′ , ⊆-++-mono g g′

≈-elem : ∀ {xs ys} → (∀ v → elem v xs ≡ elem v ys) → xs ≈ ys
≈-elem h = sub (λ v p → trans (sym (h v)) p) , sub (λ v p → trans (h v) p)

-- Concatenated images.
cmap : ∀ {A : Set} → (A → List Nat) → List A → List Nat
cmap f []       = []
cmap f (x ∷ xs) = f x ++ cmap f xs

cmap-++ : ∀ {A : Set} (f : A → List Nat) xs ys → cmap f (xs ++ ys) ≡ cmap f xs ++ cmap f ys
cmap-++ f []       ys = refl
cmap-++ f (x ∷ xs) ys = trans (cong (f x ++_) (cmap-++ f xs ys)) (sym (++-assoc (f x) (cmap f xs) (cmap f ys)))
  where
  ++-assoc : ∀ (as bs cs : List Nat) → (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
  ++-assoc []       bs cs = refl
  ++-assoc (a ∷ as) bs cs = cong (a ∷_) (++-assoc as bs cs)

++-assoc : ∀ {A : Set} (as bs cs : List A) → (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
++-assoc []       bs cs = refl
++-assoc (a ∷ as) bs cs = cong (a ∷_) (++-assoc as bs cs)

++-[] : ∀ {A : Set} (as : List A) → as ++ [] ≡ as
++-[] []       = refl
++-[] (a ∷ as) = cong (a ∷_) (++-[] as)

-- Steering an inclusion into one part of a union.
inl⊆ : ∀ {xs ys} zs → xs ⊆ ys → xs ⊆ (ys ++ zs)
inl⊆ {ys = ys} zs f = ⊆-trans f (⊆-l ys zs)

inr⊆ : ∀ {xs zs} ys → xs ⊆ zs → xs ⊆ (ys ++ zs)
inr⊆ {zs = zs} ys f = ⊆-trans f (⊆-r ys zs)

tl⊆ : ∀ {xs ys} w → xs ⊆ ys → xs ⊆ (w ∷ ys)
tl⊆ {ys = ys} w f = ⊆-trans f (⊆-tl w ys)

∈⊆ : ∀ {v xs ys} → v ∈ xs → xs ⊆ ys → v ∈ ys
∈⊆ {v} m f = app f v m

sing⊆ : ∀ {v ys} → v ∈ ys → (v ∷ []) ⊆ ys
sing⊆ m = ⊆-∷ m ⊆-[]
