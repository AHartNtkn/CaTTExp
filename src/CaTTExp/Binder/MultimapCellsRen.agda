------------------------------------------------------------------------
-- Renaming onto a support (ledger S26j, step 2b): list lemmas, and the
-- variables of a renamed term.
------------------------------------------------------------------------
module CaTTExp.Binder.MultimapCellsRen where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing hiding (canon)
open import CaTTExp.Gray.Biclosed.Strengthen
open import CaTTExp.Binder.MultimapCells
open import CaTTExp.Binder.MultimapCellsStrengthen
  using (T-if; F-if; _⊎′_; inl; inr; dec; lookup-idx; lookup-map; filter-elem; upTo-elem)
open import CaTTExp.Binder.MultimapCellsSupport using (In; _⊆_; elem-split)

------------------------------------------------------------------------
-- Lists of naturals.

map-++ : ∀ {A B : Set} (f : A → B) xs ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

upTo-cons : ∀ m → upTo (suc m) ≡ 0 ∷ map suc (upTo m)
upTo-cons zero    = refl
upTo-cons (suc m) =
  trans (cong (_++ (suc m ∷ [])) (upTo-cons m))
        (cong (0 ∷_) (sym (map-++ suc (upTo m) (m ∷ []))))

filter-map-suc : ∀ (P : Nat → Bool) xs → filter P (map suc xs) ≡ map suc (filter (λ i → P (suc i)) xs)
filter-map-suc P []       = refl
filter-map-suc P (x ∷ xs) with P (suc x)
... | true  = cong (suc x ∷_) (filter-map-suc P xs)
... | false = filter-map-suc P xs

nth : List Nat → Nat → Nat
nth []       _       = 0
nth (x ∷ xs) zero    = x
nth (x ∷ xs) (suc p) = nth xs p

data NoDup : List Nat → Set where
  []  : NoDup []
  _∷_ : ∀ {x xs} → (In xs x → ⊥) → NoDup xs → NoDup (x ∷ xs)

map-cong-In : ∀ (f g : Nat → Nat) xs → (∀ i → In xs i → f i ≡ g i) → map f xs ≡ map g xs
map-cong-In f g []       h = refl
map-cong-In f g (x ∷ xs) h =
  cong₂ _∷_ (h x (∨-l (x ==ℕ x) _ (==ℕ-refl x))) (map-cong-In f g xs (λ i p → h i (∨-r (i ==ℕ x) _ p)))

map-map : ∀ (f g : Nat → Nat) xs → map f (map g xs) ≡ map (λ i → f (g i)) xs
map-map f g []       = refl
map-map f g (x ∷ xs) = cong (f (g x) ∷_) (map-map f g xs)

filter-sub : ∀ (P : Nat → Bool) xs → filter P xs ⊆ xs
filter-sub P (x ∷ xs) i p with P x
... | true  with dec (i ==ℕ x)
...   | inl q = ∨-l (i ==ℕ x) _ q
...   | inr q = ∨-r (i ==ℕ x) _ (filter-sub P xs i (or-r (i ==ℕ x) _ q p))
  where
  or-r : ∀ a b → (T a → ⊥) → T (a ∨ b) → T b
  or-r true  b n _ = ⊥-elim (n tt)
  or-r false b n p = p
filter-sub P (x ∷ xs) i p | false = ∨-r (i ==ℕ x) _ (filter-sub P xs i p)

-- Positions of a filtered duplicate-free list.
idx-filter : ∀ (P : Nat → Bool) xs → NoDup xs →
  map (λ i → idx i xs) (filter P xs) ≡ filter (λ p → P (nth xs p)) (upTo (length xs))
idx-filter P []       _ = refl
idx-filter P (x ∷ xs) (nx ∷ nd) =
  trans lhs (sym (trans (cong (filter (λ p → P (nth (x ∷ xs) p))) (upTo-cons (length xs))) rhs))
  where
  tail-eq : map (λ i → idx i (x ∷ xs)) (filter P xs) ≡ map suc (map (λ i → idx i xs) (filter P xs))
  tail-eq = trans (map-cong-In _ _ (filter P xs) (λ i p → F-if (i ==ℕ x) (λ q →
              nx (subst (In xs) (==ℕ-sound i x q) (filter-sub P xs i p)))))
                  (sym (map-map suc (λ i → idx i xs) (filter P xs)))
  rec : map suc (map (λ i → idx i xs) (filter P xs)) ≡
        filter (λ p → P (nth (x ∷ xs) p)) (map suc (upTo (length xs)))
  rec = trans (cong (map suc) (idx-filter P xs nd))
              (sym (filter-map-suc (λ p → P (nth (x ∷ xs) p)) (upTo (length xs))))
  lhs : map (λ i → idx i (x ∷ xs)) (filter P (x ∷ xs)) ≡
        (if P x then 0 ∷ filter (λ p → P (nth (x ∷ xs) p)) (map suc (upTo (length xs)))
                else filter (λ p → P (nth (x ∷ xs) p)) (map suc (upTo (length xs))))
  lhs with P x
  ... | true  = cong₂ _∷_ (T-if (x ==ℕ x) (==ℕ-refl x)) (trans tail-eq rec)
  ... | false = trans tail-eq rec
  rhs : filter (λ p → P (nth (x ∷ xs) p)) (0 ∷ map suc (upTo (length xs))) ≡
        (if P x then 0 ∷ filter (λ p → P (nth (x ∷ xs) p)) (map suc (upTo (length xs)))
                else filter (λ p → P (nth (x ∷ xs) p)) (map suc (upTo (length xs))))
  rhs = refl

filter-ext : ∀ (P Q : Nat → Bool) xs → (∀ i → In xs i → P i ≡ Q i) → filter P xs ≡ filter Q xs
filter-ext P Q []       h = refl
filter-ext P Q (x ∷ xs) h
  rewrite h x (∨-l (x ==ℕ x) _ (==ℕ-refl x))
  with Q x
... | true  = cong (x ∷_) (filter-ext P Q xs (λ i p → h i (∨-r (i ==ℕ x) _ p)))
... | false = filter-ext P Q xs (λ i p → h i (∨-r (i ==ℕ x) _ p))

filter-filter : ∀ (P Q : Nat → Bool) xs → (∀ i → In xs i → T (P i) → T (Q i)) →
                filter P (filter Q xs) ≡ filter P xs
filter-filter P Q []       h = refl
filter-filter P Q (x ∷ xs) h with Q x in eq
... | true  with P x
...   | true  = cong (x ∷_) (filter-filter P Q xs (λ i q → h i (∨-r (i ==ℕ x) _ q)))
...   | false = filter-filter P Q xs (λ i q → h i (∨-r (i ==ℕ x) _ q))
filter-filter P Q (x ∷ xs) h | false with P x in ep
...   | true  = ⊥-elim (subst T eq (h x (∨-l (x ==ℕ x) _ (==ℕ-refl x)) (subst T (sym ep) tt)))
...   | false = filter-filter P Q xs (λ i q → h i (∨-r (i ==ℕ x) _ q))

iff-≡ : ∀ a b → (T a → T b) → (T b → T a) → a ≡ b
iff-≡ true  true  _ _ = refl
iff-≡ true  false f _ = ⊥-elim (f tt)
iff-≡ false true  _ g = ⊥-elim (g tt)
iff-≡ false false _ _ = refl

------------------------------------------------------------------------
-- Variables of a renamed term.

⊆-l : ∀ xs ys D → (xs ++ ys) ⊆ D → xs ⊆ D
⊆-l xs ys D h i p = h i (elem-++l i xs ys p)

⊆-r : ∀ xs ys D → (xs ++ ys) ⊆ D → ys ⊆ D
⊆-r xs ys D h i p = h i (elem-++r i xs ys p)

module _ (as vs : List Nat) where
  private ρ = renOf as vs
  r : Nat → Nat
  r i = idx i vs

  mutual
    varsT-ren : ∀ t → varsT t ⊆ vs → varsT (sT ρ t) ≡ map r (varsT t)
    varsT-ren (var i) h =
      cong varsT (T-if (elem i vs) (h i (∨-l (i ==ℕ i) _ (==ℕ-refl i))))
    varsT-ren (comp f gs) h =
      trans (cong₂ _++_ (varsT-ren f (⊆-l (varsT f) (varsTs gs) vs h))
                        (varsTs-ren gs (⊆-r (varsT f) (varsTs gs) vs h)))
            (sym (map-++ r (varsT f) (varsTs gs)))
    varsT-ren (glue a x b) h =
      let h₂₃ = ⊆-r (varsT a) (varsT x ++ varsT b) vs h in
      trans (cong₂ _++_ (varsT-ren a (⊆-l (varsT a) (varsT x ++ varsT b) vs h))
                        (trans (cong₂ _++_ (varsT-ren x (⊆-l (varsT x) (varsT b) vs h₂₃))
                                           (varsT-ren b (⊆-r (varsT x) (varsT b) vs h₂₃)))
                               (sym (map-++ r (varsT x) (varsT b)))))
            (sym (map-++ r (varsT a) (varsT x ++ varsT b)))
    varsT-ren (here t e φs ts) h = varsTs-ren ts h
    varsT-ren (mP _ _) h = refl
    varsT-ren (eL _ _) h = refl
    varsT-ren (eR _ _) h = refl
    varsT-ren (pP _ _) h = refl
    varsT-ren pt       h = refl
    varsT-ren (iP _)   h = refl
    varsT-ren (idt _)  h = refl

    varsTs-ren : ∀ ts → varsTs ts ⊆ vs → varsTs (sTs ρ ts) ≡ map r (varsTs ts)
    varsTs-ren []       h = refl
    varsTs-ren (t ∷ ts) h =
      trans (cong₂ _++_ (varsT-ren t (⊆-l (varsT t) (varsTs ts) vs h))
                        (varsTs-ren ts (⊆-r (varsT t) (varsTs ts) vs h)))
            (sym (map-++ r (varsT t) (varsTs ts)))

  varsY-ren : ∀ A → varsY A ⊆ vs → varsY (sY ρ A) ≡ map r (varsY A)
  varsY-ren (op _) h = refl
  varsY-ren (hom m g A s t) h =
    let h₂₃ = ⊆-r (varsY A) (varsT s ++ varsT t) vs h in
    trans (cong₂ _++_ (varsY-ren A (⊆-l (varsY A) (varsT s ++ varsT t) vs h))
                      (trans (cong₂ _++_ (varsT-ren s (⊆-l (varsT s) (varsT t) vs h₂₃))
                                         (varsT-ren t (⊆-r (varsT s) (varsT t) vs h₂₃)))
                             (sym (map-++ r (varsT s) (varsT t)))))
          (sym (map-++ r (varsY A) (varsT s ++ varsT t)))

------------------------------------------------------------------------
-- Increasing lists.

All< : Nat → List Nat → Set
All< x xs = ∀ i → In xs i → T (x <ℕ i)

data Inc : List Nat → Set where
  []  : Inc []
  _∷_ : ∀ {x xs} → All< x xs → Inc xs → Inc (x ∷ xs)

<-trans″ : ∀ a b c → T (a <ℕ b) → T (b <ℕ c) → T (a <ℕ c)
<-trans″ zero    (suc b) (suc c) _ _ = tt
<-trans″ (suc a) (suc b) (suc c) p q = <-trans″ a b c p q

<-irrefl : ∀ a → T (a <ℕ a) → ⊥
<-irrefl (suc a) p = <-irrefl a p

==→≡ : ∀ a b → T (a ==ℕ b) → a ≡ b
==→≡ = ==ℕ-sound

In-map-suc : ∀ xs i → In (map suc xs) (suc i) → In xs i
In-map-suc (x ∷ xs) i p with dec (suc i ==ℕ suc x)
... | inl q = ∨-l (i ==ℕ x) _ q
... | inr q = ∨-r (i ==ℕ x) _ (In-map-suc xs i (or-r (suc i ==ℕ suc x) _ q p))
  where
  or-r : ∀ a b → (T a → ⊥) → T (a ∨ b) → T b
  or-r true  b n _ = ⊥-elim (n tt)
  or-r false b n p = p

In-map-suc0 : ∀ xs → In (map suc xs) 0 → ⊥
In-map-suc0 (x ∷ xs) p = In-map-suc0 xs p

inc-map-suc : ∀ xs → Inc xs → Inc (map suc xs)
inc-map-suc []       []       = []
inc-map-suc (x ∷ xs) (a ∷ i) = (λ { zero p → ⊥-elim (In-map-suc0 xs p) ; (suc j) p → a j (In-map-suc xs j p) })
                               ∷ inc-map-suc xs i

inc-upTo : ∀ n → Inc (upTo n)
inc-upTo zero    = []
inc-upTo (suc n) = subst Inc (sym (upTo-cons n))
  ((λ { zero p → ⊥-elim (In-map-suc0 (upTo n) p) ; (suc j) p → tt }) ∷ inc-map-suc (upTo n) (inc-upTo n))

inc-filter : ∀ (P : Nat → Bool) xs → Inc xs → Inc (filter P xs)
inc-filter P []       []      = []
inc-filter P (x ∷ xs) (a ∷ i) with P x
... | true  = (λ j p → a j (filter-sub P xs j p)) ∷ inc-filter P xs i
... | false = inc-filter P xs i

inc-nodup : ∀ xs → Inc xs → NoDup xs
inc-nodup []       []      = []
inc-nodup (x ∷ xs) (a ∷ i) = (λ p → <-irrefl x (a x p)) ∷ inc-nodup xs i

-- idx is strictly monotone on an increasing list.
idx-mono : ∀ xs → Inc xs → ∀ i j → In xs i → In xs j → T (i <ℕ j) → T (idx i xs <ℕ idx j xs)
idx-mono (x ∷ xs) (a ∷ inc) i j pi pj ij with dec (i ==ℕ x) | dec (j ==ℕ x)
... | inl qi | inl qj = ⊥-elim (<-irrefl j (subst (λ y → T (y <ℕ j)) (trans (==→≡ i x qi) (sym (==→≡ j x qj))) ij))
... | inl qi | inr qj rewrite T-if (i ==ℕ x) {x = 0} {y = suc (idx i xs)} qi | F-if (j ==ℕ x) {x = 0} {y = suc (idx j xs)} qj = tt
... | inr qi | inl qj =
      let i∈ = or-r (i ==ℕ x) _ qi pi in
      ⊥-elim (<-irrefl j (<-trans″ j i j (subst (λ y → T (y <ℕ i)) (sym (==→≡ j x qj)) (a i i∈)) ij))
  where
  or-r : ∀ a b → (T a → ⊥) → T (a ∨ b) → T b
  or-r true  b n _ = ⊥-elim (n tt)
  or-r false b n p = p
... | inr qi | inr qj rewrite F-if (i ==ℕ x) {x = 0} {y = suc (idx i xs)} qi | F-if (j ==ℕ x) {x = 0} {y = suc (idx j xs)} qj =
      idx-mono xs inc i j (or-r (i ==ℕ x) _ qi pi) (or-r (j ==ℕ x) _ qj pj) ij
  where
  or-r : ∀ a b → (T a → ⊥) → T (a ∨ b) → T b
  or-r true  b n _ = ⊥-elim (n tt)
  or-r false b n p = p

------------------------------------------------------------------------
-- Positions.

private
  or-r : ∀ a b → (T a → ⊥) → T (a ∨ b) → T b
  or-r true  b n _ = ⊥-elim (n tt)
  or-r false b n p = p

idx-lt : ∀ xs i → In xs i → T (idx i xs <ℕ length xs)
idx-lt (x ∷ xs) i p with dec (i ==ℕ x)
... | inl q rewrite T-if (i ==ℕ x) {x = 0} {y = suc (idx i xs)} q = tt
... | inr q rewrite F-if (i ==ℕ x) {x = 0} {y = suc (idx i xs)} q = idx-lt xs i (or-r (i ==ℕ x) _ q p)

nth-idx : ∀ xs i → In xs i → nth xs (idx i xs) ≡ i
nth-idx (x ∷ xs) i p with dec (i ==ℕ x)
... | inl q rewrite T-if (i ==ℕ x) {x = 0} {y = suc (idx i xs)} q = sym (==ℕ-sound i x q)
... | inr q rewrite F-if (i ==ℕ x) {x = 0} {y = suc (idx i xs)} q = nth-idx xs i (or-r (i ==ℕ x) _ q p)

nth-In : ∀ xs p → T (p <ℕ length xs) → In xs (nth xs p)
nth-In (x ∷ xs) zero    _ = ∨-l (x ==ℕ x) _ (==ℕ-refl x)
nth-In (x ∷ xs) (suc p) l = ∨-r (nth xs p ==ℕ x) _ (nth-In xs p l)

idx-nth : ∀ xs → NoDup xs → ∀ p → T (p <ℕ length xs) → idx (nth xs p) xs ≡ p
idx-nth (x ∷ xs) (nx ∷ nd) zero    _ = T-if (x ==ℕ x) (==ℕ-refl x)
idx-nth (x ∷ xs) (nx ∷ nd) (suc p) l =
  trans (F-if (nth xs p ==ℕ x) (λ q → nx (subst (In xs) (==ℕ-sound _ x q) (nth-In xs p l))))
        (cong suc (idx-nth xs nd p l))

lookup-nth : ∀ xs p → T (p <ℕ length xs) → lookup xs p ≡ just (nth xs p)
lookup-nth (x ∷ xs) zero    _ = refl
lookup-nth (x ∷ xs) (suc p) l = lookup-nth xs p l

In-map : ∀ (f : Nat → Nat) xs x → In xs x → In (map f xs) (f x)
In-map f (y ∷ xs) x p with dec (x ==ℕ y)
... | inl q rewrite ==ℕ-sound x y q = ∨-l (f y ==ℕ f y) _ (==ℕ-refl (f y))
... | inr q = ∨-r (f x ==ℕ f y) _ (In-map f xs x (or-r (x ==ℕ y) _ q p))

In-map-inv : ∀ (f : Nat → Nat) xs y → In (map f xs) y → Σ Nat (λ x → In xs x × (y ≡ f x))
In-map-inv f (x ∷ xs) y p with dec (y ==ℕ f x)
... | inl q = x , ∨-l (x ==ℕ x) _ (==ℕ-refl x) , ==ℕ-sound y (f x) q
... | inr q =
      let (z , iz , e) = In-map-inv f xs y (or-r (y ==ℕ f x) _ q p)
      in z , ∨-r (z ==ℕ x) _ iz , e

filter-In-inv : ∀ (P : Nat → Bool) xs i → In (filter P xs) i → T (P i) × In xs i
filter-In-inv P (x ∷ xs) i p with dec (P x)
... | inl px rewrite T-if (P x) {x = x ∷ filter P xs} {y = filter P xs} px with dec (i ==ℕ x)
...   | inl q = subst (λ y → T (P y)) (sym (==ℕ-sound i x q)) px , ∨-l (i ==ℕ x) _ q
...   | inr q = let (a , b) = filter-In-inv P xs i (or-r (i ==ℕ x) _ q p) in a , ∨-r (i ==ℕ x) _ b
filter-In-inv P (x ∷ xs) i p | inr px rewrite F-if (P x) {x = x ∷ filter P xs} {y = filter P xs} px =
      let (a , b) = filter-In-inv P xs i p in a , ∨-r (i ==ℕ x) _ b

upTo-In-inv : ∀ n i → In (upTo n) i → T (i <ℕ n)
upTo-In-inv (suc n) i p with elem-split i (upTo n) (n ∷ []) p
... | inl q = <-suc′ i n (upTo-In-inv n i q)
  where
  <-suc′ : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  <-suc′ zero    b       _ = tt
  <-suc′ (suc a) (suc b) p = <-suc′ a b p
... | inr q = subst (λ y → T (y <ℕ suc n)) (sym (==ℕ-sound i n (or-l q))) (self n)
  where
  or-l : ∀ {a} → T (a ∨ false) → T a
  or-l {true} _ = tt
  self : ∀ n → T (n <ℕ suc n)
  self zero    = tt
  self (suc n) = self n
