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

------------------------------------------------------------------------
-- Supports commute with the renaming onto a support.

open import CaTTExp.Gray.Biclosed.ListLemmas using (length-map)
open import CaTTExp.Binder.MultimapCellsSupport
  using (Deps↓; Closed; cl-least; cl-closed; lookup-some)
open import CaTTExp.Binder.MultimapCellsStrengthen using (closeFrom-mono; nthY-just)

module SupportRen (Φ : Ctx) (dd : Deps↓ Φ) (X₀ : List Nat) (as : List Nat) where

  n : Nat
  n = length Φ

  R : List Nat
  R = closeFrom Φ n X₀

  vs : List Nat
  vs = filter (λ j → elem j R) (upTo n)

  ρ : Sub
  ρ = renOf as vs

  rr : Nat → Nat
  rr i = idx i vs

  Φ′ : Ctx
  Φ′ = map (sY ρ) (map (nthY Φ) vs)

  m : Nat
  m = length vs

  len-Φ′ : length Φ′ ≡ m
  len-Φ′ = trans (length-map (sY ρ) (map (nthY Φ) vs)) (length-map (nthY Φ) vs)

  vs-inc : Inc vs
  vs-inc = inc-filter _ (upTo n) (inc-upTo n)

  vs-nd : NoDup vs
  vs-nd = inc-nodup vs vs-inc

  vs-in : ∀ i → In R i → T (i <ℕ n) → In vs i
  vs-in i p l = filter-elem (λ j → elem j R) (upTo n) i p (upTo-elem n i l)

  vs-R : ∀ i → In vs i → In R i
  vs-R i p = fst (filter-In-inv (λ j → elem j R) (upTo n) i p)

  vs-lt : ∀ i → In vs i → T (i <ℕ n)
  vs-lt i p = upTo-In-inv n i (snd (filter-In-inv (λ j → elem j R) (upTo n) i p))

  <-trans‴ : ∀ a b c → T (a <ℕ b) → T (b <ℕ c) → T (a <ℕ c)
  <-trans‴ zero    (suc b) (suc c) _ _ = tt
  <-trans‴ (suc a) (suc b) (suc c) p q = <-trans‴ a b c p q

  vs-closed : ∀ j {A} → lookup Φ j ≡ just A → In vs j → varsY A ⊆ vs
  vs-closed j eA p l q = vs-in l (cl-closed Φ dd X₀ j eA (vs-R j p) l q)
                           (<-trans‴ l j n (dd j eA l q) (vs-lt j p))

  lookup-Φ′ : ∀ p → T (p <ℕ m) → lookup Φ′ p ≡ just (sY ρ (nthY Φ (nth vs p)))
  lookup-Φ′ p l =
    trans (lookup-map (sY ρ) (map (nthY Φ) vs) p)
      (trans (cong (mapM (sY ρ)) (lookup-map (nthY Φ) vs p))
             (cong (λ x → mapM (sY ρ) (mapM (nthY Φ) x)) (lookup-nth vs p l)))

  -- Entry j of Φ, for j in the support, is entry rr j of Φ′.
  lookup-Φ′-r : ∀ j {A} → lookup Φ j ≡ just A → In vs j → lookup Φ′ (rr j) ≡ just (sY ρ A)
  lookup-Φ′-r j {A} eA p =
    trans (lookup-Φ′ (rr j) (idx-lt vs j p))
      (cong (λ B → just (sY ρ B)) (trans (cong (nthY Φ) (nth-idx vs j p)) (nthY-just Φ j eA)))

  -- Φ′ at a position p < m.
  at : ∀ p → T (p <ℕ m) → Σ CTy (λ A → lookup Φ (nth vs p) ≡ just A)
  at p l = lookup-some Φ (nth vs p) (vs-lt (nth vs p) (nth-In vs p l))

  lt-m : ∀ {p A} → lookup Φ′ p ≡ just A → T (p <ℕ m)
  lt-m {p} e = subst (λ k → T (p <ℕ k)) len-Φ′ (lookup-below Φ′ p e)

  deps′ : Deps↓ Φ′
  deps′ p {A′} e i q =
    let l = lt-m e
        (A , eA) = at p l
        j = nth vs p
        jin = nth-In vs p l
        eA′ : A′ ≡ sY ρ A
        eA′ = just-inj (trans (sym e) (trans (lookup-Φ′ p l) (cong (λ B → just (sY ρ B)) (nthY-just Φ j eA))))
        q′ = subst (λ B → In (varsY B) i) eA′ q
        q″ = subst (λ xs → In xs i) (varsY-ren as vs A (vs-closed j eA jin)) q′
        (k , kin , ei) = In-map-inv rr (varsY A) i q″
        kvs = vs-closed j eA jin k kin
        mono = idx-mono vs vs-inc k j kvs jin (dd j eA k kin)
    in subst (λ x → T (x <ℕ p)) (sym ei) (subst (λ y → T (rr k <ℕ y)) (idx-nth vs vs-nd p l) mono)
    where
    just-inj : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
    just-inj refl = refl

  -- A start set inside the support: its support, after the renaming,
  -- is the support of its image.
  module ForSet (X : List Nat) (bvs : X ⊆ vs) where

    Rb : List Nat
    Rb = closeFrom Φ n X

    R′ : List Nat
    R′ = closeFrom Φ′ (length Φ′) (map rr X)

    -- Rb ∩ [0, n) ⊆ the support.
    Rb⊆vs : ∀ i → In Rb i → T (i <ℕ n) → In vs i
    Rb⊆vs i p l = cl-least Φ vs (λ j eA q → vs-closed j eA q) n X (self n)
                    (λ k q _ → bvs k q) i p l
      where
      self : ∀ n → T (n <ℕ suc n)
      self zero    = tt
      self (suc n) = self n

    lookup-inv : ∀ p {A′} → lookup Φ′ p ≡ just A′ →
                 Σ CTy (λ A → lookup Φ (nth vs p) ≡ just A × (A′ ≡ sY ρ A))
    lookup-inv p {A′} e =
      let l = lt-m e
          (A , eA) = at p l
      in A , eA , just-inj (trans (sym e) (trans (lookup-Φ′ p l) (cong (λ B → just (sY ρ B)) (nthY-just Φ (nth vs p) eA))))
      where
      just-inj : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
      just-inj refl = refl

    -- (⇒) R′ ⊆ rr (Rb).
    fwd : ∀ p → T (p <ℕ m) → In R′ p → In Rb (nth vs p)
    fwd p l q =
      let D′ = map rr (filter (λ i → elem i Rb) vs)
          cD′ : Closed Φ′ D′
          cD′ = λ p′ {A′} e inD i r →
            let (j , jin , ej) = In-map-inv rr (filter (λ i → elem i Rb) vs) p′ inD
                (jRb , jvs) = filter-In-inv (λ i → elem i Rb) vs j jin
                (A , eA , eA′) = lookup-inv p′ e
                -- nth vs p′ = j
                ej′ : nth vs p′ ≡ j
                ej′ = trans (cong (nth vs) ej) (nth-idx vs j jvs)
                eAj : lookup Φ j ≡ just A
                eAj = subst (λ x → lookup Φ x ≡ just A) ej′ eA
                r′ = subst (λ xs → In xs i) (varsY-ren as vs A (vs-closed j eAj jvs))
                       (subst (λ B → In (varsY B) i) eA′ r)
                (k , kin , ek) = In-map-inv rr (varsY A) i r′
                kRb = cl-closed Φ dd X j eAj jRb k kin
                kvs = vs-closed j eAj jvs k kin
            in subst (In D′) (sym ek) (In-map rr (filter (λ i → elem i Rb) vs) k (filter-elem (λ i → elem i Rb) vs k kRb kvs))
          h : ∀ i → In (map rr X) i → T (i <ℕ length Φ′) → In D′ i
          h i r _ =
            let (k , kin , ek) = In-map-inv rr X i r
            in subst (In D′) (sym ek)
                 (In-map rr (filter (λ i → elem i Rb) vs) k (filter-elem (λ i → elem i Rb) vs k (closeFrom-mono Φ n X k kin) (bvs k kin)))
          inD = cl-least Φ′ D′ cD′ (length Φ′) (map rr X) (self (length Φ′)) h p q
                  (subst (λ y → T (p <ℕ y)) (sym len-Φ′) l)
          (j , jin , ej) = In-map-inv rr (filter (λ i → elem i Rb) vs) p inD
          (jRb , jvs) = filter-In-inv (λ i → elem i Rb) vs j jin
      in subst (In Rb) (sym (trans (cong (nth vs) ej) (nth-idx vs j jvs))) jRb
      where
      self : ∀ n → T (n <ℕ suc n)
      self zero    = tt
      self (suc n) = self n

    -- (⇐) rr (Rb) ⊆ R′.
    bwd : ∀ p → T (p <ℕ m) → In Rb (nth vs p) → In R′ p
    bwd p l q =
      let D = filter (λ i → elem (rr i) R′) vs
          cR′ : Closed Φ′ R′
          cR′ = cl-closed Φ′ deps′ (map rr X)
          cD : Closed Φ D
          cD = λ j {A} eA inD k kin →
            let (jR′ , jvs) = filter-In-inv (λ i → elem (rr i) R′) vs j inD
                e′ = lookup-Φ′-r j eA jvs
                kvs = vs-closed j eA jvs k kin
                rk : In (varsY (sY ρ A)) (rr k)
                rk = subst (λ xs → In xs (rr k)) (sym (varsY-ren as vs A (vs-closed j eA jvs)))
                       (In-map rr (varsY A) k kin)
            in filter-elem (λ i → elem (rr i) R′) vs k (cR′ (rr j) e′ jR′ (rr k) rk) kvs
          h : ∀ i → In X i → T (i <ℕ n) → In D i
          h i r _ = filter-elem (λ i → elem (rr i) R′) vs i
                      (closeFrom-mono Φ′ (length Φ′) (map rr X) (rr i)
                        (In-map rr X i r))
                      (bvs i r)
          j = nth vs p
          jin = nth-In vs p l
          inD = cl-least Φ D cD n X (self n) h j q (vs-lt j jin)
          (jR′ , _) = filter-In-inv (λ i → elem (rr i) R′) vs j inD
      in subst (In R′) (idx-nth vs vs-nd p l) jR′
      where
      self : ∀ n → T (n <ℕ suc n)
      self zero    = tt
      self (suc n) = self n

    supVars-ren : supVarsFrom Φ′ (map rr X) ≡ map rr (supVarsFrom Φ X)
    supVars-ren =
      trans (cong (λ k → filter (λ p → elem p R′) (upTo k)) len-Φ′)
        (sym (trans (cong (map rr) (sym (filter-filter (λ i → elem i Rb) (λ j → elem j R) (upTo n)
                       (λ i ui ri → vs-R i (Rb⊆vs i ri (upTo-In-inv n i ui))))))
               (trans (idx-filter (λ i → elem i Rb) vs vs-nd)
                      (filter-ext _ _ (upTo m) (λ p up →
                        let l = upTo-In-inv m p up in
                        iff-≡ _ _ (bwd p l) (fwd p l))))))

------------------------------------------------------------------------
-- Increasing lists with the same elements are equal.

inc-ext : ∀ xs ys → Inc xs → Inc ys → (∀ i → In xs i → In ys i) → (∀ i → In ys i → In xs i) → xs ≡ ys
inc-ext []       []       _ _ _ _ = refl
inc-ext []       (y ∷ ys) _ _ _ g = ⊥-elim (g y (∨-l (y ==ℕ y) _ (==ℕ-refl y)))
inc-ext (x ∷ xs) []       _ _ f _ = ⊥-elim (f x (∨-l (x ==ℕ x) _ (==ℕ-refl x)))
inc-ext (x ∷ xs) (y ∷ ys) (ax ∷ ix) (ay ∷ iy) f g = go head-eq
  where
  head-eq : x ≡ y
  head-eq with dec (x ==ℕ y)
  ... | inl q = ==ℕ-sound x y q
  ... | inr q =
        let x∈ys = or-r (x ==ℕ y) _ q (f x (∨-l (x ==ℕ x) _ (==ℕ-refl x)))
            y<x = ay x x∈ys
        in ⊥-elim (yx y<x)
    where
    yx : T (y <ℕ x) → ⊥
    yx l with dec (y ==ℕ x)
    ... | inl r = q (subst (λ z → T (x ==ℕ z)) (sym (==ℕ-sound y x r)) (==ℕ-refl x))
    ... | inr r = <-irrefl x (<-trans″ x y x (ax y (or-r (y ==ℕ x) _ r (g y (∨-l (y ==ℕ y) _ (==ℕ-refl y))))) l)
  go : x ≡ y → x ∷ xs ≡ y ∷ ys
  go refl = cong (x ∷_) (inc-ext xs ys ix iy
    (λ i p → or-r (i ==ℕ x) _ (λ q → <-irrefl x (subst (λ z → T (x <ℕ z)) (==ℕ-sound i x q) (ax i p))) (f i (∨-r (i ==ℕ x) _ p)))
    (λ i p → or-r (i ==ℕ x) _ (λ q → <-irrefl x (subst (λ z → T (x <ℕ z)) (==ℕ-sound i x q) (ay i p))) (g i (∨-r (i ==ℕ x) _ p))))

-- Renaming a subset of an increasing list of numbers below k onto its
-- positions.
sub-filter-ren : ∀ ys → Inc ys → ∀ k → (∀ i → In ys i → T (i <ℕ k)) → ∀ S → S ⊆ ys →
  map (λ i → idx i ys) (filter (λ i → elem i S) (upTo k))
    ≡ filter (λ p → elem p (map (λ i → idx i ys) S)) (upTo (length ys))
sub-filter-ren ys iy k yk S Sy =
  trans (cong (map (λ i → idx i ys)) same)
    (trans (idx-filter (λ i → elem i S) ys (inc-nodup ys iy))
      (filter-ext _ _ (upTo (length ys)) (λ p up →
        let l = upTo-In-inv (length ys) p up in
        iff-≡ _ _
          (λ q → subst (λ z → In (map (λ i → idx i ys) S) z) (idx-nth ys (inc-nodup ys iy) p l)
                   (In-map (λ i → idx i ys) S (nth ys p) q))
          (λ q → let (x , xS , e) = In-map-inv (λ i → idx i ys) S p q in
                 subst (In S) (sym (trans (cong (nth ys) e) (nth-idx ys x (Sy x xS)))) xS))))
  where
  same : filter (λ i → elem i S) (upTo k) ≡ filter (λ i → elem i S) ys
  same = inc-ext _ _ (inc-filter _ (upTo k) (inc-upTo k)) (inc-filter _ ys iy)
    (λ i p → let (a , _) = filter-In-inv (λ i → elem i S) (upTo k) i p in
             filter-elem (λ i → elem i S) ys i a (Sy i a))
    (λ i p → let (a , b) = filter-In-inv (λ i → elem i S) ys i p in
             filter-elem (λ i → elem i S) (upTo k) i a (upTo-elem k i (yk i b)))
