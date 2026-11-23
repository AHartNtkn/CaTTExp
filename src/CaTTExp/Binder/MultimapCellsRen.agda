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
