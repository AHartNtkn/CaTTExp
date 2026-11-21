------------------------------------------------------------------------
-- List and arithmetic lemmas used by the semantics of the biclosed
-- kernel.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.ListLemmas where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps
open import CaTTExp.Gray.Biclosed.Rows using (leq; ids; idTys)

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


------------------------------------------------------------------------
-- sums and cons

infixr 1 _⊎′_
data _⊎′_ (A B : Set) : Set where
  inl : A → A ⊎′ B
  inr : B → A ⊎′ B

cons-inj : ∀ {A : Set} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → (x ≡ y) × (xs ≡ ys)
cons-inj refl = refl , refl

------------------------------------------------------------------------
-- take and drop

drop : ∀ {A : Set} → Nat → List A → List A
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

take-drop : ∀ {A : Set} n (xs : List A) → take n xs ++ drop n xs ≡ xs
take-drop zero    xs       = refl
take-drop (suc n) []       = refl
take-drop (suc n) (x ∷ xs) = cong (x ∷_) (take-drop n xs)

take-++ˡ : ∀ {A : Set} n (xs ys : List A) → T (leq n (length xs)) → take n (xs ++ ys) ≡ take n xs
take-++ˡ zero    xs       ys p = refl
take-++ˡ (suc n) (x ∷ xs) ys p = cong (x ∷_) (take-++ˡ n xs ys p)

drop-++ˡ : ∀ {A : Set} n (xs ys : List A) → T (leq n (length xs)) → drop n (xs ++ ys) ≡ drop n xs ++ ys
drop-++ˡ zero    xs       ys p = refl
drop-++ˡ (suc n) (x ∷ xs) ys p = drop-++ˡ n xs ys p

take-++ʳ : ∀ {A : Set} (xs : List A) n ys → take (length xs + n) (xs ++ ys) ≡ xs ++ take n ys
take-++ʳ []       n ys = refl
take-++ʳ (x ∷ xs) n ys = cong (x ∷_) (take-++ʳ xs n ys)

drop-++ʳ : ∀ {A : Set} (xs : List A) n ys → drop (length xs + n) (xs ++ ys) ≡ drop n ys
drop-++ʳ []       n ys = refl
drop-++ʳ (x ∷ xs) n ys = drop-++ʳ xs n ys

length-take : ∀ {A : Set} n (xs : List A) → T (leq n (length xs)) → length (take n xs) ≡ n
length-take zero    xs       p = refl
length-take (suc n) (x ∷ xs) p = cong suc (length-take n xs p)

take-map : ∀ {A B : Set} (f : A → B) n xs → take n (map f xs) ≡ map f (take n xs)
take-map f zero    xs       = refl
take-map f (suc n) []       = refl
take-map f (suc n) (x ∷ xs) = cong (f x ∷_) (take-map f n xs)

drop-map : ∀ {A B : Set} (f : A → B) n xs → drop n (map f xs) ≡ map f (drop n xs)
drop-map f zero    xs       = refl
drop-map f (suc n) []       = refl
drop-map f (suc n) (x ∷ xs) = drop-map f n xs

-- a split of a list is its take and drop
split-unique : ∀ {A : Set} (pre post xs : List A) → pre ++ post ≡ xs →
               (pre ≡ take (length pre) xs) × (post ≡ drop (length pre) xs)
split-unique []         post xs refl = refl , refl
split-unique (p ∷ pre) post ._ refl =
  cong (p ∷_) (fst (split-unique pre post _ refl)) , snd (split-unique pre post _ refl)

-- a split of a list into a prefix and a suffix extending past a hinge
split-mid : ∀ {A : Set} (pre post L : List A) X R → pre ++ post ≡ L ++ X ∷ R →
  Σ (List A) (λ M → (L ≡ pre ++ M) × (post ≡ M ++ X ∷ R)) ⊎′
  Σ (List A) (λ M → (pre ≡ L ++ X ∷ M) × (R ≡ M ++ post))
split-mid []         post L X R e = inl (L , refl , e)
split-mid (p ∷ pre) post []      X R refl = inr (pre , refl , refl)
split-mid (p ∷ pre) post (l ∷ L) X R e with cons-inj e
... | refl , e′ with split-mid pre post L X R e′
...   | inl (M , a , b) = inl (M , cong (p ∷_) a , b)
...   | inr (M , a , b) = inr (M , cong (p ∷_) a , b)

-- a prefix of Φ ++ [A] no longer than Φ
split-snoc : ∀ {A : Set} (pre post Φ : List A) a → pre ++ post ≡ Φ ++ a ∷ [] →
  T (leq (length pre) (length Φ)) → Σ (List A) (λ M → (post ≡ M ++ a ∷ []) × (pre ++ M ≡ Φ))
split-snoc []         post Φ a e p = Φ , e , refl
split-snoc (x ∷ pre) post (y ∷ Φ) a e p with cons-inj e
... | refl , e′ with split-snoc pre post Φ a e′ p
...   | M , q , r = M , q , cong (x ∷_) r

------------------------------------------------------------------------
-- leq

leq-+ : ∀ a b → T (leq a (a + b))
leq-+ zero    b = tt
leq-+ (suc a) b = leq-+ a b

leq-+suc : ∀ n m → leq (n + suc m) n ≡ false
leq-+suc zero    m = refl
leq-+suc (suc n) m = leq-+suc n m

leq-false : ∀ g n → leq g n ≡ false → Σ Nat (λ m → g ≡ n + suc m)
leq-false zero    n       ()
leq-false (suc g) zero    e = g , refl
leq-false (suc g) (suc n) e with leq-false g n e
... | m , refl = m , refl

leq-+-cancel : ∀ n m k → T (leq (n + m) (n + k)) → T (leq m k)
leq-+-cancel zero    m k p = p
leq-+-cancel (suc n) m k p = leq-+-cancel n m k p

------------------------------------------------------------------------
-- identities

concatIns-idTys : ∀ L → concatIns (idTys L) ≡ L
concatIns-idTys []      = refl
concatIns-idTys (A ∷ L) = cong (A ∷_) (concatIns-idTys L)

sumIns-++ : ∀ xs ys → sumIns (xs ++ ys) ≡ sumIns xs + sumIns ys
sumIns-++ xs ys = trans (cong length (concatIns-++ xs ys)) (length-++ (concatIns xs) (concatIns ys))

-- a gap inside the identities: the gap is unchanged
sumIns-take-idTys : ∀ P M rest → sumIns (take (length P) (idTys (P ++ M) ++ rest)) ≡ length P
sumIns-take-idTys []      M rest = refl
sumIns-take-idTys (A ∷ P) M rest = cong suc (sumIns-take-idTys P M rest)
