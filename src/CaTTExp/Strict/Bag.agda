------------------------------------------------------------------------
-- Finite multisets ("bags") of tuples of naturals, with the algebra
-- needed for chains of the Steiner complexes K(Γ) = λΘ₁ ⊗ … ⊗ λΘₙ.
--
-- A non-negative chain is a bag of basis elements (a basis element of
-- K(Γ) is a tuple of variables, one per hom; see CaTTExp.Gray.Support).
-- Two bags are equal as chains when every tuple occurs equally often:
--
--     X ≈ Y  :=  ∀ a → count a X ≡ count a Y.
--
-- Sums of chains are _++_ and the tensor product is `prod`. All chains
-- in a strict ω-category ν(K) are non-negative, and the only
-- subtraction, ∂x = x⁺ − x⁻, is written additively (∂⁺c + x⁻ = ∂⁻c + x⁺),
-- so no integers are needed.
------------------------------------------------------------------------
module CaTTExp.Strict.Bag where

open import CaTTExp.Prelude

------------------------------------------------------------------------
-- Arithmetic.

+-zero : ∀ n → n + zero ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-zero n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

+-assoc : ∀ l m n → (l + m) + n ≡ l + (m + n)
+-assoc zero    m n = refl
+-assoc (suc l) m n = cong suc (+-assoc l m n)

+-cancelˡ : ∀ l m n → l + m ≡ l + n → m ≡ n
+-cancelˡ zero    m n p = p
+-cancelˡ (suc l) m n p = +-cancelˡ l m n (suc-inj p)
  where
  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

+-cancelʳ : ∀ l m n → m + l ≡ n + l → m ≡ n
+-cancelʳ l m n p = +-cancelˡ l m n (trans (+-comm l m) (trans p (+-comm n l)))

-- Swap the middle two summands.
+-interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-interchange a b c d =
  trans (+-assoc a b (c + d))
 (trans (cong (a +_) (trans (sym (+-assoc b c d))
                     (trans (cong (_+ d) (+-comm b c)) (+-assoc c b d))))
        (sym (+-assoc a c (b + d))))

------------------------------------------------------------------------
-- Tuples.

Tuple : Set
Tuple = List Nat

Bag : Set
Bag = List Tuple

eqT : Tuple → Tuple → Bool
eqT []       []       = true
eqT (x ∷ xs) (y ∷ ys) = (x ==ℕ y) ∧ eqT xs ys
eqT _        _        = false

eqT-sound : ∀ a b → T (eqT a b) → a ≡ b
eqT-sound []       []       _ = refl
eqT-sound (x ∷ xs) (y ∷ ys) p =
  cong₂ _∷_ (==ℕ-sound x y (∧-fst p)) (eqT-sound xs ys (∧-snd {x ==ℕ y} p))

eqT-refl : ∀ a → eqT a a ≡ true
eqT-refl []       = refl
eqT-refl (x ∷ xs) = helper (x ==ℕ x) (==ℕ-refl x)
  where
  helper : (b : Bool) → T b → b ∧ eqT xs xs ≡ true
  helper true _ = eqT-refl xs

++-assocL : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assocL []       ys zs = refl
++-assocL (x ∷ xs) ys zs = cong (x ∷_) (++-assocL xs ys zs)

++-[]L : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-[]L []       = refl
++-[]L (x ∷ xs) = cong (x ∷_) (++-[]L xs)

------------------------------------------------------------------------
-- Counting and bag equality.

count : Tuple → Bag → Nat
count a []      = 0
count a (x ∷ X) = if eqT a x then suc (count a X) else count a X

infix 4 _≈_
record _≈_ (X Y : Bag) : Set where
  constructor mk≈
  field at : ∀ a → count a X ≡ count a Y
open _≈_ public

≈-refl : ∀ {X} → X ≈ X
≈-refl = mk≈ λ a → refl

≈-sym : ∀ {X Y} → X ≈ Y → Y ≈ X
≈-sym p = mk≈ λ a → sym (at p a)

≈-trans : ∀ {X Y Z} → X ≈ Y → Y ≈ Z → X ≈ Z
≈-trans p q = mk≈ λ a → trans (at p a) (at q a)

≡→≈ : ∀ {X Y} → X ≡ Y → X ≈ Y
≡→≈ refl = ≈-refl

count-++ : ∀ a X Y → count a (X ++ Y) ≡ count a X + count a Y
count-++ a []      Y = refl
count-++ a (x ∷ X) Y with eqT a x
... | true  = cong suc (count-++ a X Y)
... | false = count-++ a X Y

++-cong : ∀ {X X' Y Y'} → X ≈ X' → Y ≈ Y' → X ++ Y ≈ X' ++ Y'
++-cong {X} {X'} {Y} {Y'} p q = mk≈ λ a →
  trans (count-++ a X Y) (trans (cong₂ _+_ (at p a) (at q a)) (sym (count-++ a X' Y')))

++-comm : ∀ X Y → X ++ Y ≈ Y ++ X
++-comm X Y = mk≈ λ a → trans (count-++ a X Y) (trans (+-comm (count a X) (count a Y)) (sym (count-++ a Y X)))

++-assoc : ∀ X Y Z → (X ++ Y) ++ Z ≈ X ++ (Y ++ Z)
++-assoc X Y Z = ≡→≈ (++-assocL X Y Z)

-- (X + Y) + (Z + W) = (X + Z) + (Y + W)
++-interchange : ∀ X Y Z W → (X ++ Y) ++ (Z ++ W) ≈ (X ++ Z) ++ (Y ++ W)
++-interchange X Y Z W = mk≈ λ a →
  trans (count-++ a (X ++ Y) (Z ++ W))
 (trans (cong₂ _+_ (count-++ a X Y) (count-++ a Z W))
 (trans (+-interchange (count a X) (count a Y) (count a Z) (count a W))
 (trans (sym (cong₂ _+_ (count-++ a X Z) (count-++ a Y W)))
        (sym (count-++ a (X ++ Z) (Y ++ W))))))

++-cancelʳ : ∀ X Y Z → X ++ Z ≈ Y ++ Z → X ≈ Y
++-cancelʳ X Y Z p = mk≈ λ a →
  +-cancelʳ (count a Z) (count a X) (count a Y)
    (trans (sym (count-++ a X Z)) (trans (at p a) (count-++ a Y Z)))

++-cancelˡ : ∀ X Y Z → Z ++ X ≈ Z ++ Y → X ≈ Y
++-cancelˡ X Y Z p = ++-cancelʳ X Y Z (≈-trans (++-comm X Z) (≈-trans p (++-comm Z Y)))

------------------------------------------------------------------------
-- Equational reasoning.

infix  1 begin_
infixr 2 _≈⟨_⟩_ _≡⟨⟩_
infix  3 _∎

begin_ : ∀ {X Y} → X ≈ Y → X ≈ Y
begin p = p

_≈⟨_⟩_ : ∀ X {Y Z} → X ≈ Y → Y ≈ Z → X ≈ Z
X ≈⟨ p ⟩ q = ≈-trans p q

_≡⟨⟩_ : ∀ X {Y} → X ≈ Y → X ≈ Y
X ≡⟨⟩ q = q

_∎ : ∀ X → X ≈ X
X ∎ = ≈-refl

------------------------------------------------------------------------
-- concatMap ("Σ over a bag").

cm : (Tuple → Bag) → Bag → Bag
cm g []      = []
cm g (x ∷ X) = g x ++ cm g X

cm-++ : ∀ g X Y → cm g (X ++ Y) ≡ cm g X ++ cm g Y
cm-++ g []      Y = refl
cm-++ g (x ∷ X) Y = trans (cong (g x ++_) (cm-++ g X Y)) (sym (++-assocL (g x) (cm g X) (cm g Y)))

cm-fuse : ∀ g f X → cm g (cm f X) ≡ cm (λ x → cm g (f x)) X
cm-fuse g f []      = refl
cm-fuse g f (x ∷ X) = trans (cm-++ g (f x) (cm f X)) (cong (cm g (f x) ++_) (cm-fuse g f X))

cm-single : ∀ X → cm (λ x → x ∷ []) X ≡ X
cm-single []      = refl
cm-single (x ∷ X) = cong (x ∷_) (cm-single X)

cm-nil : ∀ X → cm (λ _ → []) X ≡ []
cm-nil []      = refl
cm-nil (x ∷ X) = cm-nil X

cm-sum : ∀ g h X → cm (λ x → g x ++ h x) X ≈ cm g X ++ cm h X
cm-sum g h []      = ≈-refl
cm-sum g h (x ∷ X) =
  begin
    (g x ++ h x) ++ cm (λ x → g x ++ h x) X
  ≈⟨ ++-cong (≈-refl {g x ++ h x}) (cm-sum g h X) ⟩
    (g x ++ h x) ++ (cm g X ++ cm h X)
  ≈⟨ ++-interchange (g x) (h x) (cm g X) (cm h X) ⟩
    (g x ++ cm g X) ++ (h x ++ cm h X)
  ∎

-- Predicates on all elements of a bag.
All : (Tuple → Set) → Bag → Set
All P []      = ⊤
All P (x ∷ X) = P x × All P X

All-++ : ∀ {P} X Y → All P X → All P Y → All P (X ++ Y)
All-++ []      Y _        q = q
All-++ (x ∷ X) Y (p , ps) q = p , All-++ X Y ps q

All-++ˡ : ∀ {P} X Y → All P (X ++ Y) → All P X
All-++ˡ []      Y _        = tt
All-++ˡ (x ∷ X) Y (p , ps) = p , All-++ˡ X Y ps

All-++ʳ : ∀ {P} X Y → All P (X ++ Y) → All P Y
All-++ʳ []      Y q        = q
All-++ʳ (x ∷ X) Y (p , ps) = All-++ʳ X Y ps

All-cm : ∀ {P Q} g X → All Q X → (∀ x → Q x → All P (g x)) → All P (cm g X)
All-cm g []      _        _ = tt
All-cm g (x ∷ X) (q , qs) f = All-++ (g x) (cm g X) (f x q) (All-cm g X qs f)

All-map : ∀ {P Q} X → (∀ x → P x → Q x) → All P X → All Q X
All-map []      f _        = tt
All-map (x ∷ X) f (p , ps) = f x p , All-map X f ps

cm-ext : ∀ {P} g h X → All P X → (∀ x → P x → g x ≈ h x) → cm g X ≈ cm h X
cm-ext g h []      _        _ = ≈-refl
cm-ext g h (x ∷ X) (p , ps) f = ++-cong (f x p) (cm-ext g h X ps f)

cm-ext' : ∀ g h X → (∀ x → g x ≈ h x) → cm g X ≈ cm h X
cm-ext' g h X f = cm-ext {λ _ → ⊤} g h X (all-tt X) (λ x _ → f x)
  where
  all-tt : ∀ X → All (λ _ → ⊤) X
  all-tt []      = tt
  all-tt (x ∷ X) = tt , all-tt X

------------------------------------------------------------------------
-- Membership through counts, and invariance of cm under ≈.

private
  pos : Nat → Set
  pos zero    = ⊥
  pos (suc _) = ⊤

  count-head : ∀ a X → count a (a ∷ X) ≡ suc (count a X)
  count-head a X rewrite eqT-refl a = refl

-- An element of positive count satisfies every predicate true of all
-- elements.
All-elem : ∀ {P} a X → pos (count a X) → All P X → P a
All-elem a (x ∷ X) c (p , ps) with eqT a x in e
... | true  = subst _ (sym (eqT-sound a x (subst T (sym e) tt))) p
... | false = All-elem a X c ps

All-from : ∀ {P} X → (∀ a → pos (count a X) → P a) → All P X
All-from []      f = tt
All-from {P} (x ∷ X) f = f x (subst pos (sym (count-head x X)) tt) , All-from X g
  where
  g : ∀ a → pos (count a X) → P a
  g a c with eqT a x in e
  ... | true  = f a (subst (λ n → pos n) (sym (cong-if e)) tt)
    where
    cong-if : eqT a x ≡ true → count a (x ∷ X) ≡ suc (count a X)
    cong-if e' rewrite e' = refl
  ... | false = f a (subst pos (sym (cong-if' e)) c)
    where
    cong-if' : eqT a x ≡ false → count a (x ∷ X) ≡ count a X
    cong-if' e' rewrite e' = refl

All-≈ : ∀ {P} X Y → X ≈ Y → All P X → All P Y
All-≈ X Y p a = All-from Y (λ b c → All-elem b X (subst pos (sym (at p b)) c) a)

private
  remove : Tuple → Bag → Bag
  remove a []      = []
  remove a (x ∷ X) = if eqT a x then X else (x ∷ remove a X)

  rem-cm : ∀ g a X → pos (count a X) → cm g X ≈ g a ++ cm g (remove a X)
  rem-cm g a (x ∷ X) c with eqT a x in e
  ... | true  rewrite eqT-sound a x (subst T (sym e) tt) = ≈-refl
  ... | false =
    begin
      g x ++ cm g X
    ≈⟨ ++-cong (≈-refl {g x}) (rem-cm g a X c) ⟩
      g x ++ (g a ++ cm g (remove a X))
    ≈⟨ ≈-sym (++-assoc (g x) (g a) _) ⟩
      (g x ++ g a) ++ cm g (remove a X)
    ≈⟨ ++-cong (++-comm (g x) (g a)) (≈-refl {cm g (remove a X)}) ⟩
      (g a ++ g x) ++ cm g (remove a X)
    ≈⟨ ++-assoc (g a) (g x) _ ⟩
      g a ++ cm g (x ∷ remove a X)
    ∎

  rem-≈ : ∀ a X → pos (count a X) → X ≈ a ∷ remove a X
  rem-≈ a X c =
    subst (λ Z → Z ≈ a ∷ remove a X) (cm-single X)
      (subst (λ Z → cm (λ x → x ∷ []) X ≈ a ∷ Z) (cm-single (remove a X))
        (rem-cm (λ x → x ∷ []) a X c))

cm-cong : ∀ g X Y → X ≈ Y → cm g X ≈ cm g Y
cm-cong g [] []      p = ≈-refl
cm-cong g [] (y ∷ Y) p = ⊥-elim (subst pos (sym (trans (at p y) (count-head y Y))) tt)
cm-cong g (x ∷ X) Y p =
  begin
    g x ++ cm g X
  ≈⟨ ++-cong (≈-refl {g x}) (cm-cong g X (remove x Y) tail) ⟩
    g x ++ cm g (remove x Y)
  ≈⟨ ≈-sym (rem-cm g x Y inY) ⟩
    cm g Y
  ∎
  where
  inY : pos (count x Y)
  inY = subst pos (trans (sym (count-head x X)) (at p x)) tt
  tail : X ≈ remove x Y
  tail = ++-cancelˡ X (remove x Y) (x ∷ []) (≈-trans p (rem-≈ x Y inY))

-- Swapping a double sum.
cm-swap : ∀ (h : Tuple → Tuple → Bag) A D →
          cm (λ d → cm (λ c → h c d) A) D ≈ cm (λ c → cm (λ d → h c d) D) A
cm-swap h A []      = ≡→≈ (sym (cm-nil A))
cm-swap h A (d ∷ D) =
  begin
    cm (λ c → h c d) A ++ cm (λ d → cm (λ c → h c d) A) D
  ≈⟨ ++-cong (≈-refl {cm (λ c → h c d) A}) (cm-swap h A D) ⟩
    cm (λ c → h c d) A ++ cm (λ c → cm (λ d → h c d) D) A
  ≈⟨ ≈-sym (cm-sum (λ c → h c d) (λ c → cm (λ d → h c d) D) A) ⟩
    cm (λ c → h c d ++ cm (λ d → h c d) D) A
  ∎

------------------------------------------------------------------------
-- Tensor product of bags: { x ++ y | x ∈ X, y ∈ Y } with multiplicity.

prod : Bag → Bag → Bag
prod X Y = cm (λ x → cm (λ y → (x ++ y) ∷ []) Y) X

prod-congˡ : ∀ {X X'} Y → X ≈ X' → prod X Y ≈ prod X' Y
prod-congˡ {X} {X'} Y p = cm-cong _ X X' p

prod-congʳ : ∀ X {Y Y'} → Y ≈ Y' → prod X Y ≈ prod X Y'
prod-congʳ X {Y} {Y'} p = cm-ext' _ _ X (λ x → cm-cong _ Y Y' p)

prod-++ˡ : ∀ X X' Y → prod (X ++ X') Y ≡ prod X Y ++ prod X' Y
prod-++ˡ X X' Y = cm-++ _ X X'

prod-++ʳ : ∀ X Y Y' → prod X (Y ++ Y') ≈ prod X Y ++ prod X Y'
prod-++ʳ X Y Y' =
  ≈-trans (cm-ext' _ (λ x → cm (λ y → (x ++ y) ∷ []) Y ++ cm (λ y → (x ++ y) ∷ []) Y') X
             (λ x → ≡→≈ (cm-++ _ Y Y')))
          (cm-sum _ _ X)

prod-nilʳ : ∀ X → prod X [] ≡ []
prod-nilʳ X = cm-nil X

prod-unitʳ : ∀ X → prod X ([] ∷ []) ≈ X
prod-unitʳ X =
  ≈-trans (cm-ext' _ (λ x → x ∷ []) X (λ x → ≡→≈ (cong (λ z → z ∷ []) (++-[]L x))))
          (≡→≈ (cm-single X))

prod-unitˡ : ∀ Y → prod ([] ∷ []) Y ≈ Y
prod-unitˡ Y = ≡→≈ (trans (++-[]L _) (cm-single Y))

prod-assoc : ∀ X Y Z → prod (prod X Y) Z ≈ prod X (prod Y Z)
prod-assoc X Y Z =
  begin
    prod (prod X Y) Z
  ≈⟨ ≡→≈ (cm-fuse _ _ X) ⟩
    cm (λ x → cm k (cm (λ y → (x ++ y) ∷ []) Y)) X
  ≈⟨ cm-ext' _ _ X (λ x → ≡→≈ (cm-fuse k _ Y)) ⟩
    cm (λ x → cm (λ y → k (x ++ y) ++ []) Y) X
  ≈⟨ cm-ext' _ _ X (λ x → cm-ext' _ _ Y (λ y → ≡→≈ (trans (++-[]L _)
       (cong (λ f → cm f Z) refl)))) ⟩
    cm (λ x → cm (λ y → cm (λ z → ((x ++ y) ++ z) ∷ []) Z) Y) X
  ≈⟨ cm-ext' _ _ X (λ x → cm-ext' _ _ Y (λ y → cm-ext' _ _ Z (λ z →
       ≡→≈ (cong (λ w → w ∷ []) (++-assocL x y z))))) ⟩
    cm (λ x → cm (λ y → cm (λ z → (x ++ (y ++ z)) ∷ []) Z) Y) X
  ≈⟨ cm-ext' _ _ X (λ x → cm-ext' _ _ Y (λ y → ≈-sym (≡→≈
       (trans (cm-fuse (λ v → (x ++ v) ∷ []) (λ z → (y ++ z) ∷ []) Z)
              (cong (λ f → cm f Z) refl))))) ⟩
    cm (λ x → cm (λ y → cm (λ v → (x ++ v) ∷ []) (cm (λ z → (y ++ z) ∷ []) Z)) Y) X
  ≈⟨ cm-ext' _ _ X (λ x → ≡→≈ (sym (cm-fuse (λ v → (x ++ v) ∷ []) _ Y))) ⟩
    prod X (prod Y Z)
  ∎
  where
  k : Tuple → Bag
  k w = cm (λ z → (w ++ z) ∷ []) Z

-- The tensor distributes over sums indexed by a bag.
prod-cmʳ : ∀ C g U → prod C (cm g U) ≈ cm (λ u → prod C (g u)) U
prod-cmʳ C g U =
  begin
    cm (λ c → cm (λ y → (c ++ y) ∷ []) (cm g U)) C
  ≈⟨ cm-ext' _ _ C (λ c → ≡→≈ (cm-fuse _ g U)) ⟩
    cm (λ c → cm (λ u → cm (λ y → (c ++ y) ∷ []) (g u)) U) C
  ≈⟨ ≈-sym (cm-swap (λ c u → cm (λ y → (c ++ y) ∷ []) (g u)) C U) ⟩
    cm (λ u → prod C (g u)) U
  ∎

prod-cmˡ : ∀ g U D → prod (cm g U) D ≡ cm (λ u → prod (g u) D) U
prod-cmˡ g U D = cm-fuse _ g U
