{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Machine check of the base-dimension-4 counterexample to the
-- relative Gray-generator presentation of Grothendieck constructions
-- (notes/conjectures/answered/fibration-presentations-all-dimensions-
-- 2026-11-19.md, Followup §1).
--
-- Setting.  One 0-cell; 1-cells are words in {g, t} (position 0 is the
-- leftmost letter).  2-generators rewrite a substring:
--     d : g ⇒ gg,     c : t ⇒ tg,     u : gtt ⇒ t.
-- A 2-path is a list of steps (generator, position), executed left to
-- right.  Strict interchange swaps two adjacent steps acting on
-- disjoint windows.  3-generators (applied in any 2-cell context):
--     D : c0;d1     ⇛ c0;c0          (on t)
--     M : u0;c0     ⇛ c2;u0          (on gtt)
--     V : c1;u2;u0  ⇛ d0;u1;u0       (on gttt)
--     K : d0;d1     ⇛ d0;d0          (on g)       (κ in the note)
--
-- What is proved here, with no postulates:
--   * every 2-path gtttt ⇒ t has exactly 5 steps (counting argument);
--   * every such 2-path occurs in the complete enumeration 'validList'
--     (completeness proved), which has 18 entries, and every one of
--     them carries a label in 'table';
--   * the labelling 'classOf' (8 labels) is invariant under strict
--     interchange;
--   * every contextual 3-generator application out of a 2-path labelled
--     R is a V-step into a path labelled Bd or Ee;
--   * no contextual 3-generator application leaves a path labelled Ee;
--   * hence (noShortSide): no chain of 3-generator applications and
--     interchanges starting with a step from R into the base vertex E
--     ever reaches L (labels Lr, Ll).  This is the statement that the
--     short side R → E → L of the pentagon has no positive lift.
-- Positive controls: the eight edges of the note's graph are exhibited
-- concretely, including the long side R → Bd → Bc → C → Lr → Ll.
--
-- Not formalised (standard, stated in the note): that the 2-cells of
-- the free strict 2-category are exactly rewriting paths modulo
-- adjacent disjoint swaps; that every 3-cell of the free strict
-- 3-category is a composite of contextual applications of generators,
-- so these chains exhaust the positive 3-cells; that each label is a
-- single interchange class (only label invariance is proved, which is
-- all noShortSide needs); and the base projection 'base', which is set
-- by hand from the note (V ↦ whiskered α; D, M, κ ↦ identities).
------------------------------------------------------------------------
module CaTTExp.Fibration.PentagonCounterexample where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Sigma

------------------------------------------------------------------------
-- Minimal prelude

data ⊥ : Set where

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

infixr 2 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

infixr 6 _&&_
_&&_ : Bool → Bool → Bool
true  && b = b
false && _ = false

infixr 5 _||_
_||_ : Bool → Bool → Bool
true  || _ = true
false || b = b

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else _ = x
if false then _ else y = y

infixr 5 _++_
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

concatMap : {A B : Set} → (A → List B) → List A → List B
concatMap f []       = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

length : {A : Set} → List A → Nat
length []       = 0
length (_ ∷ xs) = suc (length xs)

filter : {A : Set} → (A → Bool) → List A → List A
filter f [] = []
filter f (x ∷ xs) = if f x then x ∷ filter f xs else filter f xs

allB : {A : Set} → (A → Bool) → List A → Bool
allB f []       = true
allB f (x ∷ xs) = f x && allB f xs

mapM : {A B : Set} → (A → B) → Maybe A → Maybe B
mapM f nothing  = nothing
mapM f (just x) = just (f x)

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  here  : ∀ {xs}   → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

∈-++ˡ : {A : Set} {x : A} {xs : List A} (ys : List A) → x ∈ xs → x ∈ (xs ++ ys)
∈-++ˡ ys here      = here
∈-++ˡ ys (there m) = there (∈-++ˡ ys m)

∈-++ʳ : {A : Set} {x : A} (xs : List A) {ys : List A} → x ∈ ys → x ∈ (xs ++ ys)
∈-++ʳ []       m = m
∈-++ʳ (_ ∷ xs) m = there (∈-++ʳ xs m)

∈-map : {A B : Set} (f : A → B) {x : A} {xs : List A} → x ∈ xs → f x ∈ map f xs
∈-map f here      = here
∈-map f (there m) = there (∈-map f m)

∈-concatMap : {A B : Set} (f : A → List B) {x : A} {y : B} {xs : List A}
            → x ∈ xs → y ∈ f x → y ∈ concatMap f xs
∈-concatMap f {xs = x ∷ xs} here      m = ∈-++ˡ (concatMap f xs) m
∈-concatMap f {xs = z ∷ xs} (there i) m = ∈-++ʳ (f z) (∈-concatMap f i m)

∈-filter : {A : Set} (f : A → Bool) {x : A} {xs : List A}
         → x ∈ xs → f x ≡ true → x ∈ filter f xs
∈-filter f {xs = y ∷ ys} here e rewrite e = here
∈-filter f {xs = y ∷ ys} (there m) e with f y
... | true  = there (∈-filter f m e)
... | false = ∈-filter f m e

&&-l : ∀ {a b} → (a && b) ≡ true → a ≡ true
&&-l {true} _ = refl
&&-l {false} ()

&&-r : ∀ {a b} → (a && b) ≡ true → b ≡ true
&&-r {true} e = e
&&-r {false} ()

allB-sound : {A : Set} (f : A → Bool) {x : A} {xs : List A}
           → allB f xs ≡ true → x ∈ xs → f x ≡ true
allB-sound f {xs = y ∷ ys} e here      = &&-l {f y} e
allB-sound f {xs = y ∷ ys} e (there m) = allB-sound f (&&-r {f y} e) m

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl px = px

||-split : ∀ {a b} → (a || b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
||-split {true} _ = inl refl
||-split {false} e = inr e

------------------------------------------------------------------------
-- Natural-number arithmetic

+-zero : ∀ n → n + 0 ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-zero n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

+-cancelʳ : ∀ a b k → a + k ≡ b + k → a ≡ b
+-cancelʳ a b zero    e = trans (sym (+-zero a)) (trans e (+-zero b))
+-cancelʳ a b (suc k) e =
  +-cancelʳ a b k (suc-inj (trans (sym (+-suc a k)) (trans e (+-suc b k))))

-- x + (k + y) ≡ k + (x + y)
+-swap : ∀ x k y → x + (k + y) ≡ k + (x + y)
+-swap x k y = trans (sym (+-assoc x k y))
               (trans (cong (_+ y) (+-comm x k)) (+-assoc k x y))

------------------------------------------------------------------------
-- Words and 2-generators

data Letter : Set where
  g t : Letter

Word : Set
Word = List Letter

data G2 : Set where
  d c u : G2

src2 tgt2 : G2 → Word
src2 d = g ∷ []
src2 c = t ∷ []
src2 u = g ∷ t ∷ t ∷ []
tgt2 d = g ∷ g ∷ []
tgt2 c = t ∷ g ∷ []
tgt2 u = t ∷ []

data Step : Set where
  st : G2 → Nat → Step

-- Replace the prefix s of the word by tg (fails if s is not a prefix).
rewriteHere : Word → Word → Word → Maybe Word
rewriteHere []      tg w       = just (tg ++ w)
rewriteHere (_ ∷ _) tg []      = nothing
rewriteHere (g ∷ s) tg (g ∷ w) = rewriteHere s tg w
rewriteHere (g ∷ s) tg (t ∷ w) = nothing
rewriteHere (t ∷ s) tg (g ∷ w) = nothing
rewriteHere (t ∷ s) tg (t ∷ w) = rewriteHere s tg w

-- Apply a generator at a position of a word.
apply : Step → Word → Maybe Word
apply (st G zero)    w       = rewriteHere (src2 G) (tgt2 G) w
apply (st G (suc i)) []      = nothing
apply (st G (suc i)) (x ∷ w) = mapM (x ∷_) (apply (st G i) w)

mutual
 run : Word → List Step → Maybe Word
 run w []      = just w
 run w (s ∷ p) = runM (apply s w) p

 runM : Maybe Word → List Step → Maybe Word
 runM nothing   p = nothing
 runM (just w1) p = run w1 p

start : Word
start = g ∷ t ∷ t ∷ t ∷ t ∷ []

goal : Word
goal = t ∷ []

-- A 2-cell gtttt ⇒ t of the free strict 2-category, as a path.
Valid : List Step → Set
Valid p = run start p ≡ just goal

------------------------------------------------------------------------
-- Every valid path has exactly 5 steps

δ : Letter → Letter → Nat
δ g g = 1
δ g t = 0
δ t g = 0
δ t t = 1

cnt : Letter → Word → Nat
cnt ℓ []      = 0
cnt ℓ (x ∷ w) = δ ℓ x + cnt ℓ w

cnt-++ : ∀ ℓ a b → cnt ℓ (a ++ b) ≡ cnt ℓ a + cnt ℓ b
cnt-++ ℓ []      b = refl
cnt-++ ℓ (x ∷ a) b = trans (cong (δ ℓ x +_) (cnt-++ ℓ a b)) (sym (+-assoc (δ ℓ x) (cnt ℓ a) (cnt ℓ b)))

rh-cnt : ∀ ℓ s tg w {w'} → rewriteHere s tg w ≡ just w'
       → cnt ℓ w' + cnt ℓ s ≡ cnt ℓ w + cnt ℓ tg
rh-cnt ℓ [] tg w refl = trans (+-zero _) (trans (cnt-++ ℓ tg w) (+-comm (cnt ℓ tg) (cnt ℓ w)))
rh-cnt ℓ (g ∷ s) tg (g ∷ w) {w'} e =
  trans (+-swap (cnt ℓ w') (δ ℓ g) (cnt ℓ s))
  (trans (cong (δ ℓ g +_) (rh-cnt ℓ s tg w e)) (sym (+-assoc (δ ℓ g) (cnt ℓ w) (cnt ℓ tg))))
rh-cnt ℓ (t ∷ s) tg (t ∷ w) {w'} e =
  trans (+-swap (cnt ℓ w') (δ ℓ t) (cnt ℓ s))
  (trans (cong (δ ℓ t +_) (rh-cnt ℓ s tg w e)) (sym (+-assoc (δ ℓ t) (cnt ℓ w) (cnt ℓ tg))))
rh-cnt ℓ (g ∷ s) tg [] ()
rh-cnt ℓ (t ∷ s) tg [] ()
rh-cnt ℓ (g ∷ s) tg (t ∷ w) ()
rh-cnt ℓ (t ∷ s) tg (g ∷ w) ()

apply-cnt : ∀ ℓ G i w {w'} → apply (st G i) w ≡ just w'
          → cnt ℓ w' + cnt ℓ (src2 G) ≡ cnt ℓ w + cnt ℓ (tgt2 G)
apply-cnt ℓ G zero w e = rh-cnt ℓ (src2 G) (tgt2 G) w e
apply-cnt ℓ G (suc i) [] ()
apply-cnt ℓ G (suc i) (x ∷ w) e with apply (st G i) w in e1
apply-cnt ℓ G (suc i) (x ∷ w) () | nothing
apply-cnt ℓ G (suc i) (x ∷ w) refl | just w1 =
  trans (+-assoc (δ ℓ x) (cnt ℓ w1) _)
  (trans (cong (δ ℓ x +_) (apply-cnt ℓ G i w e1)) (sym (+-assoc (δ ℓ x) (cnt ℓ w) _)))

isU : Step → Nat
isU (st u _) = 1
isU (st d _) = 0
isU (st c _) = 0

isCD : Step → Nat
isCD (st u _) = 0
isCD (st d _) = 1
isCD (st c _) = 1

nU nCD : List Step → Nat
nU []      = 0
nU (s ∷ p) = isU s + nU p
nCD []      = 0
nCD (s ∷ p) = isCD s + nCD p

-- one step: t-count drops by isU, g-count changes by isCD - isU
+1≡suc : ∀ a → a + 1 ≡ suc a
+1≡suc a = trans (+-suc a 0) (cong suc (+-zero a))

step-t : ∀ s w {w1} → apply s w ≡ just w1 → cnt t w1 + isU s ≡ cnt t w
step-t (st d i) w {w1} e = trans (apply-cnt t d i w e) (+-zero (cnt t w))
step-t (st c i) w {w1} e = trans (+-zero (cnt t w1)) (+-cancelʳ (cnt t w1) (cnt t w) 1 (apply-cnt t c i w e))
step-t (st u i) w {w1} e =
  suc-inj (trans (sym (+-suc (cnt t w1) 1))
          (trans (apply-cnt t u i w e) (+1≡suc (cnt t w))))

step-g : ∀ s w {w1} → apply s w ≡ just w1 → cnt g w1 + isU s ≡ cnt g w + isCD s
step-g (st d i) w {w1} e =
  trans (+-zero (cnt g w1))
    (suc-inj (trans (sym (+1≡suc (cnt g w1)))
             (trans (apply-cnt g d i w e) (+-suc (cnt g w) 1))))
step-g (st c i) w {w1} e = apply-cnt g c i w e
step-g (st u i) w {w1} e = apply-cnt g u i w e

run-cnt : ∀ w p {w'} → run w p ≡ just w'
        → (cnt t w' + nU p ≡ cnt t w) × (cnt g w' + nU p ≡ cnt g w + nCD p)
run-cnt w [] refl = +-zero _ , trans (+-zero _) (sym (+-zero _))
run-cnt w (s ∷ p) {w'} e with apply s w in e1
run-cnt w (s ∷ p) {w'} () | nothing
run-cnt w (s ∷ p) {w'} e | just w1 with run-cnt w1 p e
... | ht , hg =
  trans (+-swap (cnt t w') (isU s) (nU p))
    (trans (cong (isU s +_) ht) (trans (+-comm (isU s) (cnt t w1)) (step-t s w e1))) ,
  trans (+-swap (cnt g w') (isU s) (nU p))
    (trans (cong (isU s +_) hg)
    (trans (sym (+-assoc (isU s) (cnt g w1) (nCD p)))
    (trans (cong (_+ nCD p) (trans (+-comm (isU s) (cnt g w1)) (step-g s w e1)))
    (trans (+-assoc (cnt g w) (isCD s) (nCD p)) refl))))

len-split : ∀ p → length p ≡ nU p + nCD p
len-split [] = refl
len-split (st u _ ∷ p) = cong suc (len-split p)
len-split (st d _ ∷ p) = trans (cong suc (len-split p)) (sym (+-suc (nU p) (nCD p)))
len-split (st c _ ∷ p) = trans (cong suc (len-split p)) (sym (+-suc (nU p) (nCD p)))

valid-length : ∀ p → Valid p → length p ≡ 5
valid-length p v with run-cnt start p v
... | ht , hg = trans (len-split p) (trans (cong (_+ nCD p) u3) (cong (3 +_) cd2))
  where
  u3 : nU p ≡ 3
  u3 = suc-inj ht
  cd2 : nCD p ≡ 2
  cd2 = suc-inj (trans (sym hg) u3)

------------------------------------------------------------------------
-- Complete enumeration of the valid paths

range : Nat → List Nat
range zero    = []
range (suc n) = 0 ∷ map suc (range n)

allG2 : List G2
allG2 = d ∷ c ∷ u ∷ []

G2-in : ∀ G → G ∈ allG2
G2-in d = here
G2-in c = there here
G2-in u = there (there here)

allSteps : Word → List Step
allSteps w = concatMap (λ G → map (st G) (range (length w))) allG2

apply-pos : ∀ G i w {w'} → apply (st G i) w ≡ just w' → i ∈ range (length w)
apply-pos d zero [] ()
apply-pos c zero [] ()
apply-pos u zero [] ()
apply-pos G zero (x ∷ w) _ = here
apply-pos G (suc i) [] ()
apply-pos G (suc i) (x ∷ w) e with apply (st G i) w in e1
apply-pos G (suc i) (x ∷ w) () | nothing
apply-pos G (suc i) (x ∷ w) refl | just w1 = there (∈-map suc (apply-pos G i w e1))

step-in : ∀ s w {w'} → apply s w ≡ just w' → s ∈ allSteps w
step-in (st G i) w e =
  ∈-concatMap (λ G' → map (st G') (range (length w))) (G2-in G)
              (∈-map (st G) (apply-pos G i w e))

after : Step → Word → List (List Step × Word) → List (List Step × Word)
after s w rest = map (λ pr → (s ∷ fst pr) , snd pr) rest

mutual
 search : Nat → Word → List (List Step × Word)
 search zero    w = (([] , w) ∷ [])
 search (suc n) w = concatMap (λ s → nextS n s w (apply s w)) (allSteps w)

 nextS : Nat → Step → Word → Maybe Word → List (List Step × Word)
 nextS n s w nothing   = []
 nextS n s w (just w1) = after s w (search n w1)

search-complete : ∀ w p {w'} → run w p ≡ just w' → (p , w') ∈ search (length p) w
search-complete w [] refl = here
search-complete w (s ∷ p) {w'} e with apply s w in e1
search-complete w (s ∷ p) {w'} () | nothing
search-complete w (s ∷ p) {w'} e | just w1 =
  ∈-concatMap (λ s' → nextS (length p) s' w (apply s' w)) (step-in s w e1) lem
  where
  lem : ((s ∷ p) , w') ∈ nextS (length p) s w (apply s w)
  lem rewrite e1 = ∈-map (λ pr → (s ∷ fst pr) , snd pr) (search-complete w1 p e)

eqW : Word → Word → Bool
eqW [] [] = true
eqW (g ∷ a) (g ∷ b) = eqW a b
eqW (t ∷ a) (t ∷ b) = eqW a b
eqW _ _ = false

validList : List (List Step)
validList = map fst (filter (λ pr → eqW (snd pr) goal) (search 5 start))

valid-in : ∀ p → Valid p → p ∈ validList
valid-in p v =
  ∈-map fst (∈-filter (λ pr → eqW (snd pr) goal)
    (subst5 (search-complete start p v)) refl)
  where
  subst5 : (p , goal) ∈ search (length p) start → (p , goal) ∈ search 5 start
  subst5 m rewrite valid-length p v = m

eighteen : length validList ≡ 18
eighteen = refl

------------------------------------------------------------------------
-- The eight strict 2-cells (interchange classes), as labels

data Cls : Set where
  R Bd Bc C Lr Ll Ee El : Cls

eqG2 : G2 → G2 → Bool
eqG2 d d = true
eqG2 c c = true
eqG2 u u = true
eqG2 _ _ = false

eqN : Nat → Nat → Bool
eqN zero zero = true
eqN (suc m) (suc n) = eqN m n
eqN _ _ = false

eqStep : Step → Step → Bool
eqStep (st G i) (st H j) = eqG2 G H && eqN i j

eqPath : List Step → List Step → Bool
eqPath [] [] = true
eqPath (s ∷ p) (r ∷ q) = eqStep s r && eqPath p q
eqPath _ _ = false

table : List (List Step × Cls)
table =
  ((st c 1 ∷ st c 1 ∷ st u 3 ∷ st u 2 ∷ st u 0 ∷ []) , Bc) ∷
  ((st c 1 ∷ st c 3 ∷ st u 4 ∷ st u 2 ∷ st u 0 ∷ []) , R) ∷
  ((st c 1 ∷ st d 0 ∷ st u 3 ∷ st u 1 ∷ st u 0 ∷ []) , C) ∷
  ((st c 1 ∷ st d 2 ∷ st u 3 ∷ st u 2 ∷ st u 0 ∷ []) , Bd) ∷
  ((st c 1 ∷ st u 2 ∷ st c 1 ∷ st u 2 ∷ st u 0 ∷ []) , Bc) ∷
  ((st c 1 ∷ st u 2 ∷ st d 0 ∷ st u 1 ∷ st u 0 ∷ []) , C) ∷
  ((st c 2 ∷ st c 1 ∷ st u 4 ∷ st u 2 ∷ st u 0 ∷ []) , R) ∷
  ((st c 2 ∷ st d 0 ∷ st u 1 ∷ st u 2 ∷ st u 0 ∷ []) , Ee) ∷
  ((st c 2 ∷ st d 0 ∷ st u 4 ∷ st u 1 ∷ st u 0 ∷ []) , Ee) ∷
  ((st c 2 ∷ st u 3 ∷ st c 1 ∷ st u 2 ∷ st u 0 ∷ []) , R) ∷
  ((st c 2 ∷ st u 3 ∷ st d 0 ∷ st u 1 ∷ st u 0 ∷ []) , Ee) ∷
  ((st d 0 ∷ st c 2 ∷ st u 3 ∷ st u 1 ∷ st u 0 ∷ []) , C) ∷
  ((st d 0 ∷ st c 3 ∷ st u 1 ∷ st u 2 ∷ st u 0 ∷ []) , Ee) ∷
  ((st d 0 ∷ st c 3 ∷ st u 4 ∷ st u 1 ∷ st u 0 ∷ []) , Ee) ∷
  ((st d 0 ∷ st d 0 ∷ st u 2 ∷ st u 1 ∷ st u 0 ∷ []) , Ll) ∷
  ((st d 0 ∷ st d 1 ∷ st u 2 ∷ st u 1 ∷ st u 0 ∷ []) , Lr) ∷
  ((st d 0 ∷ st u 1 ∷ st c 1 ∷ st u 2 ∷ st u 0 ∷ []) , El) ∷
  ((st d 0 ∷ st u 1 ∷ st d 0 ∷ st u 1 ∷ st u 0 ∷ []) , Ll) ∷
  []

lookupCls : List Step → List (List Step × Cls) → Maybe Cls
lookupCls p [] = nothing
lookupCls p ((q , k) ∷ tb) = if eqPath p q then just k else lookupCls p tb

classOf : List Step → Maybe Cls
classOf p = lookupCls p table

code : Cls → Nat
code R = 0
code Bd = 1
code Bc = 2
code C = 3
code Lr = 4
code Ll = 5
code Ee = 6
code El = 7

decode : Nat → Cls
decode 0 = R
decode 1 = Bd
decode 2 = Bc
decode 3 = C
decode 4 = Lr
decode 5 = Ll
decode 6 = Ee
decode _ = El

decode-code : ∀ k → decode (code k) ≡ k
decode-code R = refl
decode-code Bd = refl
decode-code Bc = refl
decode-code C = refl
decode-code Lr = refl
decode-code Ll = refl
decode-code Ee = refl
decode-code El = refl

eqN-sound : ∀ m n → eqN m n ≡ true → m ≡ n
eqN-sound zero zero _ = refl
eqN-sound (suc m) (suc n) e = cong suc (eqN-sound m n e)
eqN-sound zero (suc n) ()
eqN-sound (suc m) zero ()

eqMC : Maybe Cls → Maybe Cls → Bool
eqMC nothing nothing = true
eqMC (just a) (just b) = eqN (code a) (code b)
eqMC _ _ = false

eqMC-sound : ∀ a b → eqMC a b ≡ true → a ≡ b
eqMC-sound nothing nothing _ = refl
eqMC-sound (just a) (just b) e =
  cong just (trans (sym (decode-code a)) (trans (cong decode (eqN-sound _ _ e)) (decode-code b)))
eqMC-sound nothing (just _) ()
eqMC-sound (just _) nothing ()

eqMC-refl : ∀ a → eqMC a a ≡ true
eqMC-refl nothing = refl
eqMC-refl (just R) = refl
eqMC-refl (just Bd) = refl
eqMC-refl (just Bc) = refl
eqMC-refl (just C) = refl
eqMC-refl (just Lr) = refl
eqMC-refl (just Ll) = refl
eqMC-refl (just Ee) = refl
eqMC-refl (just El) = refl

isJust : {A : Set} → Maybe A → Bool
isJust nothing = false
isJust (just _) = true

every-valid-labelled : allB (λ p → isJust (classOf p)) validList ≡ true
every-valid-labelled = refl

------------------------------------------------------------------------
-- Strict interchange: swap adjacent steps acting on disjoint windows

leq : Nat → Nat → Bool
leq zero _ = true
leq (suc m) zero = false
leq (suc m) (suc n) = leq m n

_∸_ : Nat → Nat → Nat
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

|s| |t| : G2 → Nat
|s| G = length (src2 G)
|t| G = length (tgt2 G)

-- steps s1 = (G1,i1) then s2 = (G2,i2); s2 acts on the word after s1.
swap2 : Step → Step → Maybe (Step × Step)
swap2 (st G1 i1) (st G2 i2) =
  if leq (i2 + |s| G2) i1
    then just (st G2 i2 , st G1 ((i1 ∸ |s| G2) + |t| G2))       -- s2 left of s1's output
    else (if leq (i1 + |t| G1) i2
            then just (st G2 ((i2 ∸ |t| G1) + |s| G1) , st G1 i1) -- s2 right of s1's output
            else nothing)

sw2M : List Step → Maybe (Step × Step) → Maybe (List Step)
sw2M rest nothing = nothing
sw2M rest (just (a , b)) = just (a ∷ b ∷ rest)

swapAt : Nat → List Step → Maybe (List Step)
swapAt zero (s1 ∷ s2 ∷ rest) = sw2M rest (swap2 s1 s2)
swapAt zero _ = nothing
swapAt (suc k) [] = nothing
swapAt (suc k) (s ∷ p) = mapM (s ∷_) (swapAt k p)

swapAt-pos : ∀ k p {q} → swapAt k p ≡ just q → k ∈ range (length p)
swapAt-pos zero (s1 ∷ s2 ∷ rest) _ = here
swapAt-pos zero [] ()
swapAt-pos zero (s1 ∷ []) ()
swapAt-pos (suc k) [] ()
swapAt-pos (suc k) (s ∷ p) e with swapAt k p in e1
swapAt-pos (suc k) (s ∷ p) () | nothing
swapAt-pos (suc k) (s ∷ p) refl | just q = there (∈-map suc (swapAt-pos k p e1))

-- Interchange between two 2-cells gtttt ⇒ t.
record Interch (p q : List Step) : Set where
  field
    vp : Valid p
    vq : Valid q
    pos : Nat
    swp : swapAt pos p ≡ just q

okM : List Step → Maybe (List Step) → Bool
okM p nothing  = true
okM p (just q) = eqMC (classOf q) (classOf p)

swapOK : List Step → Nat → Bool
swapOK p k = okM p (swapAt k p)

swaps-preserve-labels : allB (λ p → allB (swapOK p) (range 5)) validList ≡ true
swaps-preserve-labels = refl

interch-label : ∀ {p q} → Interch p q → classOf q ≡ classOf p
interch-label {p} {q} I = go (allB-sound (swapOK p) inner kin)
  where
  open Interch I
  inner : allB (swapOK p) (range 5) ≡ true
  inner = allB-sound (λ p' → allB (swapOK p') (range 5)) swaps-preserve-labels (valid-in p vp)
  kin : pos ∈ range 5
  kin = subst (λ n → pos ∈ range n) (valid-length p vp) (swapAt-pos pos p swp)
  go : swapOK p pos ≡ true → classOf q ≡ classOf p
  go e = eqMC-sound _ _ (subst (λ m → okM p m ≡ true) swp e)

------------------------------------------------------------------------
-- 3-generators and their contextual applications

data G3 : Set where
  D M V K : G3

w3 : G3 → Word
w3 D = t ∷ []
w3 M = g ∷ t ∷ t ∷ []
w3 V = g ∷ t ∷ t ∷ t ∷ []
w3 K = g ∷ []

src3 tgt3 : G3 → List Step
src3 D = st c 0 ∷ st d 1 ∷ []
src3 M = st u 0 ∷ st c 0 ∷ []
src3 V = st c 1 ∷ st u 2 ∷ st u 0 ∷ []
src3 K = st d 0 ∷ st d 1 ∷ []
tgt3 D = st c 0 ∷ st c 0 ∷ []
tgt3 M = st c 2 ∷ st u 0 ∷ []
tgt3 V = st d 0 ∷ st u 1 ∷ st u 0 ∷ []
tgt3 K = st d 0 ∷ st d 0 ∷ []

-- Each 3-generator is well typed: source and target 2-paths are parallel.
typed : (G : G3) → run (w3 G) (src3 G) ≡ run (w3 G) (tgt3 G)
typed D = refl
typed M = refl
typed V = refl
typed K = refl

shift : Nat → List Step → List Step
shift o = map (λ { (st G i) → st G (i + o) })

isPrefixW : Word → Word → Bool
isPrefixW [] _ = true
isPrefixW (_ ∷ _) [] = false
isPrefixW (g ∷ a) (g ∷ b) = isPrefixW a b
isPrefixW (t ∷ a) (t ∷ b) = isPrefixW a b
isPrefixW _ _ = false

-- word v occurs in w at offset o
isAt : Nat → Word → Word → Bool
isAt zero v w = isPrefixW v w
isAt (suc o) v [] = false
isAt (suc o) v (_ ∷ w) = isAt o v w

isPrefixP : List Step → List Step → Bool
isPrefixP [] _ = true
isPrefixP (_ ∷ _) [] = false
isPrefixP (s ∷ a) (r ∷ b) = eqStep s r && isPrefixP a b

dropN : {A : Set} → Nat → List A → List A
dropN zero xs = xs
dropN (suc n) [] = []
dropN (suc n) (_ ∷ xs) = dropN n xs

-- Apply generator G whiskered by the word context (offset o) and the
-- 2-cell context (the first k steps before, the rest after).
-- w is the current word before step k.
mutual
 apply3 : G3 → Nat → Nat → Word → List Step → Maybe (List Step)
 apply3 G zero o w p =
   if isAt o (w3 G) w
     then (if isPrefixP (shift o (src3 G)) p
             then just (shift o (tgt3 G) ++ dropN (length (src3 G)) p)
             else nothing)
     else nothing
 apply3 G (suc k) o w [] = nothing
 apply3 G (suc k) o w (s ∷ p) = a3M G k o s p (apply s w)

 a3M : G3 → Nat → Nat → Step → List Step → Maybe Word → Maybe (List Step)
 a3M G k o s p nothing   = nothing
 a3M G k o s p (just w1) = mapM (s ∷_) (apply3 G k o w1 p)

-- A generating 3-cell application between 2-cells gtttt ⇒ t.
record Edge (G : G3) (p q : List Step) : Set where
  field
    vp : Valid p
    lvl : Nat
    off : Nat
    app : apply3 G lvl off start p ≡ just q

allG3 : List G3
allG3 = D ∷ M ∷ V ∷ K ∷ []

G3-in : ∀ G → G ∈ allG3
G3-in D = here
G3-in M = there here
G3-in V = there (there here)
G3-in K = there (there (there here))

asList : {A : Set} → Maybe A → List A
asList nothing = []
asList (just x) = x ∷ []

hereEdges : Word → List Step → List (G3 × List Step)
hereEdges w p =
  concatMap (λ G → concatMap (λ o → map (λ q → G , q) (asList (apply3 G zero o w p)))
                             (range (length w)))
            allG3

mutual
 edgesFrom : Word → List Step → List (G3 × List Step)
 edgesFrom w p = hereEdges w p ++ laterAll w p

 laterAll : Word → List Step → List (G3 × List Step)
 laterAll w [] = []
 laterAll w (s ∷ p) = laterE s p (apply s w)

 laterE : Step → List Step → Maybe Word → List (G3 × List Step)
 laterE s p nothing = []
 laterE s p (just w1) = map (λ e → fst e , (s ∷ snd e)) (edgesFrom w1 p)

isAt-pos : ∀ G o w → isAt o (w3 G) w ≡ true → o ∈ range (length w)
isAt-pos D zero [] ()
isAt-pos M zero [] ()
isAt-pos V zero [] ()
isAt-pos K zero [] ()
isAt-pos G zero (_ ∷ w) _ = here
isAt-pos G (suc o) [] ()
isAt-pos G (suc o) (_ ∷ w) e = there (∈-map suc (isAt-pos G o w e))

if-true : ∀ b {A : Set} {x : Maybe A} {y : A} → (if b then x else nothing) ≡ just y → b ≡ true
if-true true _ = refl
if-true false ()

edges-complete : ∀ G k o w p {q} → apply3 G k o w p ≡ just q → (G , q) ∈ edgesFrom w p
edges-complete G zero o w p {q} e =
  ∈-++ˡ (laterAll w p)
    (∈-concatMap (λ G' → concatMap (λ o' → map (λ q' → G' , q') (asList (apply3 G' zero o' w p)))
                                    (range (length w)))
                 (G3-in G)
      (∈-concatMap (λ o' → map (λ q' → G , q') (asList (apply3 G zero o' w p)))
                   (isAt-pos G o w (if-true _ e)) mem))
  where
  mem : (G , q) ∈ map (λ q' → G , q') (asList (apply3 G zero o w p))
  mem rewrite e = here
edges-complete G (suc k) o w [] ()
edges-complete G (suc k) o w (s ∷ p) e with apply s w in e1
edges-complete G (suc k) o w (s ∷ p) () | nothing
edges-complete G (suc k) o w (s ∷ p) e | just w1 with apply3 G k o w1 p in e2
edges-complete G (suc k) o w (s ∷ p) () | just w1 | nothing
edges-complete G (suc k) o w (s ∷ p) refl | just w1 | just q' =
  ∈-++ʳ (hereEdges w (s ∷ p)) (∈-map (λ e' → fst e' , (s ∷ snd e')) (edges-complete G k o w1 p e2))

------------------------------------------------------------------------
-- The two finite facts: edges out of R, and no edges out of Ee

isV : G3 → Bool
isV V = true
isV _ = false

isV-sound : ∀ G → isV G ≡ true → G ≡ V
isV-sound V _ = refl
isV-sound D ()
isV-sound M ()
isV-sound K ()

okR : G3 × List Step → Bool
okR (G , q) = isV G && (eqMC (classOf q) (just Bd) || eqMC (classOf q) (just Ee))

isNil : {A : Set} → List A → Bool
isNil [] = true
isNil (_ ∷ _) = false

whenCls : Cls → Bool → List Step → Bool
whenCls k b p = if eqMC (classOf p) (just k) then b else true

checkR : allB (λ p → whenCls R (allB okR (edgesFrom start p)) p) validList ≡ true
checkR = refl

checkEe : allB (λ p → whenCls Ee (isNil (edgesFrom start p)) p) validList ≡ true
checkEe = refl

whenCls-elim : ∀ k b p → classOf p ≡ just k → whenCls k b p ≡ true → b ≡ true
whenCls-elim k b p e w rewrite e | eqMC-refl (just k) = w

edge-in : ∀ {G p q} → Edge G p q → (G , q) ∈ edgesFrom start p
edge-in E = edges-complete _ (Edge.lvl E) (Edge.off E) start _ (Edge.app E)

-- Every generating 3-cell out of a 2-cell labelled R is a V-step into
-- a 2-cell labelled Bd or Ee.
out-of-R : ∀ {G p q} → Edge G p q → classOf p ≡ just R
         → (G ≡ V) × ((classOf q ≡ just Bd) ⊎ (classOf q ≡ just Ee))
out-of-R {G} {p} {q} E e =
  isV-sound G (&&-l {isV G} ok) , split (||-split (&&-r {isV G} ok))
  where
  allok : allB okR (edgesFrom start p) ≡ true
  allok = whenCls-elim R _ p e
            (allB-sound (λ p₁ → whenCls R (allB okR (edgesFrom start p₁)) p₁) checkR
              (valid-in p (Edge.vp E)))
  ok : okR (G , q) ≡ true
  ok = allB-sound okR allok (edge-in E)
  split : (eqMC (classOf q) (just Bd) ≡ true) ⊎ (eqMC (classOf q) (just Ee) ≡ true)
        → (classOf q ≡ just Bd) ⊎ (classOf q ≡ just Ee)
  split (inl x) = inl (eqMC-sound _ _ x)
  split (inr x) = inr (eqMC-sound _ _ x)

-- No generating 3-cell leaves a 2-cell labelled Ee.
out-of-Ee : ∀ {G p q} → Edge G p q → classOf p ≡ just Ee → ⊥
out-of-Ee {G} {p} {q} E e = nil-empty (edgesFrom start p) isnil (edge-in E)
  where
  isnil : isNil (edgesFrom start p) ≡ true
  isnil = whenCls-elim Ee _ p e
            (allB-sound (λ p₁ → whenCls Ee (isNil (edgesFrom start p₁)) p₁) checkEe
              (valid-in p (Edge.vp E)))
  nil-empty : ∀ (xs : List (G3 × List Step)) → isNil xs ≡ true → (G , q) ∈ xs → ⊥
  nil-empty [] _ ()
  nil-empty (_ ∷ _) () _

------------------------------------------------------------------------
-- Base projection and the short side of the pentagon

data BaseV : Set where
  bR bB bC bE bL : BaseV

base : Cls → BaseV
base R = bR
base Bd = bB
base Bc = bB
base C = bC
base Lr = bL
base Ll = bL
base Ee = bE
base El = bE

baseOf : List Step → Maybe BaseV
baseOf p = mapM base (classOf p)

-- Positive 3-cells continuing from q into a 2-cell over L: chains of
-- generating 3-cell applications and interchanges (in either direction).
data ReachL : List Step → Set where
  done : ∀ {q} → baseOf q ≡ just bL → ReachL q
  gen  : ∀ {G q q'} → Edge G q q' → ReachL q' → ReachL q
  fwd  : ∀ {q q'} → Interch q q' → ReachL q' → ReachL q
  bwd  : ∀ {q q'} → Interch q' q → ReachL q' → ReachL q

stuck-at-Ee : ∀ {q} → classOf q ≡ just Ee → ReachL q → ⊥
stuck-at-Ee {q} e (done b) = bad (classOf q) e b
  where
  bad : ∀ m → m ≡ just Ee → mapM base m ≡ just bL → ⊥
  bad .(just Ee) refl ()
stuck-at-Ee e (gen E r) = out-of-Ee E e
stuck-at-Ee e (fwd I r) = stuck-at-Ee (trans (interch-label I) e) r
stuck-at-Ee {q} e (bwd {q' = q'} I r) = stuck-at-Ee (trans (sym (interch-label I)) e) r

-- The short side R → E → L has no positive lift: a generating 3-cell
-- out of (any representative of) R whose target lies over the base
-- vertex E can never be continued to a 2-cell over L.
noShortSide : ∀ {G p q} → classOf p ≡ just R → Edge G p q
            → baseOf q ≡ just bE → ReachL q → ⊥
noShortSide {G} {p} {q} e E b r with out-of-R E e
... | _ , inl qBd = notE (classOf q) b qBd
  where
  notE : ∀ m → mapM base m ≡ just bE → m ≡ just Bd → ⊥
  notE .(just Bd) () refl
... | _ , inr qEe = stuck-at-Ee qEe r

------------------------------------------------------------------------
-- Positive controls: the eight edges of the note's graph (3)–(4)

rRep bdRep bcRep cRep lrRep llRep eeRep elRep : List Step
rRep  = st c 1 ∷ st c 3 ∷ st u 4 ∷ st u 2 ∷ st u 0 ∷ []
bdRep = st c 1 ∷ st d 2 ∷ st u 3 ∷ st u 2 ∷ st u 0 ∷ []
bcRep = st c 1 ∷ st c 1 ∷ st u 3 ∷ st u 2 ∷ st u 0 ∷ []
cRep  = st c 1 ∷ st d 0 ∷ st u 3 ∷ st u 1 ∷ st u 0 ∷ []
lrRep = st d 0 ∷ st d 1 ∷ st u 2 ∷ st u 1 ∷ st u 0 ∷ []
llRep = st d 0 ∷ st d 0 ∷ st u 2 ∷ st u 1 ∷ st u 0 ∷ []
eeRep = st c 2 ∷ st d 0 ∷ st u 1 ∷ st u 2 ∷ st u 0 ∷ []
elRep = st d 0 ∷ st u 1 ∷ st c 1 ∷ st u 2 ∷ st u 0 ∷ []

labels : (classOf rRep ≡ just R) × (classOf bdRep ≡ just Bd) × (classOf bcRep ≡ just Bc)
       × (classOf cRep ≡ just C) × (classOf lrRep ≡ just Lr) × (classOf llRep ≡ just Ll)
       × (classOf eeRep ≡ just Ee) × (classOf elRep ≡ just El)
labels = refl , refl , refl , refl , refl , refl , refl , refl

mkEdge : ∀ G k o p q → Valid p → apply3 G k o start p ≡ just q → Edge G p q
mkEdge G k o p q v a = record { vp = v ; lvl = k ; off = o ; app = a }

-- long side: R -V-> Bd -D-> Bc -V-> C -V-> Lr -K-> Ll
e1 : Edge V rRep bdRep
e1 = mkEdge V 1 2 _ _ refl refl
e2 : Edge D bdRep bcRep
e2 = mkEdge D 0 1 _ _ refl refl
-- Bc -V-> C uses another representative of Bc, reached by interchange
bcRep' cRep' : List Step
bcRep' = st c 1 ∷ st u 2 ∷ st c 1 ∷ st u 2 ∷ st u 0 ∷ []
cRep'  = st c 1 ∷ st u 2 ∷ st d 0 ∷ st u 1 ∷ st u 0 ∷ []
e3 : Edge V bcRep' cRep'
e3 = mkEdge V 2 0 _ _ refl refl
e3-labels : (classOf bcRep' ≡ just Bc) × (classOf cRep' ≡ just C)
e3-labels = refl , refl
cRep'' : List Step
cRep'' = st d 0 ∷ st c 2 ∷ st u 3 ∷ st u 1 ∷ st u 0 ∷ []
e4 : Edge V cRep'' lrRep
e4 = mkEdge V 1 1 _ _ refl refl
e5 : Edge K lrRep llRep
e5 = mkEdge K 0 0 _ _ refl refl
-- short side: R -V-> Ee <-M- El -V-> Ll  (M points the wrong way)
rRep' eeRep' llRep' : List Step
rRep'  = st c 2 ∷ st u 3 ∷ st c 1 ∷ st u 2 ∷ st u 0 ∷ []
eeRep' = st c 2 ∷ st u 3 ∷ st d 0 ∷ st u 1 ∷ st u 0 ∷ []
llRep' = st d 0 ∷ st u 1 ∷ st d 0 ∷ st u 1 ∷ st u 0 ∷ []
e6 : Edge V rRep' eeRep'
e6 = mkEdge V 2 0 _ _ refl refl
eeRep'' : List Step
eeRep'' = st d 0 ∷ st c 3 ∷ st u 1 ∷ st u 2 ∷ st u 0 ∷ []
e7 : Edge M elRep eeRep''
e7 = mkEdge M 1 1 _ _ refl refl
e8 : Edge V elRep llRep'
e8 = mkEdge V 2 0 _ _ refl refl
short-labels : (classOf rRep' ≡ just R) × (classOf eeRep' ≡ just Ee)
             × (classOf eeRep'' ≡ just Ee) × (classOf llRep' ≡ just Ll)
short-labels = refl , refl , refl , refl

-- The long side really reaches L from R (positive control for ReachL):
-- the interchanges between the representatives used above.
long-side : ReachL rRep
long-side =
  gen e1 (gen e2 (fwd ib (gen e3 (fwd ic1 (fwd ic2 (gen e4 (gen e5 (done refl))))))))
  where
  ib : Interch bcRep bcRep'
  ib = record { vp = refl ; vq = refl ; pos = 1 ; swp = refl }
  ic1 : Interch cRep' cRep
  ic1 = record { vp = refl ; vq = refl ; pos = 1 ; swp = refl }
  ic2 : Interch cRep cRep''
  ic2 = record { vp = refl ; vq = refl ; pos = 0 ; swp = refl }
