------------------------------------------------------------------------
-- Symbolic supports and an exact cover check that never enumerates
-- them (notes/agda-gray-findings.md, "Fast side condition").
--
-- A support is a set of tuples. Instead of listing it, we describe it
-- by a *sequence* of items, read left to right (one entry per item
-- position, in execution order):
--
--   lit ls          one entry, any of the levels ls
--   alt ss          a union of sequences (of any lengths)
--   sch shs sg k    a substituted table chain: the chain T^sg_k of the
--                   tensor of the homs in shs, where the cells of each
--                   hom have already been replaced by symbolic sets
--                   (each SHom lists, for every dimension i, the
--                   images of ⟨Θ⟩^-_i and ⟨Θ⟩^+_i)
--
-- The meaning of a sequence is defined through its first-entry
-- decomposition: `nullS e` says whether the empty tuple is in it, and
-- `heads e` lists pairs (a , r): tuples a ∷ x with x in r. Everything
-- is decided by walking these decompositions, so the work is
-- proportional to the number of distinct residuals, not to the number
-- of tuples.
--
-- The cover check (∀ x ∈ E. ∃ y ∈ F. x ≤ y entrywise) propagates
-- pairs (residual of E, set of residuals of F) one entry at a time,
-- removing duplicate pairs: an on-the-fly subset construction. It is
-- exact for every input (`cover-correct`).
------------------------------------------------------------------------
module CaTTExp.Gray.Cover where

open import CaTTExp.Prelude

------------------------------------------------------------------------
-- Generic list facts.

infix 4 _≤_
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

≤-refl : ∀ n → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-step : ∀ {a b} → a ≤ b → a ≤ suc b
≤-step z≤n     = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

≤-+r : ∀ {a b} c → a ≤ b → a + c ≤ b + c
≤-+r c z≤n     = n≤m+n _ c
  where
  n≤m+n : ∀ m n → n ≤ m + n
  n≤m+n zero    n = ≤-refl n
  n≤m+n (suc m) n = ≤-step (n≤m+n m n)
≤-+r c (s≤s p) = s≤s (≤-+r c p)

m≤m+n : ∀ m n → m ≤ m + n
m≤m+n zero    n = z≤n
m≤m+n (suc m) n = s≤s (m≤m+n m n)

n≤m+n : ∀ m n → n ≤ m + n
n≤m+n zero    n = ≤-refl n
n≤m+n (suc m) n = ≤-step (n≤m+n m n)

max-l : ∀ m n → m ≤ max m n
max-l zero    n       = z≤n
max-l (suc m) zero    = ≤-refl (suc m)
max-l (suc m) (suc n) = s≤s (max-l m n)

max-r : ∀ m n → n ≤ max m n
max-r zero    n       = ≤-refl n
max-r (suc m) zero    = z≤n
max-r (suc m) (suc n) = s≤s (max-r m n)

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

+-zero : ∀ a → a + zero ≡ a
+-zero zero    = refl
+-zero (suc a) = cong suc (+-zero a)

++-assoc : ∀ {a} {A : Set a} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-[] : ∀ {a} {A : Set a} (xs : List A) → xs ++ [] ≡ xs
++-[] []       = refl
++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

length : ∀ {a} {A : Set a} → List A → Nat
length []       = 0
length (_ ∷ xs) = suc (length xs)

mapL : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
mapL f []       = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

concatMapL : ∀ {a b} {A : Set a} {B : Set b} → (A → List B) → List A → List B
concatMapL f []       = []
concatMapL f (x ∷ xs) = f x ++ concatMapL f xs

infixr 1 _⊎_
data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data Any {a p} {A : Set a} (P : A → Set p) : List A → Set (a ⊔ p) where
  here  : ∀ {x xs} → P x → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

module _ {a p} {A : Set a} {P : A → Set p} where
  any-++l : ∀ {xs ys} → Any P xs → Any P (xs ++ ys)
  any-++l (here q)  = here q
  any-++l (there q) = there (any-++l q)

  any-++r : ∀ xs {ys} → Any P ys → Any P (xs ++ ys)
  any-++r []       q = q
  any-++r (x ∷ xs) q = there (any-++r xs q)

  any-++⁻ : ∀ xs {ys} → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  any-++⁻ []       q         = inj₂ q
  any-++⁻ (x ∷ xs) (here q)  = inj₁ (here q)
  any-++⁻ (x ∷ xs) (there q) with any-++⁻ xs q
  ... | inj₁ r = inj₁ (there r)
  ... | inj₂ r = inj₂ r

  any-if : ∀ b {xs} → Any P (if b then xs else []) → T b × Any P xs
  any-if true  q = tt , q
  any-if false ()

  any-if⁺ : ∀ b {xs} → T b → Any P xs → Any P (if b then xs else [])
  any-if⁺ true _ q = q

  any-witness : ∀ {xs} → Any P xs → Σ A λ x → Any (x ≡_) xs × P x
  any-witness (here q)  = _ , here refl , q
  any-witness (there q) with any-witness q
  ... | x , m , r = x , there m , r

  any-at : ∀ {xs x} → Any (x ≡_) xs → P x → Any P xs
  any-at (here refl) q = here q
  any-at (there m)   q = there (any-at m q)

any-map⁺ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p} (f : A → B) {xs} →
           Any (λ x → P (f x)) xs → Any P (mapL f xs)
any-map⁺ f (here q)  = here q
any-map⁺ f (there q) = there (any-map⁺ f q)

any-map⁻ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p} (f : A → B) xs →
           Any P (mapL f xs) → Any (λ x → P (f x)) xs
any-map⁻ f (x ∷ xs) (here q)  = here q
any-map⁻ f (x ∷ xs) (there q) = there (any-map⁻ f xs q)

any-mono : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} →
           (∀ {x} → P x → Q x) → ∀ {xs} → Any P xs → Any Q xs
any-mono f (here r)  = here (f r)
any-mono f (there r) = there (any-mono f r)

any-cm⁺ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p} (f : A → List B) {xs} →
          Any (λ x → Any P (f x)) xs → Any P (concatMapL f xs)
any-cm⁺ f {x ∷ xs} (here q)  = any-++l q
any-cm⁺ f {x ∷ xs} (there q) = any-++r (f x) (any-cm⁺ f q)

any-cm⁻ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p} (f : A → List B) xs →
          Any P (concatMapL f xs) → Any (λ x → Any P (f x)) xs
any-cm⁻ f (x ∷ xs) q with any-++⁻ (f x) q
... | inj₁ r = here r
... | inj₂ r = there (any-cm⁻ f xs r)

All-T : ∀ {a} {A : Set a} (p : A → Bool) xs → T (all p xs) → ∀ {x} → Any (x ≡_) xs → T (p x)
All-T p (x ∷ xs) q (here refl) = ∧-fst {p x} q
All-T p (x ∷ xs) q (there m)   = All-T p xs (∧-snd {p x} q) m

T-All : ∀ {a} {A : Set a} (p : A → Bool) xs → (∀ {x} → Any (x ≡_) xs → T (p x)) → T (all p xs)
T-All p []       f = tt
T-All p (x ∷ xs) f = ∧-in (f (here refl)) (T-All p xs (λ m → f (there m)))
  where
  ∧-in : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-in {true} _ q = q

-- Duplicate removal by a sound equality test.
module Nub {a} {A : Set a} (eq : A → A → Bool) (eq-sound : ∀ x y → T (eq x y) → x ≡ y) where
  memB : A → List A → Bool
  memB x []       = false
  memB x (y ∷ ys) = eq x y ∨ memB x ys

  nub : List A → List A
  nub []       = []
  nub (x ∷ xs) = if memB x xs then nub xs else (x ∷ nub xs)

  private
    memB-sound : ∀ x ys → T (memB x ys) → Any (x ≡_) ys
    memB-sound x (y ∷ ys) q with eq x y in e
    ... | true  = here (eq-sound x y (subst T (sym e) tt))
    ... | false = there (memB-sound x ys q)

  nub⁺ : ∀ {p} {P : A → Set p} xs → Any P xs → Any P (nub xs)
  nub⁺ (x ∷ xs) q with memB x xs in e
  nub⁺ (x ∷ xs) (here q)  | true  =
    nub⁺ xs (any-at (memB-sound x xs (subst T (sym e) tt)) q)
  nub⁺ (x ∷ xs) (there q) | true  = nub⁺ xs q
  nub⁺ (x ∷ xs) (here q)  | false = here q
  nub⁺ (x ∷ xs) (there q) | false = there (nub⁺ xs q)

  nub⁻ : ∀ {p} {P : A → Set p} xs → Any P (nub xs) → Any P xs
  nub⁻ (x ∷ xs) q with memB x xs
  ... | true  = there (nub⁻ xs q)
  nub⁻ (x ∷ xs) (here q)  | false = here q
  nub⁻ (x ∷ xs) (there q) | false = there (nub⁻ xs q)

------------------------------------------------------------------------
-- Symbolic sets of tuples.

Tuple : Set
Tuple = List Nat

mutual
  data Item : Set where
    lit : List Nat → Item
    alt : List (List Item) → Item
    sch : List (List (Nat × List (List Item) × List (List Item))) → Bool → Nat → Item

Seq : Set
Seq = List Item

Exp : Set
Exp = List Seq

-- One substituted hom: for each dimension i, the images of ⟨Θ⟩^-_i
-- and ⟨Θ⟩^+_i.
Entry : Set
Entry = Nat × Exp × Exp

SHom : Set
SHom = List Entry

oddN : Nat → Bool
oddN zero    = false
oddN (suc n) = not (oddN n)

flipS : Bool → Nat → Bool
flipS sg i = if oddN i then not sg else sg

appR : List (Nat × Seq) → Seq → List (Nat × Seq)
appR xs c = mapL (λ p → fst p , (snd p ++ c)) xs

mutual
  nullS : Seq → Bool
  nullS []       = true
  nullS (i ∷ is) = nullI i ∧ nullS is

  nullI : Item → Bool
  nullI (lit _)        = false
  nullI (alt ss)       = nullE ss
  nullI (sch shs sg k) = nullCh shs sg k

  nullE : Exp → Bool
  nullE []       = false
  nullE (q ∷ qs) = nullS q ∨ nullE qs

  nullCh : List SHom → Bool → Nat → Bool
  nullCh []         sg k = k ==ℕ 0
  nullCh (sh ∷ shs) sg k = nullH sh shs sg k

  nullH : SHom → List SHom → Bool → Nat → Bool
  nullH []                  shs sg k = false
  nullH ((i , m , p) ∷ es) shs sg k =
    ((i <ℕ suc k) ∧ (if sg then nullE p else nullE m) ∧ nullCh shs (flipS sg i) (k ∸ i))
    ∨ nullH es shs sg k

mutual
  heads : Seq → List (Nat × Seq)
  heads []       = []
  heads (i ∷ is) = appR (headsI i) is ++ (if nullI i then heads is else [])

  headsI : Item → List (Nat × Seq)
  headsI (lit ls)       = mapL (λ a → a , []) ls
  headsI (alt ss)       = headsE ss
  headsI (sch shs sg k) = headsCh shs sg k

  headsE : Exp → List (Nat × Seq)
  headsE []       = []
  headsE (q ∷ qs) = heads q ++ headsE qs

  headsCh : List SHom → Bool → Nat → List (Nat × Seq)
  headsCh []         sg k = []
  headsCh (sh ∷ shs) sg k = headsH sh shs sg k

  headsH : SHom → List SHom → Bool → Nat → List (Nat × Seq)
  headsH []                  shs sg k = []
  headsH ((i , m , p) ∷ es) shs sg k =
    (if i <ℕ suc k
     then (if sg then headsQ p shs (flipS sg i) (k ∸ i) else headsQ m shs (flipS sg i) (k ∸ i))
     else [])
    ++ headsH es shs sg k

  -- Heads of q followed by the chain sch shs sg k, for q in a piece.
  headsQ : Exp → List SHom → Bool → Nat → List (Nat × Seq)
  headsQ []       shs sg k = []
  headsQ (q ∷ qs) shs sg k =
    appR (heads q) (sch shs sg k ∷ [])
    ++ (if nullS q then headsCh shs sg k else [])
    ++ headsQ qs shs sg k

-- Membership, by the first-entry decomposition.
infix 4 _∈S_ _∈E_
_∈S_ : Tuple → Seq → Set
[]      ∈S e = T (nullS e)
(a ∷ x) ∈S e = Any (λ p → (a ≡ fst p) × (x ∈S snd p)) (heads e)

_∈E_ : Tuple → Exp → Set
x ∈E es = Any (x ∈S_) es

------------------------------------------------------------------------
-- Boolean facts.

∧-in : ∀ {a b} → T a → T b → T (a ∧ b)
∧-in {true} _ q = q

∨-out : ∀ {a b} → T (a ∨ b) → T a ⊎ T b
∨-out {true}  _ = inj₁ tt
∨-out {false} q = inj₂ q

∨-inl : ∀ {a b} → T a → T (a ∨ b)
∨-inl {true} _ = tt

∨-inr : ∀ {a b} → T b → T (a ∨ b)
∨-inr {true}  _ = tt
∨-inr {false} q = q

∧-assoc : ∀ a b c → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
∧-assoc true  b c = refl
∧-assoc false b c = refl

------------------------------------------------------------------------
-- The meaning of the constructors.

pick : Bool → Entry → Exp
pick sg (i , m , p) = if sg then p else m

null-++ : ∀ e c → nullS (e ++ c) ≡ nullS e ∧ nullS c
null-++ []      c = refl
null-++ (i ∷ e) c rewrite null-++ e c = sym (∧-assoc (nullI i) (nullS e) (nullS c))

nullE-any : ∀ ss → T (nullE ss) → Any (λ q → T (nullS q)) ss
nullE-any (q ∷ qs) t with ∨-out {nullS q} t
... | inj₁ r = here r
... | inj₂ r = there (nullE-any qs r)

any-nullE : ∀ ss → Any (λ q → T (nullS q)) ss → T (nullE ss)
any-nullE (q ∷ qs) (here r)  = ∨-inl r
any-nullE (q ∷ qs) (there r) = ∨-inr {nullS q} (any-nullE qs r)

module _ {p} {P : Nat × Seq → Set p} where
  appR⁻ : ∀ xs c → Any P (appR xs c) → Any (λ q → P (fst q , (snd q ++ c))) xs
  appR⁻ xs c = any-map⁻ _ xs

  appR⁺ : ∀ xs c → Any (λ q → P (fst q , (snd q ++ c))) xs → Any P (appR xs c)
  appR⁺ xs c = any-map⁺ _

  headsE⁻ : ∀ ss → Any P (headsE ss) → Any (λ q → Any P (heads q)) ss
  headsE⁻ (q ∷ qs) r with any-++⁻ (heads q) r
  ... | inj₁ s = here s
  ... | inj₂ s = there (headsE⁻ qs s)

  headsE⁺ : ∀ ss → Any (λ q → Any P (heads q)) ss → Any P (headsE ss)
  headsE⁺ (q ∷ qs) (here s)  = any-++l s
  headsE⁺ (q ∷ qs) (there s) = any-++r (heads q) (headsE⁺ qs s)

  if-hq : ∀ sg ent shs i k →
          (if sg then headsQ (snd (snd ent)) shs (flipS sg i) k else headsQ (fst (snd ent)) shs (flipS sg i) k)
          ≡ headsQ (pick sg ent) shs (flipS sg i) k
  if-hq true  (_ , m , q) shs i k = refl
  if-hq false (_ , m , q) shs i k = refl

  headsH⁻ : ∀ sh shs sg k → Any P (headsH sh shs sg k) →
            Any (λ ent → T (fst ent <ℕ suc k) × Any P (headsQ (pick sg ent) shs (flipS sg (fst ent)) (k ∸ fst ent))) sh
  headsH⁻ ((i , m , q) ∷ es) shs sg k r
    with any-++⁻ (if i <ℕ suc k then (if sg then headsQ q shs (flipS sg i) (k ∸ i) else headsQ m shs (flipS sg i) (k ∸ i)) else []) r
  ... | inj₂ s = there (headsH⁻ es shs sg k s)
  ... | inj₁ s with any-if (i <ℕ suc k) s
  ...   | lt , s' = here (lt , subst (Any P) (if-hq sg (i , m , q) shs i (k ∸ i)) s')

  headsH⁺ : ∀ sh shs sg k →
            Any (λ ent → T (fst ent <ℕ suc k) × Any P (headsQ (pick sg ent) shs (flipS sg (fst ent)) (k ∸ fst ent))) sh →
            Any P (headsH sh shs sg k)
  headsH⁺ ((i , m , q) ∷ es) shs sg k (here (lt , s)) =
    any-++l (any-if⁺ (i <ℕ suc k) lt (subst (Any P) (sym (if-hq sg (i , m , q) shs i (k ∸ i))) s))
  headsH⁺ ((i , m , q) ∷ es) shs sg k (there s) =
    any-++r (if i <ℕ suc k then (if sg then headsQ q shs (flipS sg i) (k ∸ i) else headsQ m shs (flipS sg i) (k ∸ i)) else [])
            (headsH⁺ es shs sg k s)

  headsQ⁻ : ∀ e shs sg k → Any P (headsQ e shs sg k) →
            Any (λ q → Any P (appR (heads q) (sch shs sg k ∷ [])) ⊎ (T (nullS q) × Any P (headsCh shs sg k))) e
  headsQ⁻ (q ∷ qs) shs sg k r with any-++⁻ (appR (heads q) (sch shs sg k ∷ [])) r
  ... | inj₁ s = here (inj₁ s)
  ... | inj₂ s with any-++⁻ (if nullS q then headsCh shs sg k else []) s
  ...   | inj₂ s' = there (headsQ⁻ qs shs sg k s')
  ...   | inj₁ s' with any-if (nullS q) s'
  ...     | nq , s'' = here (inj₂ (nq , s''))

  headsQ⁺ : ∀ e shs sg k →
            Any (λ q → Any P (appR (heads q) (sch shs sg k ∷ [])) ⊎ (T (nullS q) × Any P (headsCh shs sg k))) e →
            Any P (headsQ e shs sg k)
  headsQ⁺ (q ∷ qs) shs sg k (here (inj₁ s)) = any-++l s
  headsQ⁺ (q ∷ qs) shs sg k (here (inj₂ (nq , s))) =
    any-++r (appR (heads q) (sch shs sg k ∷ [])) (any-++l (any-if⁺ (nullS q) nq s))
  headsQ⁺ (q ∷ qs) shs sg k (there s) =
    any-++r (appR (heads q) (sch shs sg k ∷ []))
      (any-++r (if nullS q then headsCh shs sg k else []) (headsQ⁺ qs shs sg k s))

nullH⁻ : ∀ sh shs sg k → T (nullH sh shs sg k) →
         Any (λ ent → T (fst ent <ℕ suc k) × T (nullE (pick sg ent)) × T (nullCh shs (flipS sg (fst ent)) (k ∸ fst ent))) sh
nullH⁻ ((i , m , q) ∷ es) shs sg k t with ∨-out {(i <ℕ suc k) ∧ (if sg then nullE q else nullE m) ∧ nullCh shs (flipS sg i) (k ∸ i)} t
... | inj₂ r = there (nullH⁻ es shs sg k r)
... | inj₁ r = here (∧-fst {i <ℕ suc k} r , pk sg (∧-fst (∧-snd {i <ℕ suc k} r)) , ∧-snd {if sg then nullE q else nullE m} (∧-snd {i <ℕ suc k} r))
  where
  pk : ∀ sg → T (if sg then nullE q else nullE m) → T (nullE (pick sg (i , m , q)))
  pk true  x = x
  pk false x = x

nullH⁺ : ∀ sh shs sg k →
         Any (λ ent → T (fst ent <ℕ suc k) × T (nullE (pick sg ent)) × T (nullCh shs (flipS sg (fst ent)) (k ∸ fst ent))) sh →
         T (nullH sh shs sg k)
nullH⁺ ((i , m , q) ∷ es) shs sg k (here (a , b , c)) = ∨-inl (∧-in a (∧-in (pk sg b) c))
  where
  pk : ∀ sg → T (nullE (pick sg (i , m , q))) → T (if sg then nullE q else nullE m)
  pk true  x = x
  pk false x = x
nullH⁺ ((i , m , q) ∷ es) shs sg k (there r) =
  ∨-inr {(i <ℕ suc k) ∧ (if sg then nullE q else nullE m) ∧ nullCh shs (flipS sg i) (k ∸ i)} (nullH⁺ es shs sg k r)

------------------------------------------------------------------------
-- Concatenation.

record Split (x : Tuple) (e c : Seq) : Set where
  constructor split
  field
    sy sz : Tuple
    s-eq  : x ≡ sy ++ sz
    s-y   : sy ∈S e
    s-z   : sz ∈S c
open Split

null-cons : ∀ i e y → T (nullI i) → y ∈S e → y ∈S (i ∷ e)
null-cons i e []      ni ye = ∧-in ni ye
null-cons i e (a ∷ y) ni ye = any-++r (appR (headsI i) e) (any-if⁺ (nullI i) ni ye)

mutual
  cl⇒ : ∀ x e c → x ∈S (e ++ c) → Split x e c
  cl⇒ x       []      c q = split [] x refl tt q
  cl⇒ []      (i ∷ e) c q
    rewrite null-++ e c
    = split [] [] refl (∧-in (∧-fst {nullI i} q) (∧-fst {nullS e} (∧-snd {nullI i} q)))
                       (∧-snd {nullS e} (∧-snd {nullI i} q))
  cl⇒ (a ∷ x) e c q = clL⇒ a x e c q

  -- recursion on e, with the tuple a ∷ x fixed
  clL⇒ : ∀ a x e c → (a ∷ x) ∈S (e ++ c) → Split (a ∷ x) e c
  clL⇒ a x []      c q = split [] (a ∷ x) refl tt q
  clL⇒ a x (i ∷ e) c q = go (any-++⁻ (appR (headsI i) (e ++ c)) q)
    where
    P : Nat × Seq → Set
    P p = (a ≡ fst p) × (x ∈S snd p)
    back : ∀ {r₀ b} → Any (λ p → (b , r₀) ≡ p) (headsI i) → a ≡ b → Split x (r₀ ++ e) c → Split (a ∷ x) (i ∷ e) c
    back {r₀} {b} m ab (split y z eq ye zc) =
      split (a ∷ y) z (cong (a ∷_) eq) (any-++l (appR⁺ (headsI i) e (any-at m (ab , ye)))) zc
    ext : T (nullI i) → Split (a ∷ x) e c → Split (a ∷ x) (i ∷ e) c
    ext ni (split y z eq ye zc) = split y z eq (null-cons i e y ni ye) zc
    go : Any P (appR (headsI i) (e ++ c)) ⊎ Any P (if nullI i then heads (e ++ c) else []) → Split (a ∷ x) (i ∷ e) c
    go (inj₂ r) with any-if (nullI i) r
    ... | ni , r' = ext ni (clL⇒ a x e c r')
    go (inj₁ r) with any-witness (appR⁻ (headsI i) (e ++ c) r)
    ... | (b , r₀) , m , (ab , xr) = back m ab (cl⇒ x (r₀ ++ e) c (subst (x ∈S_) (sym (++-assoc r₀ e c)) xr))

mutual
  cl⇐ : ∀ y z e c → y ∈S e → z ∈S c → (y ++ z) ∈S (e ++ c)
  cl⇐ []      z []      c ye zc = zc
  cl⇐ []      z (i ∷ e) c ye zc =
    null-cons i (e ++ c) z (∧-fst {nullI i} ye) (cl⇐ [] z e c (∧-snd {nullI i} ye) zc)
  cl⇐ (a ∷ y) z e c ye zc = clL⇐ a y z e c ye zc

  clL⇐ : ∀ a y z e c → (a ∷ y) ∈S e → z ∈S c → ((a ∷ y) ++ z) ∈S (e ++ c)
  clL⇐ a y z []      c () zc
  clL⇐ a y z (i ∷ e) c ye zc = go (any-++⁻ (appR (headsI i) e) ye)
    where
    P : Nat × Seq → Set
    P p = (a ≡ fst p) × (y ∈S snd p)
    go : Any P (appR (headsI i) e) ⊎ Any P (if nullI i then heads e else []) → ((a ∷ y) ++ z) ∈S (i ∷ (e ++ c))
    go (inj₂ r) with any-if (nullI i) r
    ... | ni , r' = null-cons i (e ++ c) ((a ∷ y) ++ z) ni (clL⇐ a y z e c r' zc)
    go (inj₁ r) with any-witness (appR⁻ (headsI i) e r)
    ... | (b , r₀) , m , (ab , yr) =
      any-++l (appR⁺ (headsI i) (e ++ c)
        (any-at m (ab , subst ((y ++ z) ∈S_) (++-assoc r₀ e c) (cl⇐ y z (r₀ ++ e) c yr zc))))

------------------------------------------------------------------------
-- Items.

lit⇒ : ∀ x ls c → x ∈S (lit ls ∷ c) → Σ Nat λ a → Σ Tuple λ x' → (x ≡ a ∷ x') × Any (a ≡_) ls × x' ∈S c
lit⇒ []      ls c ()
lit⇒ (a ∷ x) ls c q with any-++⁻ (appR (mapL (λ a → a , []) ls) c) q
... | inj₂ ()
... | inj₁ r with any-witness (any-map⁻ _ ls (appR⁻ (mapL (λ a → a , []) ls) c r))
...   | b , m , (ab , xc) = a , x , refl , subst (λ b' → Any (b' ≡_) ls) (sym ab) m , xc

lit⇐ : ∀ a x ls c → Any (a ≡_) ls → x ∈S c → (a ∷ x) ∈S (lit ls ∷ c)
lit⇐ a x ls c m xc =
  any-++l (appR⁺ (mapL (λ a → a , []) ls) c (any-map⁺ _ (any-mono (λ { refl → refl , xc }) m)))

alt⇒ : ∀ x ss → x ∈S (alt ss ∷ []) → x ∈E ss
alt⇒ []      ss q = nullE-any ss (∧-fst {nullE ss} q)
alt⇒ (a ∷ x) ss q with any-++⁻ (appR (headsE ss) []) q
... | inj₂ r with any-if (nullE ss) r
...   | _ , ()
alt⇒ (a ∷ x) ss q | inj₁ r =
  any-mono (λ s → s) (headsE⁻ ss (any-mono (λ { (ab , xr) → ab , subst (x ∈S_) (++-[] _) xr }) (appR⁻ (headsE ss) [] r)))

alt⇐ : ∀ x ss → x ∈E ss → x ∈S (alt ss ∷ [])
alt⇐ []      ss q = ∧-in (any-nullE ss q) tt
alt⇐ (a ∷ x) ss q =
  any-++l (appR⁺ (headsE ss) []
    (any-mono (λ { (ab , xr) → ab , subst (x ∈S_) (sym (++-[] _)) xr }) (headsE⁺ ss q)))

-- The chain of no homs: the empty tuple, in dimension 0.
schNil⇒ : ∀ x sg k → x ∈S (sch [] sg k ∷ []) → (x ≡ []) × T (k ==ℕ 0)
schNil⇒ []      sg k q = refl , ∧-fst {k ==ℕ 0} q
schNil⇒ (a ∷ x) sg k q with any-if (k ==ℕ 0) q
... | _ , ()

schNil⇐ : ∀ sg k → T (k ==ℕ 0) → [] ∈S (sch [] sg k ∷ [])
schNil⇐ sg k t = ∧-in t tt

-- One step of a chain: an entry of the first hom with i ≤ k, a
-- tuple from its piece, then the rest of the chain.
SchW : Tuple → SHom → List SHom → Bool → Nat → Set
SchW x sh shs sg k =
  Any (λ ent → T (fst ent <ℕ suc k) ×
               Any (λ q → Split x q (sch shs (flipS sg (fst ent)) (k ∸ fst ent) ∷ [])) (pick sg ent)) sh

schCons⇒ : ∀ x sh shs sg k → x ∈S (sch (sh ∷ shs) sg k ∷ []) → SchW x sh shs sg k
schCons⇒ [] sh shs sg k q =
  any-mono (λ { (lt , ne , nc) → lt , any-mono (λ nq → split [] [] refl nq (∧-in nc tt)) (nullE-any _ ne) })
    (nullH⁻ sh shs sg k (∧-fst {nullH sh shs sg k} q))
schCons⇒ (a ∷ x) sh shs sg k q with any-++⁻ (appR (headsH sh shs sg k) []) q
... | inj₂ r with any-if (nullH sh shs sg k) r
...   | _ , ()
schCons⇒ (a ∷ x) sh shs sg k q | inj₁ r =
  any-mono (λ { (lt , s) → lt , any-mono one (headsQ⁻ _ _ _ _ s) }) (headsH⁻ sh shs sg k (appR⁻ (headsH sh shs sg k) [] r))
  where
  one : ∀ {sg' k' q} →
        Any (λ p → (a ≡ fst p) × (x ∈S (snd p ++ []))) (appR (heads q) (sch shs sg' k' ∷ []))
        ⊎ (T (nullS q) × Any (λ p → (a ≡ fst p) × (x ∈S (snd p ++ []))) (headsCh shs sg' k')) →
        Split (a ∷ x) q (sch shs sg' k' ∷ [])
  one {sg'} {k'} {q} (inj₁ s) with any-witness (appR⁻ (heads q) (sch shs sg' k' ∷ []) s)
  ... | (b , r₀) , m , (ab , xr) with cl⇒ x r₀ (sch shs sg' k' ∷ []) (subst (x ∈S_) (++-[] _) xr)
  ...   | split y z eq ye zc = split (a ∷ y) z (cong (a ∷_) eq) (any-at m (ab , ye)) zc
  one {sg'} {k'} {q} (inj₂ (nq , s)) =
    split [] (a ∷ x) refl nq (any-++l (appR⁺ (headsCh shs sg' k') [] s))

schCons⇐ : ∀ x sh shs sg k → SchW x sh shs sg k → x ∈S (sch (sh ∷ shs) sg k ∷ [])
schCons⇐ x sh shs sg k w with x
... | [] = ∧-in (nullH⁺ sh shs sg k (nil w)) tt
  where
  nil : ∀ {sh} → SchW [] sh shs sg k →
        Any (λ ent → T (fst ent <ℕ suc k) × T (nullE (pick sg ent)) × T (nullCh shs (flipS sg (fst ent)) (k ∸ fst ent))) sh
  nil (here {x = i , m' , p'} (lt , s)) with any-witness s
  ... | q , m , split [] [] refl ye zc =
    here (lt , any-nullE _ (any-at m ye) , ∧-fst {nullCh shs (flipS sg i) (k ∸ i)} zc)
  nil (there w) = there (nil w)
... | a ∷ x' = any-++l (appR⁺ (headsH sh shs sg k) []
                 (headsH⁺ sh shs sg k (any-mono (λ { (lt , s) → lt , cons s }) w)))
  where
  cons : ∀ {qs sg' k'} → Any (λ q → Split (a ∷ x') q (sch shs sg' k' ∷ [])) qs →
         Any (λ p → (a ≡ fst p) × (x' ∈S (snd p ++ []))) (headsQ qs shs sg' k')
  cons {qs} {sg'} {k'} s = headsQ⁺ qs shs sg' k' (any-mono pt s)
    where
    pt : ∀ {q} → Split (a ∷ x') q (sch shs sg' k' ∷ []) →
         Any (λ p → (a ≡ fst p) × (x' ∈S (snd p ++ []))) (appR (heads q) (sch shs sg' k' ∷ []))
         ⊎ (T (nullS q) × Any (λ p → (a ≡ fst p) × (x' ∈S (snd p ++ []))) (headsCh shs sg' k'))
    pt {q} (split [] (.a ∷ .x') refl ye zc) with any-++⁻ (appR (headsCh shs sg' k') []) zc
    ... | inj₁ r = inj₂ (ye , appR⁻ (headsCh shs sg' k') [] r)
    ... | inj₂ r with any-if (nullCh shs sg' k') r
    ...   | _ , ()
    pt {q} (split (.a ∷ y) z refl ye zc) with any-witness ye
    ... | (b , r₀) , m , (ab , yr) =
      inj₁ (appR⁺ (heads q) (sch shs sg' k' ∷ [])
              (any-at m (ab , subst (λ s → (y ++ z) ∈S s) (sym (++-[] _)) (cl⇐ y z r₀ (sch shs sg' k' ∷ []) yr zc))))

------------------------------------------------------------------------
-- A size bound: every residual is smaller, so tuples in e have
-- length ≤ μS e. This bounds the number of rounds of the cover check.

mutual
  μS : Seq → Nat
  μS []       = 0
  μS (i ∷ is) = μI i + μS is

  μI : Item → Nat
  μI (lit _)       = 1
  μI (alt ss)      = μE ss
  μI (sch shs _ _) = μCh shs

  μE : Exp → Nat
  μE []       = 0
  μE (q ∷ qs) = max (μS q) (μE qs)

  μCh : List SHom → Nat
  μCh []         = 0
  μCh (sh ∷ shs) = μH sh + μCh shs

  μH : SHom → Nat
  μH []                 = 0
  μH ((_ , m , p) ∷ es) = max (max (μE m) (μE p)) (μH es)

μS-++ : ∀ a b → μS (a ++ b) ≡ μS a + μS b
μS-++ []      b = refl
μS-++ (i ∷ a) b rewrite μS-++ a b = sym (+-assoc (μI i) (μS a) (μS b))

private
  Mem : Nat × Seq → List (Nat × Seq) → Set
  Mem p xs = Any (p ≡_) xs

  appR-mem : ∀ {p} xs c → Mem p (appR xs c) →
             Σ (Nat × Seq) λ q → Mem q xs × (p ≡ (fst q , (snd q ++ c)))
  appR-mem xs c m with any-witness (appR⁻ {P = λ q → _ ≡ q} xs c m)
  ... | q , m' , e = q , m' , e

  -- suc a ≤ b  ⇒  suc (a + c) ≤ b + c
  bump : ∀ {a b} c → suc a ≤ b → suc (a + c) ≤ b + c
  bump c p = ≤-+r c p

mutual
  hb : ∀ e {p} → Mem p (heads e) → suc (μS (snd p)) ≤ μS e
  hb (i ∷ is) {p} m with any-++⁻ (appR (headsI i) is) m
  ... | inj₁ r with appR-mem (headsI i) is r
  ...   | q , m' , refl rewrite μS-++ (snd q) is = bump (μS is) (hbI i m')
  hb (i ∷ is) {p} m | inj₂ r with any-if (nullI i) r
  ...   | _ , r' = ≤-trans (hb is r') (n≤m+n (μI i) (μS is))

  hbI : ∀ i {p} → Mem p (headsI i) → suc (μS (snd p)) ≤ μI i
  hbI (lit ls)       m with any-witness (any-map⁻ (λ a → a , []) ls m)
  ... | _ , _ , refl = s≤s z≤n
  hbI (alt ss)       m = hbE ss m
  hbI (sch shs sg k) m = hbCh shs sg k m

  hbE : ∀ ss {p} → Mem p (headsE ss) → suc (μS (snd p)) ≤ μE ss
  hbE (q ∷ qs) m with any-++⁻ (heads q) m
  ... | inj₁ r = ≤-trans (hb q r) (max-l (μS q) (μE qs))
  ... | inj₂ r = ≤-trans (hbE qs r) (max-r (μS q) (μE qs))

  hbCh : ∀ shs sg k {p} → Mem p (headsCh shs sg k) → suc (μS (snd p)) ≤ μCh shs
  hbCh (sh ∷ shs) sg k m = hbH sh shs sg k m

  hbH : ∀ sh shs sg k {p} → Mem p (headsH sh shs sg k) → suc (μS (snd p)) ≤ μH sh + μCh shs
  hbH ((i , mm , pp) ∷ es) shs sg k m
    with any-++⁻ (if i <ℕ suc k then (if sg then headsQ pp shs (flipS sg i) (k ∸ i) else headsQ mm shs (flipS sg i) (k ∸ i)) else []) m
  ... | inj₂ r = ≤-trans (hbH es shs sg k r) (≤-+r (μCh shs) (max-r (max (μE mm) (μE pp)) (μH es)))
  ... | inj₁ r with any-if (i <ℕ suc k) r
  ...   | _ , r' = ≤-trans (pk sg r') (≤-+r (μCh shs) (≤-trans (top sg) (max-l (max (μE mm) (μE pp)) (μH es))))
    where
    top : ∀ sg → μE (if sg then pp else mm) ≤ max (μE mm) (μE pp)
    top true  = max-r (μE mm) (μE pp)
    top false = max-l (μE mm) (μE pp)
    pk : ∀ sg {p} → Mem p (if sg then headsQ pp shs (flipS sg i) (k ∸ i) else headsQ mm shs (flipS sg i) (k ∸ i)) →
         suc (μS (snd p)) ≤ μE (if sg then pp else mm) + μCh shs
    pk true  m' = hbQ pp shs (flipS true i) (k ∸ i) m'
    pk false m' = hbQ mm shs (flipS false i) (k ∸ i) m'

  hbQ : ∀ e shs sg k {p} → Mem p (headsQ e shs sg k) → suc (μS (snd p)) ≤ μE e + μCh shs
  hbQ (q ∷ qs) shs sg k m with any-++⁻ (appR (heads q) (sch shs sg k ∷ [])) m
  ... | inj₁ r with appR-mem (heads q) (sch shs sg k ∷ []) r
  ...   | w , m' , refl rewrite μS-++ (snd w) (sch shs sg k ∷ []) | +-zero (μCh shs) =
    bump (μCh shs) (≤-trans (hb q m') (max-l (μS q) (μE qs)))
  hbQ (q ∷ qs) shs sg k m | inj₂ r with any-++⁻ (if nullS q then headsCh shs sg k else []) r
  ...   | inj₂ r' = ≤-trans (hbQ qs shs sg k r') (≤-+r (μCh shs) (max-r (μS q) (μE qs)))
  ...   | inj₁ r' with any-if (nullS q) r'
  ...     | _ , r'' = ≤-trans (hbCh shs sg k r'') (n≤m+n (max (μS q) (μE qs)) (μCh shs))

len-bound : ∀ x e → x ∈S e → length x ≤ μS e
len-bound []      e q = z≤n
len-bound (a ∷ x) e q with any-witness q
... | p , m , (_ , xr) = ≤-trans (s≤s (len-bound x (snd p) xr)) (hb e m)

------------------------------------------------------------------------
-- Equality of symbolic sets (syntactic), for duplicate removal.

eqB : Bool → Bool → Bool
eqB true  true  = true
eqB false false = true
eqB _     _     = false

eqB-sound : ∀ a b → T (eqB a b) → a ≡ b
eqB-sound true  true  _ = refl
eqB-sound false false _ = refl

mutual
  eqNs : List Nat → List Nat → Bool
  eqNs []       []       = true
  eqNs (x ∷ xs) (y ∷ ys) = (x ==ℕ y) ∧ eqNs xs ys
  eqNs _        _        = false

  eqI : Item → Item → Bool
  eqI (lit a)      (lit b)        = eqNs a b
  eqI (alt a)      (alt b)        = eqExp a b
  eqI (sch a s k)  (sch b s' k')  = eqSHL a b ∧ eqB s s' ∧ (k ==ℕ k')
  eqI _            _              = false

  eqSeq : Seq → Seq → Bool
  eqSeq []       []       = true
  eqSeq (x ∷ xs) (y ∷ ys) = eqI x y ∧ eqSeq xs ys
  eqSeq _        _        = false

  eqExp : Exp → Exp → Bool
  eqExp []       []       = true
  eqExp (x ∷ xs) (y ∷ ys) = eqSeq x y ∧ eqExp xs ys
  eqExp _        _        = false

  eqSHL : List SHom → List SHom → Bool
  eqSHL []       []       = true
  eqSHL (x ∷ xs) (y ∷ ys) = eqSH x y ∧ eqSHL xs ys
  eqSHL _        _        = false

  eqSH : SHom → SHom → Bool
  eqSH []                 []                    = true
  eqSH ((i , m , p) ∷ xs) ((i' , m' , p') ∷ ys) =
    (i ==ℕ i') ∧ eqExp m m' ∧ eqExp p p' ∧ eqSH xs ys
  eqSH _                  _                     = false

private
  ∧₁ : ∀ {a b} → T (a ∧ b) → T a
  ∧₁ {a} = ∧-fst {a}
  ∧₂ : ∀ {a b} → T (a ∧ b) → T b
  ∧₂ {a} = ∧-snd {a}

mutual
  eqNs-sound : ∀ a b → T (eqNs a b) → a ≡ b
  eqNs-sound []       []       _ = refl
  eqNs-sound (x ∷ xs) (y ∷ ys) t =
    cong₂ _∷_ (==ℕ-sound x y (∧₁ {x ==ℕ y} t)) (eqNs-sound xs ys (∧₂ {x ==ℕ y} t))

  eqI-sound : ∀ a b → T (eqI a b) → a ≡ b
  eqI-sound (lit a)     (lit b)       t = cong lit (eqNs-sound a b t)
  eqI-sound (alt a)     (alt b)       t = cong alt (eqExp-sound a b t)
  eqI-sound (sch a s k) (sch b s' k') t
    rewrite eqSHL-sound a b (∧₁ {eqSHL a b} t)
          | eqB-sound s s' (∧₁ {eqB s s'} (∧₂ {eqSHL a b} t))
          | ==ℕ-sound k k' (∧₂ {eqB s s'} (∧₂ {eqSHL a b} t)) = refl

  eqSeq-sound : ∀ a b → T (eqSeq a b) → a ≡ b
  eqSeq-sound []       []       _ = refl
  eqSeq-sound (x ∷ xs) (y ∷ ys) t =
    cong₂ _∷_ (eqI-sound x y (∧₁ {eqI x y} t)) (eqSeq-sound xs ys (∧₂ {eqI x y} t))

  eqExp-sound : ∀ a b → T (eqExp a b) → a ≡ b
  eqExp-sound []       []       _ = refl
  eqExp-sound (x ∷ xs) (y ∷ ys) t =
    cong₂ _∷_ (eqSeq-sound x y (∧₁ {eqSeq x y} t)) (eqExp-sound xs ys (∧₂ {eqSeq x y} t))

  eqSHL-sound : ∀ a b → T (eqSHL a b) → a ≡ b
  eqSHL-sound []       []       _ = refl
  eqSHL-sound (x ∷ xs) (y ∷ ys) t =
    cong₂ _∷_ (eqSH-sound x y (∧₁ {eqSH x y} t)) (eqSHL-sound xs ys (∧₂ {eqSH x y} t))

  eqSH-sound : ∀ a b → T (eqSH a b) → a ≡ b
  eqSH-sound []                 []                    _ = refl
  eqSH-sound ((i , m , p) ∷ xs) ((i' , m' , p') ∷ ys) t
    rewrite ==ℕ-sound i i' (∧₁ {i ==ℕ i'} t)
          | eqExp-sound m m' (∧₁ {eqExp m m'} (∧₂ {i ==ℕ i'} t))
          | eqExp-sound p p' (∧₁ {eqExp p p'} (∧₂ {eqExp m m'} (∧₂ {i ==ℕ i'} t)))
          | eqSH-sound xs ys (∧₂ {eqExp p p'} (∧₂ {eqExp m m'} (∧₂ {i ==ℕ i'} t))) = refl

eqPair : Seq × Exp → Seq × Exp → Bool
eqPair (e , F) (e' , F') = eqSeq e e' ∧ eqExp F F'

eqPair-sound : ∀ a b → T (eqPair a b) → a ≡ b
eqPair-sound (e , F) (e' , F') t
  rewrite eqSeq-sound e e' (∧₁ {eqSeq e e'} t) | eqExp-sound F F' (∧₂ {eqSeq e e'} t) = refl

module NS = Nub eqSeq eqSeq-sound
module NP = Nub eqPair eqPair-sound

------------------------------------------------------------------------
-- The cover check, for any order `le` on entries.

module Algo (le : Nat → Nat → Bool) where

  leqTg : Tuple → Tuple → Bool
  leqTg []      []      = true
  leqTg (a ∷ x) (b ∷ y) = le a b ∧ leqTg x y
  leqTg _       _       = false

  -- every tuple of e is below a tuple of one of the Fs
  Cov : Seq × Exp → Set
  Cov (e , Fs) = ∀ x → x ∈S e → Σ Tuple λ y → T (leqTg x y) × y ∈E Fs

  -- residuals of the Fs after an entry above a
  D : Nat → Exp → Exp
  D a Fs = NS.nub (concatMapL (λ f → concatMapL (λ p → if le a (fst p) then snd p ∷ [] else []) (heads f)) Fs)

  local : Seq × Exp → Bool
  local (e , Fs) = not (nullS e) ∨ nullE Fs

  succs : Seq × Exp → List (Seq × Exp)
  succs (e , Fs) = mapL (λ p → snd p , D (fst p) Fs) (heads e)

  run : Nat → List (Seq × Exp) → Bool
  run zero    P = true
  run (suc n) P = all local P ∧ run n (NP.nub (concatMapL succs P))

  cover : Exp → Exp → Bool
  cover E F = run (suc (μE E)) (mapL (λ e → e , F) E)

  -- correctness ---------------------------------------------------------

  D⇐ : ∀ a b y Fs → T (le a b) → (b ∷ y) ∈E Fs → y ∈E D a Fs
  D⇐ a b y Fs lab q =
    NS.nub⁺ _ (any-cm⁺ _ (any-mono (λ {f} r → any-cm⁺ _ (any-mono (λ { {p} (refl , yr) → any-if⁺ (le a (fst p)) lab (here yr) }) r)) q))

  D⇒ : ∀ a y Fs → y ∈E D a Fs → Σ Nat λ b → T (le a b) × (b ∷ y) ∈E Fs
  D⇒ a y Fs q with any-witness (any-cm⁻ _ Fs (NS.nub⁻ _ q))
  ... | f , mf , r with any-witness (any-cm⁻ _ (heads f) r)
  ...   | p , mp , r' with any-if (le a (fst p)) r'
  ...     | lab , here yr = fst p , lab , any-at mf (any-at mp (refl , yr))

  private
    leq-nil : ∀ y → T (leqTg [] y) → y ≡ []
    leq-nil []      _ = refl

    leq-cons : ∀ a x y → T (leqTg (a ∷ x) y) → Σ Nat λ b → Σ Tuple λ y' → (y ≡ b ∷ y') × T (le a b) × T (leqTg x y')
    leq-cons a x (b ∷ y') t = b , y' , refl , ∧-fst {le a b} t , ∧-snd {le a b} t

  cov⇒local : ∀ p → Cov p → T (local p)
  cov⇒local (e , Fs) c with nullS e in ne
  ... | false = tt
  ... | true with c [] (subst T (sym ne) tt)
  ...   | y , l , yF rewrite leq-nil y l = any-nullE Fs yF

  cov⇒succ : ∀ p → Cov p → ∀ {p'} → Any (p' ≡_) (succs p) → Cov p'
  cov⇒succ (e , Fs) c m with any-witness (any-map⁻ _ (heads e) m)
  ... | q , mq , refl = λ x xr →
    let y , l , yF = c (fst q ∷ x) (any-at mq (refl , xr))
        b , y' , eq , lab , l' = leq-cons (fst q) x y l
    in y' , l' , D⇐ (fst q) b y' Fs lab (subst (_∈E Fs) eq yF)

  local+succ⇒cov : ∀ p → T (local p) → (∀ {p'} → Any (p' ≡_) (succs p) → Cov p') → Cov p
  local+succ⇒cov (e , Fs) lo sc [] xr with ∨-out {not (nullS e)} lo
  ... | inj₂ nF = [] , tt , nullE-any Fs nF
  ... | inj₁ nn = ⊥-elim (contra (nullS e) nn xr)
    where
    contra : ∀ b → T (not b) → T b → ⊥
    contra true  () _
    contra false _  ()
  local+succ⇒cov (e , Fs) lo sc (a ∷ x) xr with any-witness xr
  ... | q , mq , (refl , xq) =
    let y' , l' , yD = sc (any-map⁺ _ (any-mono (λ { refl → refl }) mq)) x xq
        b , lab , bF = D⇒ (fst q) y' Fs yD
    in b ∷ y' , ∧-in lab l' , bF

  Bnd : Nat → Seq → Set
  Bnd n e = ∀ x → x ∈S e → suc (length x) ≤ n

  run⇒ : ∀ n P → (∀ {p} → Any (p ≡_) P → Bnd n (fst p)) → T (run n P) → ∀ {p} → Any (p ≡_) P → Cov p
  run⇒ zero P bnd t {e , Fs} m x xr with bnd m x xr
  ... | ()
  run⇒ (suc n) P bnd t {p} m =
    local+succ⇒cov p (All-T local P (∧-fst {all local P} t) m)
      (λ m' → run⇒ n _ bnd' (∧-snd {all local P} t) (NP.nub⁺ _ (any-cm⁺ succs (any-at m m'))))
    where
    bnd' : ∀ {p'} → Any (p' ≡_) (NP.nub (concatMapL succs P)) → Bnd n (fst p')
    bnd' m₁ x xr with any-witness (any-cm⁻ succs P (NP.nub⁻ _ m₁))
    ... | (e , Fs) , mp , m₂ with any-witness (any-map⁻ _ (heads e) m₂)
    ...   | q , mq , refl with bnd mp (fst q ∷ x) (any-at mq (refl , xr))
    ...     | s≤s le' = le'

  run⇐ : ∀ n P → (∀ {p} → Any (p ≡_) P → Cov p) → T (run n P)
  run⇐ zero    P c = tt
  run⇐ (suc n) P c =
    ∧-in (T-All local P (λ {p} m → cov⇒local p (c m)))
         (run⇐ n _ (λ m₁ → sub m₁))
    where
    sub : ∀ {p'} → Any (p' ≡_) (NP.nub (concatMapL succs P)) → Cov p'
    sub m₁ with any-witness (any-cm⁻ succs P (NP.nub⁻ _ m₁))
    ... | p , mp , m₂ = cov⇒succ p (c mp) m₂

  private
    μ-mem : ∀ {e} E → Any (e ≡_) E → μS e ≤ μE E
    μ-mem (q ∷ qs) (here refl) = max-l (μS q) (μE qs)
    μ-mem (q ∷ qs) (there m)   = ≤-trans (μ-mem qs m) (max-r (μS q) (μE qs))

    pairs-mem : ∀ {p : Seq × Exp} (E F : Exp) → Any (p ≡_) (mapL (λ e → e , F) E) → Σ Seq λ e → Any (e ≡_) E × (p ≡ (e , F))
    pairs-mem E F m with any-witness (any-map⁻ (λ e → e , F) E m)
    ... | e , me , refl = e , me , refl

  -- The check is exact.
  cover-sound : ∀ E F → T (cover E F) → ∀ x → x ∈E E → Σ Tuple λ y → T (leqTg x y) × y ∈E F
  cover-sound E F t x xE with any-witness xE
  ... | e , me , xr =
    run⇒ (suc (μE E)) (mapL (λ e → e , F) E) bnd t (any-map⁺ _ (any-mono (λ { refl → refl }) me)) x xr
    where
    bnd : ∀ {p} → Any (p ≡_) (mapL (λ e → e , F) E) → Bnd (suc (μE E)) (fst p)
    bnd m x' xr' with pairs-mem E F m
    ... | e' , me' , refl = s≤s (≤-trans (len-bound x' e' xr') (μ-mem E me'))

  cover-complete : ∀ E F → (∀ x → x ∈E E → Σ Tuple λ y → T (leqTg x y) × y ∈E F) → T (cover E F)
  cover-complete E F c = run⇐ (suc (μE E)) (mapL (λ e → e , F) E) λ m → cv m
    where
    cv : ∀ {p} → Any (p ≡_) (mapL (λ e → e , F) E) → Cov p
    cv m x xr with pairs-mem E F m
    ... | e , me , refl = c x (any-at me xr)
