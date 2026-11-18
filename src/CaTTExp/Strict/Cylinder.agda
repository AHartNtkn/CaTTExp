------------------------------------------------------------------------
-- The Gray cylinder K ⊗ λD¹ of a finite ordered basis (ledger A5, (N3)).
--
-- λD¹ has basis 0, 1 (degree 0) and i (degree 1) with ∂⁻i = 0,
-- ∂⁺i = 1. The basis of K ⊗ λD¹ is k⊗0, k⊗i, k⊗1 for k in K, with
--     ∂^α(k⊗e) = ∂^α k ⊗ e,
--     ∂^α(k⊗i) = ∂^α k ⊗ i + k ⊗ ∂^{(−1)^{deg k} α} i
-- (Steiner 2004 §7, the Leibniz rule of conventions.md §2).
--
-- Layout. A chain of K ⊗ λD¹ is a triple (u₀, uᵢ, u₁) of chains of K
-- (the parts at the 0-end, in the middle and at the 1-end), stored
-- block by block: block k lists k⊗0, k⊗i, k⊗1 when deg k is even and
-- k⊗1, k⊗i, k⊗0 when deg k is odd (`cyl`). With this order every
-- negative face of an element comes before it and every positive face
-- after it, so the cylinder of an ordered basis is ordered.
--
-- `dP-cyl`, `dM-cyl`: the boundary of a chain in this layout,
--     ∂⁺(u₀, uᵢ, u₁) = (∂⁺u₀ + Od uᵢ, ∂⁺uᵢ, Ev uᵢ + ∂⁺u₁),
--     ∂⁻(u₀, uᵢ, u₁) = (∂⁻u₀ + Ev uᵢ, ∂⁻uᵢ, Od uᵢ + ∂⁻u₁),
-- where Ev and Od keep the even- and the odd-degree part.
--
-- `CylDD.Hyp′`: for a finite basis satisfying `Hyp` (ordered, unital)
-- whose boundaries have the right degrees (`DegP`, `DegM`), the
-- cylinder satisfies `Hyp` too: ∂∂ = 0 (`dd′`, from the parity shifts
-- Od ∂ = ∂ Ev, Ev ∂ = ∂ Od), degrees (`deg-dp′`, `deg-dm′`),
-- augmentation (`aug1′`), the order (`ordm′`, `ordp′`) and unitality
-- (`unital′`). So atom generation (N1) and freeness (N2, `Strict.Lift`)
-- apply to ν(K ⊗ λD¹).
--
-- The atoms (Steiner 2004, ⟨k⊗e⟩ = ⟨k⟩⊗e and ⟨k⊗i⟩ = ⟨k⟩⊗⟨i⟩):
--   `entK-end`  the atom of an end element is the copy of ⟨k⟩ at that end;
--   `Mid.claim` the atom of k⊗i has, j steps below its top, the row
--               ⟨k⟩_{j}⊗i in the middle and ⟨k⟩_{j−1} at the end picked
--               by the parity of its degree (`F`, `G`).
-- Instances: the square λD¹ ⊗ λD¹ and λD² ⊗ λD¹, cross-checked by the
-- decision procedures of `BasisCheck`.
------------------------------------------------------------------------
module CaTTExp.Strict.Cylinder where

open import CaTTExp.Prelude
open import Agda.Builtin.Nat using (_*_)
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; ≤-refl; ≤-suc; ≤-trans; ≤-<-⊥)
open import CaTTExp.Strict.Tables using (CMon; Vec; []; _∷_)
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms
open import CaTTExp.Strict.Generation
open import CaTTExp.Strict.BasisCheck
open import CaTTExp.Strict.Nu using (IsCell)
open import CaTTExp.Strict.CMonSolver
open import CaTTExp.Strict.Bag using (+-comm; +-assoc; +-zero; +-suc)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Parity.

even : Nat → Bool
even zero          = true
even (suc zero)    = false
even (suc (suc n)) = even n

odd : Nat → Bool
odd n = not (even n)

------------------------------------------------------------------------
-- The layout.

blk : ∀ {A : Set} {n} → Bool → A → A → A → Vec A n → Vec A (suc (suc (suc n)))
blk true  a b c r = a ∷ b ∷ c ∷ r
blk false a b c r = c ∷ b ∷ a ∷ r

cylA : ∀ {A : Set} {m} → Vec Nat m → Vec A m → Vec A m → Vec A m → Vec A (m * 3)
cylA []       []      []      []      = []
cylA (g ∷ gs) (a ∷ u) (b ∷ v) (c ∷ w) = blk (even g) a b c (cylA gs u v w)

cyl : ∀ {m} → Vec Nat m → Vec Nat m → Vec Nat m → Vec Nat m → Vec Nat (m * 3)
cyl = cylA

-- The three parts of a chain.
ub : ∀ {m} → Bool → Nat → Nat → Nat → Vec Nat m × (Vec Nat m × Vec Nat m) →
     Vec Nat (suc m) × (Vec Nat (suc m) × Vec Nat (suc m))
ub true  x y z (u , v , w) = (x ∷ u) , (y ∷ v) , (z ∷ w)
ub false x y z (u , v , w) = (z ∷ u) , (y ∷ v) , (x ∷ w)

uncyl : ∀ {m} → Vec Nat m → Vec Nat (m * 3) → Vec Nat m × (Vec Nat m × Vec Nat m)
uncyl []       []              = [] , ([] , [])
uncyl (g ∷ gs) (x ∷ y ∷ z ∷ r) = ub (even g) x y z (uncyl gs r)

cyl-uncyl : ∀ {m} (gs : Vec Nat m) (c : Vec Nat (m * 3)) →
            cyl gs (fst (uncyl gs c)) (fst (snd (uncyl gs c))) (snd (snd (uncyl gs c))) ≡ c
cyl-uncyl []       []              = refl
cyl-uncyl {suc m} (g ∷ gs) (x ∷ y ∷ z ∷ r) = go (even g) refl
  where
  T3 = uncyl gs r
  go : ∀ b → even g ≡ b →
       cyl (g ∷ gs) (fst (ub b x y z T3)) (fst (snd (ub b x y z T3))) (snd (snd (ub b x y z T3))) ≡ x ∷ y ∷ z ∷ r
  go true  e rewrite e = cong (λ q → x ∷ y ∷ z ∷ q) (cyl-uncyl gs r)
  go false e rewrite e = cong (λ q → x ∷ y ∷ z ∷ q) (cyl-uncyl gs r)

------------------------------------------------------------------------
-- The layout is linear.

private
  4mid : ∀ {M} (a b c d : Vec Nat M) → (a +c b) +c (c +c d) ≡ (a +c c) +c (b +c d)
  4mid {M} a b c d = solve ((` 0 ⊞ ` 1) ⊞ (` 2 ⊞ ` 3)) ((` 0 ⊞ ` 2) ⊞ (` 1 ⊞ ` 3)) (lk (a ∷ b ∷ c ∷ d ∷ [])) tt
    where open Solver (chainMon M)

cyl-+ : ∀ {m} (gs : Vec Nat m) a b c a′ b′ c′ →
        cyl gs (a +c a′) (b +c b′) (c +c c′) ≡ cyl gs a b c +c cyl gs a′ b′ c′
cyl-+ []       []      []      []      []        []        []        = refl
cyl-+ (g ∷ gs) (a ∷ u) (b ∷ v) (c ∷ w) (a′ ∷ u′) (b′ ∷ v′) (c′ ∷ w′) with even g
... | true  = cong (λ q → (a + a′) ∷ (b + b′) ∷ (c + c′) ∷ q) (cyl-+ gs u v w u′ v′ w′)
... | false = cong (λ q → (c + c′) ∷ (b + b′) ∷ (a + a′) ∷ q) (cyl-+ gs u v w u′ v′ w′)

cyl-0 : ∀ {m} (gs : Vec Nat m) → cyl gs 0c 0c 0c ≡ 0c
cyl-0 []       = refl
cyl-0 (g ∷ gs) with even g
... | true  = cong (λ q → 0 ∷ 0 ∷ 0 ∷ q) (cyl-0 gs)
... | false = cong (λ q → 0 ∷ 0 ∷ 0 ∷ q) (cyl-0 gs)

cyl-⊙ : ∀ {m} (gs : Vec Nat m) k a b c → k ⊙ cyl gs a b c ≡ cyl gs (k ⊙ a) (k ⊙ b) (k ⊙ c)
cyl-⊙ gs zero    a b c = sym (cyl-0 gs)
cyl-⊙ gs (suc k) a b c = trans (cong (cyl gs a b c +c_) (cyl-⊙ gs k a b c)) (sym (cyl-+ gs a b c _ _ _))

cyl-∸ : ∀ {m} (gs : Vec Nat m) a b c a′ b′ c′ →
        cyl gs a b c ∸c cyl gs a′ b′ c′ ≡ cyl gs (a ∸c a′) (b ∸c b′) (c ∸c c′)
cyl-∸ []       []      []      []      []        []        []        = refl
cyl-∸ (g ∷ gs) (a ∷ u) (b ∷ v) (c ∷ w) (a′ ∷ u′) (b′ ∷ v′) (c′ ∷ w′) with even g
... | true  = cong (λ q → (a ∸ a′) ∷ (b ∸ b′) ∷ (c ∸ c′) ∷ q) (cyl-∸ gs u v w u′ v′ w′)
... | false = cong (λ q → (c ∸ c′) ∷ (b ∸ b′) ∷ (a ∸ a′) ∷ q) (cyl-∸ gs u v w u′ v′ w′)

-- lin over a vector laid out like a chain.
lin-cyl : ∀ {M m} (gs : Vec Nat m) (a b c : Vec Nat m) (X Y Z : Vec (Vec Nat M) m) →
          lin (cyl gs a b c) (cylA gs X Y Z) ≡ (lin a X +c lin b Y) +c lin c Z
lin-cyl {M} []       []      []      []      []      []      []      = sym (trans (cong (_+c 0c) (+c-id 0c)) (+c-id 0c))
lin-cyl {M} (g ∷ gs) (a ∷ u) (b ∷ v) (c ∷ w) (x ∷ X) (y ∷ Y) (z ∷ Z) with even g
... | true  = trans (cong (λ q → (a ⊙ x) +c ((b ⊙ y) +c ((c ⊙ z) +c q))) (lin-cyl gs u v w X Y Z))
                (solve (` 0 ⊞ (` 1 ⊞ (` 2 ⊞ ((` 3 ⊞ ` 4) ⊞ ` 5))))
                       (((` 0 ⊞ ` 3) ⊞ (` 1 ⊞ ` 4)) ⊞ (` 2 ⊞ ` 5))
                       (lk (a ⊙ x ∷ b ⊙ y ∷ c ⊙ z ∷ lin u X ∷ lin v Y ∷ lin w Z ∷ [])) tt)
  where open Solver (chainMon M)
... | false = trans (cong (λ q → (c ⊙ z) +c ((b ⊙ y) +c ((a ⊙ x) +c q))) (lin-cyl gs u v w X Y Z))
                (solve (` 2 ⊞ (` 1 ⊞ (` 0 ⊞ ((` 3 ⊞ ` 4) ⊞ ` 5))))
                       (((` 0 ⊞ ` 3) ⊞ (` 1 ⊞ ` 4)) ⊞ (` 2 ⊞ ` 5))
                       (lk (a ⊙ x ∷ b ⊙ y ∷ c ⊙ z ∷ lin u X ∷ lin v Y ∷ lin w Z ∷ [])) tt)
  where open Solver (chainMon M)

-- lin through an additive map.
lin-hom : ∀ {M M′ m} (f : Vec Nat M → Vec Nat M′) →
          (∀ u v → f (u +c v) ≡ f u +c f v) → f 0c ≡ 0c →
          (c : Vec Nat m) (vs : Vec (Vec Nat M) m) → lin c (mapV f vs) ≡ f (lin c vs)
lin-hom f h z []      []       = sym z
lin-hom f h z (k ∷ c) (v ∷ vs) = trans (cong₂ _+c_ (sc k v) (lin-hom f h z c vs)) (sym (h (k ⊙ v) (lin c vs)))
  where
  sc : ∀ k v → k ⊙ f v ≡ f (k ⊙ v)
  sc zero    v = sym z
  sc (suc k) v = trans (cong (f v +c_) (sc k v)) (sym (h v (k ⊙ v)))

zip3 : ∀ {A B C D : Set} {m} → (A → B → C → D) → Vec A m → Vec B m → Vec C m → Vec D m
zip3 f []       []       []       = []
zip3 f (x ∷ xs) (y ∷ ys) (z ∷ zs) = f x y z ∷ zip3 f xs ys zs

-- lin over a vector of cylinder chains.
lin-zip3 : ∀ {m n} (gs : Vec Nat n) (c : Vec Nat m) (Os Bs Es : Vec (Vec Nat n) m) →
           lin c (zip3 (cyl gs) Os Bs Es) ≡ cyl gs (lin c Os) (lin c Bs) (lin c Es)
lin-zip3 gs []      []       []       []       = sym (cyl-0 gs)
lin-zip3 gs (k ∷ c) (o ∷ Os) (b ∷ Bs) (e ∷ Es) =
  trans (cong₂ _+c_ (cyl-⊙ gs k o b e) (lin-zip3 gs c Os Bs Es)) (sym (cyl-+ gs _ _ _ _ _ _))

------------------------------------------------------------------------
-- Selection by degree, and unit vectors.

sel : ∀ {m} → (Nat → Bool) → Vec Nat m → Vec Nat m → Vec Nat m
sel p gs u = zipV (λ g a → if p g then a else 0) gs u

selV : ∀ {M m} → (Nat → Bool) → Vec Nat m → Vec (Vec Nat M) m → Vec (Vec Nat M) m
selV p gs vs = zipV (λ g v → if p g then v else 0c) gs vs

lin-sel : ∀ {M m} (p : Nat → Bool) (gs : Vec Nat m) (u : Vec Nat m) (vs : Vec (Vec Nat M) m) →
          lin u (selV p gs vs) ≡ lin (sel p gs u) vs
lin-sel p []       []      []       = refl
lin-sel p (g ∷ gs) (a ∷ u) (v ∷ vs) with p g
... | true  = cong ((a ⊙ v) +c_) (lin-sel p gs u vs)
... | false = cong₂ _+c_ (⊙-0c a) (lin-sel p gs u vs)

sel-+ : ∀ {m} p (gs : Vec Nat m) u v → sel p gs (u +c v) ≡ sel p gs u +c sel p gs v
sel-+ p []       []      []      = refl
sel-+ p (g ∷ gs) (a ∷ u) (b ∷ v) with p g
... | true  = cong ((a + b) ∷_) (sel-+ p gs u v)
... | false = cong (0 ∷_) (sel-+ p gs u v)

sel-0 : ∀ {m} p (gs : Vec Nat m) → sel p gs 0c ≡ 0c
sel-0 p []       = refl
sel-0 p (g ∷ gs) with p g
... | true  = cong (0 ∷_) (sel-0 p gs)
... | false = cong (0 ∷_) (sel-0 p gs)

units : ∀ m → Vec (Vec Nat m) m
units zero    = []
units (suc m) = (1 ∷ 0c) ∷ mapV (0 ∷_) (units m)

private
  ⊙-head : ∀ {m} a → a ⊙ (1 ∷ 0c {m}) ≡ a ∷ 0c
  ⊙-head zero    = refl
  ⊙-head {m} (suc a) = trans (cong ((1 ∷ 0c) +c_) (⊙-head a)) (cong (suc a ∷_) (+c-id 0c))

  ⊙-cons0 : ∀ {m} k (v : Vec Nat m) → k ⊙ (0 ∷ v) ≡ 0 ∷ (k ⊙ v)
  ⊙-cons0 zero    v = refl
  ⊙-cons0 (suc k) v = cong ((0 ∷ v) +c_) (⊙-cons0 k v)

  lin-cons0 : ∀ {M m} (u : Vec Nat m) (vs : Vec (Vec Nat M) m) → lin u (mapV (0 ∷_) vs) ≡ 0 ∷ lin u vs
  lin-cons0 []      []       = refl
  lin-cons0 (k ∷ u) (v ∷ vs) = cong₂ _+c_ (⊙-cons0 k v) (lin-cons0 u vs)

lin-units : ∀ {m} (u : Vec Nat m) → lin u (units m) ≡ u
lin-units []      = refl
lin-units {suc m} (a ∷ u) =
  trans (cong₂ _+c_ (⊙-head a) (trans (lin-cons0 u (units m)) (cong (0 ∷_) (lin-units u))))
        (cong₂ _∷_ (+-zero a) (+c-id u))

at-units : ∀ m k → k < m → at 0c (units m) k ≡ unit k
at-units (suc m) zero    _       = refl
at-units (suc m) (suc k) (s≤s l) =
  trans (at-map (0 ∷_) 0c 0c refl (units m) k) (cong (0 ∷_) (at-units m k l))

even-suc : ∀ j → even (suc j) ≡ not (even j)
even-suc zero          = refl
even-suc (suc zero)    = refl
even-suc (suc (suc j)) = even-suc j

private
  if-0 : ∀ b → (if b then 0 else 0) ≡ 0
  if-0 true  = refl
  if-0 false = refl

  T-of : ∀ {b} → b ≡ true → T b
  T-of refl = tt

sel-prj-in : ∀ {m} p j (gs : Vec Nat m) v → p j ≡ true → sel p gs (prj j gs v) ≡ prj j gs v
sel-prj-in p j []       []      e = refl
sel-prj-in p j (g ∷ gs) (a ∷ v) e with g ==ℕ j in q
... | true  rewrite ==ℕ-sound g j (T-of q) | e = cong (a ∷_) (sel-prj-in p j gs v e)
... | false = cong₂ _∷_ (if-0 (p g)) (sel-prj-in p j gs v e)

sel-prj-out : ∀ {m} p j (gs : Vec Nat m) v → p j ≡ false → sel p gs (prj j gs v) ≡ 0c
sel-prj-out p j []       []      e = refl
sel-prj-out p j (g ∷ gs) (a ∷ v) e with g ==ℕ j in q
... | true  rewrite ==ℕ-sound g j (T-of q) | e = cong (0 ∷_) (sel-prj-out p j gs v e)
... | false = cong₂ _∷_ (if-0 (p g)) (sel-prj-out p j gs v e)

private
  vcons-inj : ∀ {A : Set} {m} {a b : A} {u v : Vec A m} → _≡_ {A = Vec A (suc m)} (a ∷ u) (b ∷ v) → (a ≡ b) × (u ≡ v)
  vcons-inj refl = refl , refl

prj-cyl : ∀ {m} j (gs hs ks ls a b c : Vec Nat m) →
          prj j (cyl gs hs ks ls) (cyl gs a b c) ≡ cyl gs (prj j hs a) (prj j ks b) (prj j ls c)
prj-cyl j []       []       []       []       []      []      []      = refl
prj-cyl j (g ∷ gs) (h ∷ hs) (k ∷ ks) (l ∷ ls) (a ∷ u) (b ∷ v) (c ∷ w) with even g
... | true  = cong (λ q → _ ∷ _ ∷ _ ∷ q) (prj-cyl j gs hs ks ls u v w)
... | false = cong (λ q → _ ∷ _ ∷ _ ∷ q) (prj-cyl j gs hs ks ls u v w)

augm-cyl : ∀ {m} (gs hs ks ls a b c : Vec Nat m) →
           augm (cyl gs hs ks ls) (cyl gs a b c) ≡ (augm hs a + augm ks b) + augm ls c
augm-cyl []       []       []       []       []      []      []      = refl
augm-cyl (g ∷ gs) (h ∷ hs) (k ∷ ks) (l ∷ ls) (a ∷ u) (b ∷ v) (c ∷ w) with even g
... | true  = trans (cong (λ q → x + (y + (z + q))) (augm-cyl gs hs ks ls u v w))
                    (solve (` 0 ⊞ (` 1 ⊞ (` 2 ⊞ ((` 3 ⊞ ` 4) ⊞ ` 5)))) (((` 0 ⊞ ` 3) ⊞ (` 1 ⊞ ` 4)) ⊞ (` 2 ⊞ ` 5))
                           (lk (x ∷ y ∷ z ∷ augm hs u ∷ augm ks v ∷ augm ls w ∷ [])) tt)
  where
  open Solver (record { M = Nat ; ε = 0 ; _⊕_ = _+_ ; ⊕-id = λ _ → refl ; ⊕-comm = +-comm ; ⊕-assoc = +-assoc })
  x = if h ==ℕ 0 then a else 0
  y = if k ==ℕ 0 then b else 0
  z = if l ==ℕ 0 then c else 0
... | false = trans (cong (λ q → z + (y + (x + q))) (augm-cyl gs hs ks ls u v w))
                    (solve (` 2 ⊞ (` 1 ⊞ (` 0 ⊞ ((` 3 ⊞ ` 4) ⊞ ` 5)))) (((` 0 ⊞ ` 3) ⊞ (` 1 ⊞ ` 4)) ⊞ (` 2 ⊞ ` 5))
                           (lk (x ∷ y ∷ z ∷ augm hs u ∷ augm ks v ∷ augm ls w ∷ [])) tt)
  where
  open Solver (record { M = Nat ; ε = 0 ; _⊕_ = _+_ ; ⊕-id = λ _ → refl ; ⊕-comm = +-comm ; ⊕-assoc = +-assoc })
  x = if h ==ℕ 0 then a else 0
  y = if k ==ℕ 0 then b else 0
  z = if l ==ℕ 0 then c else 0

augm-suc : ∀ {m} (gs b : Vec Nat m) → augm (mapV suc gs) b ≡ 0
augm-suc []       []      = refl
augm-suc (g ∷ gs) (a ∷ b) = augm-suc gs b

prj-suc0 : ∀ {m} (gs b : Vec Nat m) → prj 0 (mapV suc gs) b ≡ 0c
prj-suc0 []       []      = refl
prj-suc0 (g ∷ gs) (a ∷ b) = cong (0 ∷_) (prj-suc0 gs b)

prj-sucS : ∀ {m} j (gs b : Vec Nat m) → prj (suc j) (mapV suc gs) b ≡ prj j gs b
prj-sucS j []       []      = refl
prj-sucS j (g ∷ gs) (a ∷ b) = cong (_ ∷_) (prj-sucS j gs b)

prj-sel : ∀ {m} j p (gs b : Vec Nat m) → prj j gs (sel p gs b) ≡ sel p gs (prj j gs b)
prj-sel j p []       []      = refl
prj-sel j p (g ∷ gs) (a ∷ b) with g ==ℕ j | p g
... | true  | true  = cong (a ∷_) (prj-sel j p gs b)
... | true  | false = cong (0 ∷_) (prj-sel j p gs b)
... | false | true  = cong (0 ∷_) (prj-sel j p gs b)
... | false | false = cong (0 ∷_) (prj-sel j p gs b)

uncyl-cyl : ∀ {m} (gs a b c : Vec Nat m) → uncyl gs (cyl gs a b c) ≡ (a , b , c)
uncyl-cyl []       []      []      []      = refl
uncyl-cyl (g ∷ gs) (x ∷ u) (y ∷ v) (z ∷ w) = go (even g) refl
  where
  go : ∀ b → even g ≡ b → uncyl (g ∷ gs) (blk b x y z (cyl gs u v w)) ≡ ((x ∷ u) , (y ∷ v) , (z ∷ w))
  go true  e rewrite e | uncyl-cyl gs u v w = refl
  go false e rewrite e | uncyl-cyl gs u v w = refl

cyl-inj : ∀ {m} (gs : Vec Nat m) {a b c a′ b′ c′} → cyl gs a b c ≡ cyl gs a′ b′ c′ → (a ≡ a′) × ((b ≡ b′) × (c ≡ c′))
cyl-inj gs {a} {b} {c} {a′} {b′} {c′} e =
  let E = trans (sym (uncyl-cyl gs a b c)) (trans (cong (uncyl gs) e) (uncyl-cyl gs a′ b′ c′)) in
  cong fst E , cong (λ t → fst (snd t)) E , cong (λ t → snd (snd t)) E

------------------------------------------------------------------------
-- Positions in the layout.

slot : ∀ {A : Set} → Bool → Nat → A → A → A → A
slot true  zero          x y z = x
slot true  (suc zero)    x y z = y
slot true  (suc (suc _)) x y z = z
slot false zero          x y z = z
slot false (suc zero)    x y z = y
slot false (suc (suc _)) x y z = x

at-cylA : ∀ {A : Set} {m} (d : A) (gs : Vec Nat m) X Y Z k r → k < m → r < 3 →
          at d (cylA gs X Y Z) (k * 3 + r) ≡ slot (even (at 0 gs k)) r (at d X k) (at d Y k) (at d Z k)
at-cylA d (g ∷ gs) (x ∷ X) (y ∷ Y) (z ∷ Z) zero    zero                _ _ with even g
... | true  = refl
... | false = refl
at-cylA d (g ∷ gs) (x ∷ X) (y ∷ Y) (z ∷ Z) zero    (suc zero)          _ _ with even g
... | true  = refl
... | false = refl
at-cylA d (g ∷ gs) (x ∷ X) (y ∷ Y) (z ∷ Z) zero    (suc (suc zero))    _ _ with even g
... | true  = refl
... | false = refl
at-cylA d (g ∷ gs) (x ∷ X) (y ∷ Y) (z ∷ Z) zero    (suc (suc (suc r))) _ (s≤s (s≤s (s≤s ())))
at-cylA d (g ∷ gs) (x ∷ X) (y ∷ Y) (z ∷ Z) (suc k) r (s≤s l) q with even g
... | true  = at-cylA d gs X Y Z k r l q
... | false = at-cylA d gs X Y Z k r l q

divmod : ∀ n → Σ Nat (λ k → Σ Nat (λ r → (r < 3) × (n ≡ k * 3 + r)))
divmod zero                = 0 , 0 , s≤s z≤n , refl
divmod (suc zero)          = 0 , 1 , s≤s (s≤s z≤n) , refl
divmod (suc (suc zero))    = 0 , 2 , s≤s (s≤s (s≤s z≤n)) , refl
divmod (suc (suc (suc n))) = let (k , r , l , e) = divmod n in suc k , r , l , cong (λ q → suc (suc (suc q))) e

private
  ≤r : ∀ a r → a ≤ a + r
  ≤r zero    r = z≤n
  ≤r (suc a) r = s≤s (≤r a r)

  *3-mono : ∀ {a b} → a ≤ b → a * 3 ≤ b * 3
  *3-mono z≤n     = z≤n
  *3-mono (s≤s p) = s≤s (s≤s (s≤s (*3-mono p)))

  at-out : ∀ {A : Set} {m} (d : A) (vs : Vec A m) i → m ≤ i → at d vs i ≡ d
  at-out d []       i       _       = refl
  at-out d (v ∷ vs) (suc i) (s≤s q) = at-out d vs i q

-- Supports of laid-out chains.
cyl-Lo : ∀ {m} (gs : Vec Nat m) k (a b c : Vec Nat m) → Lo k a → Lo k b → Lo k c → Lo (k * 3) (cyl gs a b c)
cyl-Lo []       k       []      []      []      ha hb hc d p = refl
cyl-Lo (g ∷ gs) zero    (x ∷ a) (y ∷ b) (z ∷ c) ha hb hc d p with even g
... | true  = go d
  where
  go : ∀ d → at0 (x ∷ y ∷ z ∷ cyl gs a b c) d ≡ 0
  go zero                = ha 0 z≤n
  go (suc zero)          = hb 0 z≤n
  go (suc (suc zero))    = hc 0 z≤n
  go (suc (suc (suc d))) = cyl-Lo gs zero a b c (λ d _ → ha (suc d) z≤n) (λ d _ → hb (suc d) z≤n) (λ d _ → hc (suc d) z≤n) d z≤n
... | false = go d
  where
  go : ∀ d → at0 (z ∷ y ∷ x ∷ cyl gs a b c) d ≡ 0
  go zero                = hc 0 z≤n
  go (suc zero)          = hb 0 z≤n
  go (suc (suc zero))    = ha 0 z≤n
  go (suc (suc (suc d))) = cyl-Lo gs zero a b c (λ d _ → ha (suc d) z≤n) (λ d _ → hb (suc d) z≤n) (λ d _ → hc (suc d) z≤n) d z≤n
cyl-Lo (g ∷ gs) (suc k) (x ∷ a) (y ∷ b) (z ∷ c) ha hb hc (suc (suc (suc d))) (s≤s (s≤s (s≤s p))) with even g
... | true  = cyl-Lo gs k a b c (λ d q → ha (suc d) (s≤s q)) (λ d q → hb (suc d) (s≤s q)) (λ d q → hc (suc d) (s≤s q)) d p
... | false = cyl-Lo gs k a b c (λ d q → ha (suc d) (s≤s q)) (λ d q → hb (suc d) (s≤s q)) (λ d q → hc (suc d) (s≤s q)) d p

cyl-Hi : ∀ {m} (gs : Vec Nat m) k (a b c : Vec Nat m) → Hi k a → Hi k b → Hi k c → Hi (k * 3) (cyl gs a b c)
cyl-Hi gs       zero    a       b       c       ha hb hc d       ()
cyl-Hi []       (suc k) []      []      []      ha hb hc d       p = refl
cyl-Hi (g ∷ gs) (suc k) (x ∷ a) (y ∷ b) (z ∷ c) ha hb hc d p with even g
... | true  = go d p
  where
  go : ∀ d → d < suc k * 3 → at0 (x ∷ y ∷ z ∷ cyl gs a b c) d ≡ 0
  go zero                _ = ha 0 (s≤s z≤n)
  go (suc zero)          _ = hb 0 (s≤s z≤n)
  go (suc (suc zero))    _ = hc 0 (s≤s z≤n)
  go (suc (suc (suc d))) (s≤s (s≤s (s≤s q))) =
    cyl-Hi gs k a b c (λ d q → ha (suc d) (s≤s q)) (λ d q → hb (suc d) (s≤s q)) (λ d q → hc (suc d) (s≤s q)) d q
... | false = go d p
  where
  go : ∀ d → d < suc k * 3 → at0 (z ∷ y ∷ x ∷ cyl gs a b c) d ≡ 0
  go zero                _ = hc 0 (s≤s z≤n)
  go (suc zero)          _ = hb 0 (s≤s z≤n)
  go (suc (suc zero))    _ = ha 0 (s≤s z≤n)
  go (suc (suc (suc d))) (s≤s (s≤s (s≤s q))) =
    cyl-Hi gs k a b c (λ d q → ha (suc d) (s≤s q)) (λ d q → hb (suc d) (s≤s q)) (λ d q → hc (suc d) (s≤s q)) d q

private
  if-cons : ∀ {m} b (u v : Vec Nat m) →
    _≡_ {A = Vec Nat (suc m)} (if b then (0 ∷ u) else (0 ∷ v)) (0 ∷ (if b then u else v))
  if-cons true  u v = refl
  if-cons false u v = refl

cyl-unit-lo : ∀ {m} (gs : Vec Nat m) k → k < m →
  cyl gs (if even (at 0 gs k) then unit k else 0c) 0c (if odd (at 0 gs k) then unit k else 0c) ≡ unit (k * 3)
cyl-unit-lo (g ∷ gs) zero    _ = go (even g) refl
  where
  go : ∀ b → even g ≡ b → cyl (g ∷ gs) (if b then unit 0 else 0c) 0c (if not b then unit 0 else 0c) ≡ unit 0
  go true  e rewrite e = cong (λ q → 1 ∷ 0 ∷ 0 ∷ q) (cyl-0 gs)
  go false e rewrite e = cong (λ q → 1 ∷ 0 ∷ 0 ∷ q) (cyl-0 gs)
cyl-unit-lo {suc n} (g ∷ gs) (suc k) (s≤s l)
  rewrite if-cons {n} (even (at 0 gs k)) (unit k) 0c | if-cons {n} (not (even (at 0 gs k))) (unit k) 0c with even g
... | true  = cong (λ q → 0 ∷ 0 ∷ 0 ∷ q) (cyl-unit-lo gs k l)
... | false = cong (λ q → 0 ∷ 0 ∷ 0 ∷ q) (cyl-unit-lo gs k l)

cyl-unit-hi : ∀ {m} (gs : Vec Nat m) k → k < m →
  cyl gs (if odd (at 0 gs k) then unit k else 0c) 0c (if even (at 0 gs k) then unit k else 0c) ≡ unit (k * 3 + 2)
cyl-unit-hi (g ∷ gs) zero    _ = go (even g) refl
  where
  go : ∀ b → even g ≡ b → cyl (g ∷ gs) (if not b then unit 0 else 0c) 0c (if b then unit 0 else 0c) ≡ unit 2
  go true  e rewrite e = cong (λ q → 0 ∷ 0 ∷ 1 ∷ q) (cyl-0 gs)
  go false e rewrite e = cong (λ q → 0 ∷ 0 ∷ 1 ∷ q) (cyl-0 gs)
cyl-unit-hi {suc n} (g ∷ gs) (suc k) (s≤s l)
  rewrite if-cons {n} (even (at 0 gs k)) (unit k) 0c | if-cons {n} (not (even (at 0 gs k))) (unit k) 0c with even g
... | true  = cong (λ q → 0 ∷ 0 ∷ 0 ∷ q) (cyl-unit-hi gs k l)
... | false = cong (λ q → 0 ∷ 0 ∷ 0 ∷ q) (cyl-unit-hi gs k l)

cyl-unit-mid : ∀ {m} (gs : Vec Nat m) k → k < m → cyl gs 0c (unit k) 0c ≡ unit (k * 3 + 1)
cyl-unit-mid (g ∷ gs) zero    _ with even g
... | true  = cong (λ q → 0 ∷ 1 ∷ 0 ∷ q) (cyl-0 gs)
... | false = cong (λ q → 0 ∷ 1 ∷ 0 ∷ q) (cyl-0 gs)
cyl-unit-mid (g ∷ gs) (suc k) (s≤s l) with even g
... | true  = cong (λ q → 0 ∷ 0 ∷ 0 ∷ q) (cyl-unit-mid gs k l)
... | false = cong (λ q → 0 ∷ 0 ∷ 0 ∷ q) (cyl-unit-mid gs k l)

at-map-lt : ∀ {A B : Set} {m} (f : A → B) (d : A) (d′ : B) (xs : Vec A m) k → k < m → at d′ (mapV f xs) k ≡ f (at d xs k)
at-map-lt f d d′ (x ∷ xs) zero    _       = refl
at-map-lt f d d′ (x ∷ xs) (suc k) (s≤s l) = at-map-lt f d d′ xs k l

augm-0 : ∀ {m} (gs : Vec Nat m) → augm gs 0c ≡ 0
augm-0 []       = refl
augm-0 (g ∷ gs) with g ==ℕ 0
... | true  = augm-0 gs
... | false = augm-0 gs

------------------------------------------------------------------------
-- The cylinder of a basis.

module Cyl {N : Nat} (B : Basis N) where
  open Basis B

  Ev Od : Vec Nat N → Vec Nat N
  Ev = sel even gdeg
  Od = sel odd gdeg

  EvU OdU : Vec (Vec Nat N) N
  EvU = selV even gdeg (units N)
  OdU = selV odd gdeg (units N)

  c0 c1 cm : Vec Nat N → Vec Nat (N * 3)
  c0 v = cyl gdeg v 0c 0c
  cm v = cyl gdeg 0c v 0c
  c1 v = cyl gdeg 0c 0c v

  gdeg′ : Vec Nat (N * 3)
  gdeg′ = cyl gdeg gdeg (mapV suc gdeg) gdeg

  bplus′ bminus′ : Vec (Vec Nat (N * 3)) (N * 3)
  bplus′  = cylA gdeg (mapV c0 bplus)  (zip3 (cyl gdeg) OdU bplus EvU)  (mapV c1 bplus)
  bminus′ = cylA gdeg (mapV c0 bminus) (zip3 (cyl gdeg) EvU bminus OdU) (mapV c1 bminus)

  B′ : Basis (N * 3)
  B′ = record { gdeg = gdeg′ ; bplus = bplus′ ; bminus = bminus′ }

  private
    hom0 : ∀ u v → c0 (u +c v) ≡ c0 u +c c0 v
    hom0 u v = trans (cong₂ (λ p q → cyl gdeg (u +c v) p q) (sym (+c-id 0c)) (sym (+c-id 0c))) (cyl-+ gdeg u 0c 0c v 0c 0c)
    hom1 : ∀ u v → c1 (u +c v) ≡ c1 u +c c1 v
    hom1 u v = trans (cong₂ (λ p q → cyl gdeg p q (u +c v)) (sym (+c-id 0c)) (sym (+c-id 0c))) (cyl-+ gdeg 0c 0c u 0c 0c v)

  Ev-lin : ∀ u → lin u EvU ≡ Ev u
  Ev-lin u = trans (lin-sel even gdeg u (units N)) (lin-units (Ev u))

  Od-lin : ∀ u → lin u OdU ≡ Od u
  Od-lin u = trans (lin-sel odd gdeg u (units N)) (lin-units (Od u))

  dP-cyl : ∀ a b c → dP B′ (cyl gdeg a b c) ≡ cyl gdeg (dP B a +c Od b) (dP B b) (Ev b +c dP B c)
  dP-cyl a b c =
    trans (lin-cyl gdeg a b c _ _ _)
    (trans (cong₂ (λ x z → (x +c lin b (zip3 (cyl gdeg) OdU bplus EvU)) +c z)
                  (lin-hom c0 hom0 (cyl-0 gdeg) a bplus) (lin-hom c1 hom1 (cyl-0 gdeg) c bplus))
    (trans (cong (λ y → (c0 (dP B a) +c y) +c c1 (dP B c))
                 (trans (lin-zip3 gdeg b OdU bplus EvU) (cong₂ (λ x z → cyl gdeg x (dP B b) z) (Od-lin b) (Ev-lin b))))
    (trans (cong (_+c c1 (dP B c)) (sym (cyl-+ gdeg _ _ _ _ _ _)))
    (trans (sym (cyl-+ gdeg _ _ _ _ _ _))
           (cong₃ (cyl gdeg) (r0 (dP B a +c Od b))
                             (trans (r0 (0c +c dP B b)) (+c-id (dP B b)))
                             (cong (_+c dP B c) (+c-id (Ev b))))))))
    where
    r0 : ∀ v → v +c 0c ≡ v
    r0 v = trans (+c-comm v 0c) (+c-id v)
    cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x x′ y y′ z z′} → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
    cong₃ f refl refl refl = refl

  dM-cyl : ∀ a b c → dM B′ (cyl gdeg a b c) ≡ cyl gdeg (dM B a +c Ev b) (dM B b) (Od b +c dM B c)
  dM-cyl a b c =
    trans (lin-cyl gdeg a b c _ _ _)
    (trans (cong₂ (λ x z → (x +c lin b (zip3 (cyl gdeg) EvU bminus OdU)) +c z)
                  (lin-hom c0 hom0 (cyl-0 gdeg) a bminus) (lin-hom c1 hom1 (cyl-0 gdeg) c bminus))
    (trans (cong (λ y → (c0 (dM B a) +c y) +c c1 (dM B c))
                 (trans (lin-zip3 gdeg b EvU bminus OdU) (cong₂ (λ x z → cyl gdeg x (dM B b) z) (Ev-lin b) (Od-lin b))))
    (trans (cong (_+c c1 (dM B c)) (sym (cyl-+ gdeg _ _ _ _ _ _)))
    (trans (sym (cyl-+ gdeg _ _ _ _ _ _))
           (cong₃ (cyl gdeg) (r0 (dM B a +c Ev b))
                             (trans (r0 (0c +c dM B b)) (+c-id (dM B b)))
                             (cong (_+c dM B c) (+c-id (Od b))))))))
    where
    r0 : ∀ v → v +c 0c ≡ v
    r0 v = trans (+c-comm v 0c) (+c-id v)
    cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x x′ y y′ z z′} → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
    cong₃ f refl refl refl = refl

------------------------------------------------------------------------
-- ∂∂ = 0 on the cylinder.

module CylDD {N : Nat} (B : Basis N) (H : Hyp B) (dgp : DegP B) (dgm : DegM B) where
  open Basis B
  open Cyl B
  open Hyp H using (dd)

  private
    dp = dP B
    dm = dM B
    df = degFix B

  Od-deg : ∀ h v → sel odd gdeg (df h v) ≡ (if even h then df h v else 0c)
  Od-deg zero    v = sel-0 odd gdeg
  Od-deg (suc j) v rewrite even-suc j with even j in q
  ... | true  = sel-prj-out odd j gdeg v (cong not q)
  ... | false = sel-prj-in odd j gdeg v (cong not q)

  Ev-deg : ∀ h v → sel even gdeg (df h v) ≡ (if odd h then df h v else 0c)
  Ev-deg zero    v = sel-0 even gdeg
  Ev-deg (suc j) v rewrite even-suc j with even j in q
  ... | true  = sel-prj-in even j gdeg v q
  ... | false = sel-prj-out even j gdeg v q

  mapV-sel : ∀ {m} (p q : Nat → Bool) (hs : Vec Nat m) (vs : Vec (Vec Nat N) m) →
             (∀ h v → sel p gdeg (df h v) ≡ (if q h then df h v else 0c)) →
             zipV df hs vs ≡ vs → mapV (sel p gdeg) vs ≡ selV q hs vs
  mapV-sel p q []       []       h E = refl
  mapV-sel p q (g ∷ hs) (v ∷ vs) h E =
    let (e1 , e2) = vcons-inj E in
    cong₂ _∷_ (trans (cong (sel p gdeg) (sym e1)) (trans (h g v) (cong (λ w → if q g then w else 0c) e1)))
              (mapV-sel p q hs vs h e2)

  private
    shift : ∀ (p q : Nat → Bool) (bs : Vec (Vec Nat N) N) →
            (∀ h v → sel p gdeg (df h v) ≡ (if q h then df h v else 0c)) → zipV df gdeg bs ≡ bs →
            ∀ u → sel p gdeg (lin u bs) ≡ lin (sel q gdeg u) bs
    shift p q bs h E u =
      trans (sym (lin-hom (sel p gdeg) (sel-+ p gdeg) (sel-0 p gdeg) u bs))
            (trans (cong (lin u) (mapV-sel p q gdeg bs h E)) (lin-sel q gdeg u bs))

  Od-dP : ∀ u → Od (dp u) ≡ dp (Ev u)
  Od-dP = shift odd even bplus Od-deg dgp
  Ev-dP : ∀ u → Ev (dp u) ≡ dp (Od u)
  Ev-dP = shift even odd bplus Ev-deg dgp
  Od-dM : ∀ u → Od (dm u) ≡ dm (Ev u)
  Od-dM = shift odd even bminus Od-deg dgm
  Ev-dM : ∀ u → Ev (dm u) ≡ dm (Od u)
  Ev-dM = shift even odd bminus Ev-deg dgm

  private
    dp′ = dP B′
    dm′ = dM B′
    lp : ∀ x y → dp (x +c y) ≡ dp x +c dp y
    lp x y = lin-+ x y bplus
    lm : ∀ x y → dm (x +c y) ≡ dm x +c dm y
    lm x y = lin-+ x y bminus
    cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x x′ y y′ z z′} → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
    cong₃ f refl refl refl = refl

  dd-cyl : ∀ a b c →
    dp′ (dp′ (cyl gdeg a b c)) +c dm′ (dm′ (cyl gdeg a b c)) ≡ dp′ (dm′ (cyl gdeg a b c)) +c dm′ (dp′ (cyl gdeg a b c))
  dd-cyl a b c =
    trans (cong₂ _+c_ (trans (cong dp′ (dP-cyl a b c)) (dP-cyl _ _ _)) (trans (cong dm′ (dM-cyl a b c)) (dM-cyl _ _ _)))
    (trans (sym (cyl-+ gdeg _ _ _ _ _ _))
    (trans (cong₃ (cyl gdeg) c0-eq (dd b) c1-eq)
    (trans (cyl-+ gdeg _ _ _ _ _ _)
           (sym (cong₂ _+c_ (trans (cong dp′ (dM-cyl a b c)) (dP-cyl _ _ _)) (trans (cong dm′ (dP-cyl a b c)) (dM-cyl _ _ _)))))))
    where
    open Solver (chainMon N)
    c0-eq : (dp (dp a +c Od b) +c Od (dp b)) +c (dm (dm a +c Ev b) +c Ev (dm b))
          ≡ (dp (dm a +c Ev b) +c Od (dm b)) +c (dm (dp a +c Od b) +c Ev (dp b))
    c0-eq =
      trans (cong₂ _+c_ (cong₂ _+c_ (lp (dp a) (Od b)) (Od-dP b)) (cong₂ _+c_ (lm (dm a) (Ev b)) (Ev-dM b)))
      (trans (solve (((` 0 ⊞ ` 4) ⊞ ` 5) ⊞ ((` 1 ⊞ ` 6) ⊞ ` 7)) ((` 0 ⊞ ` 1) ⊞ ((` 4 ⊞ ` 5) ⊞ (` 6 ⊞ ` 7)))
                    (lk (dp (dp a) ∷ dm (dm a) ∷ dp (dm a) ∷ dm (dp a) ∷ dp (Od b) ∷ dp (Ev b) ∷ dm (Ev b) ∷ dm (Od b) ∷ [])) tt)
      (trans (cong (_+c ((dp (Od b) +c dp (Ev b)) +c (dm (Ev b) +c dm (Od b)))) (dd a))
      (trans (solve ((` 2 ⊞ ` 3) ⊞ ((` 4 ⊞ ` 5) ⊞ (` 6 ⊞ ` 7))) (((` 2 ⊞ ` 5) ⊞ ` 6) ⊞ ((` 3 ⊞ ` 7) ⊞ ` 4))
                    (lk (dp (dp a) ∷ dm (dm a) ∷ dp (dm a) ∷ dm (dp a) ∷ dp (Od b) ∷ dp (Ev b) ∷ dm (Ev b) ∷ dm (Od b) ∷ [])) tt)
             (sym (cong₂ _+c_ (cong₂ _+c_ (lp (dm a) (Ev b)) (Od-dM b)) (cong₂ _+c_ (lm (dp a) (Od b)) (Ev-dP b)))))))
    c1-eq : (Ev (dp b) +c dp (Ev b +c dp c)) +c (Od (dm b) +c dm (Od b +c dm c))
          ≡ (Ev (dm b) +c dp (Od b +c dm c)) +c (Od (dp b) +c dm (Ev b +c dp c))
    c1-eq =
      trans (cong₂ _+c_ (cong₂ _+c_ (Ev-dP b) (lp (Ev b) (dp c))) (cong₂ _+c_ (Od-dM b) (lm (Od b) (dm c))))
      (trans (solve ((` 4 ⊞ (` 5 ⊞ ` 0)) ⊞ (` 6 ⊞ (` 7 ⊞ ` 1))) ((` 0 ⊞ ` 1) ⊞ ((` 4 ⊞ ` 5) ⊞ (` 6 ⊞ ` 7)))
                    (lk (dp (dp c) ∷ dm (dm c) ∷ dp (dm c) ∷ dm (dp c) ∷ dp (Od b) ∷ dp (Ev b) ∷ dm (Ev b) ∷ dm (Od b) ∷ [])) tt)
      (trans (cong (_+c ((dp (Od b) +c dp (Ev b)) +c (dm (Ev b) +c dm (Od b)))) (dd c))
      (trans (solve ((` 2 ⊞ ` 3) ⊞ ((` 4 ⊞ ` 5) ⊞ (` 6 ⊞ ` 7))) ((` 7 ⊞ (` 4 ⊞ ` 2)) ⊞ (` 5 ⊞ (` 6 ⊞ ` 3)))
                    (lk (dp (dp c) ∷ dm (dm c) ∷ dp (dm c) ∷ dm (dp c) ∷ dp (Od b) ∷ dp (Ev b) ∷ dm (Ev b) ∷ dm (Od b) ∷ [])) tt)
             (sym (cong₂ _+c_ (cong₂ _+c_ (Ev-dM b) (lp (Od b) (dm c))) (cong₂ _+c_ (Od-dP b) (lm (Ev b) (dp c))))))))

  dd′ : ∀ x → dp′ (dp′ x) +c dm′ (dm′ x) ≡ dp′ (dm′ x) +c dm′ (dp′ x)
  dd′ x = subst (λ y → dp′ (dp′ y) +c dm′ (dm′ y) ≡ dp′ (dm′ y) +c dm′ (dp′ y)) (cyl-uncyl gdeg x) (dd-cyl _ _ _)

  ----------------------------------------------------------------------
  -- Degrees and augmentation.

  private
    lin-prj0 : ∀ {m} (gs b : Vec Nat m) (vs : Vec (Vec Nat N) m) → lin (prj 0 gs b) (zipV df gs vs) ≡ 0c
    lin-prj0 []       []      []       = refl
    lin-prj0 (g ∷ gs) (a ∷ b) (v ∷ vs) with g ==ℕ 0
    ... | true  = trans (cong (_+c lin (prj 0 gs b) (zipV df gs vs)) (⊙-0c a)) (trans (+c-id _) (lin-prj0 gs b vs))
    ... | false = trans (+c-id _) (lin-prj0 gs b vs)

    deg0 : ∀ (bs : Vec (Vec Nat N) N) → zipV df gdeg bs ≡ bs → ∀ b → prj 0 gdeg b ≡ b → lin b bs ≡ 0c
    deg0 bs E b e = trans (cong₂ lin (sym e) (sym E)) (lin-prj0 gdeg b bs)

    gen-deg : (D : Vec Nat (N * 3) → Vec Nat (N * 3)) (d : Vec Nat N → Vec Nat N) (P Q : Vec Nat N → Vec Nat N) →
              (∀ a b c → D (cyl gdeg a b c) ≡ cyl gdeg (d a +c P b) (d b) (Q b +c d c)) →
              (∀ x y → d (x +c y) ≡ d x +c d y) →
              (∀ j c → prj (suc j) gdeg c ≡ c → prj j gdeg (d c) ≡ d c) →
              (∀ b → prj 0 gdeg b ≡ b → d b ≡ 0c) →
              (∀ j b → prj j gdeg (P b) ≡ P (prj j gdeg b)) →
              (∀ j b → prj j gdeg (Q b) ≡ Q (prj j gdeg b)) →
              ∀ j x → prj (suc j) gdeg′ x ≡ x → prj j gdeg′ (D x) ≡ D x
    gen-deg D d P Q Dc dl dg d0 Pp Qp j x hx =
      subst (λ y → prj (suc j) gdeg′ y ≡ y → prj j gdeg′ (D y) ≡ D y) (cyl-uncyl gdeg x) (go _ _ _) hx
      where
      go : ∀ a b c → prj (suc j) gdeg′ (cyl gdeg a b c) ≡ cyl gdeg a b c → prj j gdeg′ (D (cyl gdeg a b c)) ≡ D (cyl gdeg a b c)
      go a b c h =
        let (ea , eb′ , ec) = cyl-inj gdeg (trans (sym (prj-cyl (suc j) gdeg gdeg (mapV suc gdeg) gdeg a b c)) h)
            eb : prj j gdeg b ≡ b
            eb = trans (sym (prj-sucS j gdeg b)) eb′
        in trans (cong (prj j gdeg′) (Dc a b c))
           (trans (prj-cyl j gdeg gdeg (mapV suc gdeg) gdeg _ _ _)
           (trans (cong₃ (cyl gdeg)
                     (trans (prj-+ j gdeg (d a) (P b)) (cong₂ _+c_ (dg j a ea) (trans (Pp j b) (cong P eb))))
                     (mid j b eb)
                     (trans (prj-+ j gdeg (Q b) (d c)) (cong₂ _+c_ (trans (Qp j b) (cong Q eb)) (dg j c ec))))
                  (sym (Dc a b c))))
        where
        mid : ∀ j b → prj j gdeg b ≡ b → prj j (mapV suc gdeg) (d b) ≡ d b
        mid zero    b eb = trans (prj-suc0 gdeg (d b)) (sym (d0 b eb))
        mid (suc j) b eb = trans (prj-sucS j gdeg (d b)) (dg j b eb)

  deg-dp′ : ∀ j x → prj (suc j) gdeg′ x ≡ x → prj j gdeg′ (dp′ x) ≡ dp′ x
  deg-dp′ = gen-deg dp′ dp Od Ev dP-cyl lp (Hyp.deg-dp H) (deg0 bplus dgp) (λ j → prj-sel j odd gdeg) (λ j → prj-sel j even gdeg)

  deg-dm′ : ∀ j x → prj (suc j) gdeg′ x ≡ x → prj j gdeg′ (dm′ x) ≡ dm′ x
  deg-dm′ = gen-deg dm′ dm Ev Od dM-cyl lm (Hyp.deg-dm H) (deg0 bminus dgm) (λ j → prj-sel j even gdeg) (λ j → prj-sel j odd gdeg)

  aug1′ : ∀ x → prj 1 gdeg′ x ≡ x → augm gdeg′ (dp′ x) ≡ augm gdeg′ (dm′ x)
  aug1′ x hx = subst (λ y → prj 1 gdeg′ y ≡ y → augm gdeg′ (dp′ y) ≡ augm gdeg′ (dm′ y)) (cyl-uncyl gdeg x) (go _ _ _) hx
    where
    open Solver (record { M = Nat ; ε = 0 ; _⊕_ = _+_ ; ⊕-id = λ _ → refl ; ⊕-comm = +-comm ; ⊕-assoc = +-assoc })
    au = augm gdeg
    go : ∀ a b c → prj 1 gdeg′ (cyl gdeg a b c) ≡ cyl gdeg a b c → augm gdeg′ (dp′ (cyl gdeg a b c)) ≡ augm gdeg′ (dm′ (cyl gdeg a b c))
    go a b c h =
      let (ea , _ , ec) = cyl-inj gdeg (trans (sym (prj-cyl 1 gdeg gdeg (mapV suc gdeg) gdeg a b c)) h) in
      trans (cong (augm gdeg′) (dP-cyl a b c))
      (trans (augm-cyl gdeg gdeg (mapV suc gdeg) gdeg _ _ _)
      (trans (cong₃ (λ x y z → (x + y) + z) (augm-+′ gdeg (dp a) (Od b)) (augm-suc gdeg (dp b)) (augm-+′ gdeg (Ev b) (dp c)))
      (trans (cong₂ (λ p q → ((p + au (Od b)) + 0) + (au (Ev b) + q)) (Hyp.aug1 H a ea) (Hyp.aug1 H c ec))
      (trans (solve (((` 0 ⊞ ` 1) ⊞ ` 4) ⊞ (` 2 ⊞ ` 3)) (((` 0 ⊞ ` 2) ⊞ ` 4) ⊞ (` 1 ⊞ ` 3))
                    (lk (au (dm a) ∷ au (Od b) ∷ au (Ev b) ∷ au (dm c) ∷ 0 ∷ [])) tt)
      (sym (trans (cong (augm gdeg′) (dM-cyl a b c))
           (trans (augm-cyl gdeg gdeg (mapV suc gdeg) gdeg _ _ _)
                  (cong₃ (λ x y z → (x + y) + z) (augm-+′ gdeg (dm a) (Ev b)) (augm-suc gdeg (dm b)) (augm-+′ gdeg (Od b) (dm c))))))))))

  ----------------------------------------------------------------------
  -- The order: negative faces before, positive faces after.

  private
    r0 : ∀ (v : Vec Nat N) → v +c 0c ≡ v
    r0 v = trans (+c-comm v 0c) (+c-id v)

    Lo-+ : ∀ {m t} (u v : Vec Nat m) → Lo t u → Lo t v → Lo t (u +c v)
    Lo-+ u v hu hv d p = trans (at-+c u v d) (cong₂ _+_ (hu d p) (hv d p))

    Hi-+ : ∀ {m t} (u v : Vec Nat m) → Hi t u → Hi t v → Hi t (u +c v)
    Hi-+ u v hu hv d p = trans (at-+c u v d) (cong₂ _+_ (hu d p) (hv d p))

    Lo-mono : ∀ {m t t′} {u : Vec Nat m} → Lo t u → t ≤ t′ → Lo t′ u
    Lo-mono h p d q = h d (≤-trans p q)

    Hi-mono : ∀ {m t t′} {u : Vec Nat m} → Hi t u → t′ ≤ t → Hi t′ u
    Hi-mono h p d q = h d (≤-trans q p)

    Lo-0 : ∀ {m} t → Lo t (0c {m})
    Lo-0 {m} t d _ = at-0c {m} d

    Hi-0 : ∀ {m} t → Hi t (0c {m})
    Hi-0 {m} t d _ = at-0c {m} d

    ≤r′ : ∀ a r → a ≤ a + r
    ≤r′ zero    r = z≤n
    ≤r′ (suc a) r = s≤s (≤r′ a r)

    +-mono-r : ∀ a {r r′} → r ≤ r′ → a + r ≤ a + r′
    +-mono-r zero    p = p
    +-mono-r (suc a) p = s≤s (+-mono-r a p)

    *3-mono′ : ∀ {a b} → a ≤ b → a * 3 ≤ b * 3
    *3-mono′ z≤n     = z≤n
    *3-mono′ (s≤s p) = s≤s (s≤s (s≤s (*3-mono′ p)))

    at-out′ : ∀ {A : Set} {m} (d : A) (vs : Vec A m) i → m ≤ i → at d vs i ≡ d
    at-out′ d []       i       _       = refl
    at-out′ d (v ∷ vs) (suc i) (s≤s q) = at-out′ d vs i q

    slot-elim : ∀ {A : Set} (P : A → Set) b r x y z → P x → P z → (r ≡ 1 → P y) → P (slot b r x y z)
    slot-elim P true  zero          x y z px pz py = px
    slot-elim P true  (suc zero)    x y z px pz py = py refl
    slot-elim P true  (suc (suc _)) x y z px pz py = pz
    slot-elim P false zero          x y z px pz py = pz
    slot-elim P false (suc zero)    x y z px pz py = py refl
    slot-elim P false (suc (suc _)) x y z px pz py = px

    at-zip3 : ∀ {A B C D : Set} {m} (f : A → B → C → D) (a : A) (b : B) (c : C) (d : D) →
              (xs : Vec A m) (ys : Vec B m) (zs : Vec C m) → ∀ k → k < m →
              at d (zip3 f xs ys zs) k ≡ f (at a xs k) (at b ys k) (at c zs k)
    at-zip3 f a b c d (x ∷ xs) (y ∷ ys) (z ∷ zs) zero    _       = refl
    at-zip3 f a b c d (x ∷ xs) (y ∷ ys) (z ∷ zs) (suc k) (s≤s l) = at-zip3 f a b c d xs ys zs k l

    g = λ k → at 0 gdeg k

    if-same : ∀ {A : Set} b (v : A) → (if b then v else v) ≡ v
    if-same true  v = refl
    if-same false v = refl

    at-sel : ∀ (p : Nat → Bool) k → k < N → at 0c (selV p gdeg (units N)) k ≡ (if p (g k) then unit k else 0c)
    at-sel p k kN = trans (at-zip (λ h v → if p h then v else 0c) 0 0c 0c (if-same (p 0) 0c) gdeg (units N) k)
                          (cong (λ v → if p (g k) then v else 0c) (at-units N k kN))

    E = λ k → if even (g k) then unit {N} k else 0c
    O = λ k → if odd (g k) then unit {N} k else 0c

    split : ∀ (x b y : Vec Nat N) → cyl gdeg x b y ≡ cyl gdeg x 0c y +c cyl gdeg 0c b 0c
    split x b y = trans (cong₂ (λ p q → cyl gdeg p q y) (sym (r0 x)) (sym (+c-id b)))
                    (trans (cong (cyl gdeg (x +c 0c) (0c +c b)) (sym (r0 y))) (cyl-+ gdeg x 0c y 0c b 0c))

    bm = λ k → at 0c bminus k
    bp = λ k → at 0c bplus k

    at-bminus′ : ∀ k r → k < N → r < 3 →
      at 0c bminus′ (k * 3 + r) ≡ slot (even (g k)) r (c0 (bm k)) (cyl gdeg (E k) (bm k) (O k)) (c1 (bm k))
    at-bminus′ k r kN rl =
      trans (at-cylA 0c gdeg _ _ _ k r kN rl)
            (cong₃ (slot (even (g k)) r) (at-map c0 0c 0c (cyl-0 gdeg) bminus k)
                   (trans (at-zip3 (cyl gdeg) 0c 0c 0c 0c EvU bminus OdU k kN)
                          (cong₃ (cyl gdeg) (at-sel even k kN) refl (at-sel odd k kN)))
                   (at-map c1 0c 0c (cyl-0 gdeg) bminus k))

    at-bplus′ : ∀ k r → k < N → r < 3 →
      at 0c bplus′ (k * 3 + r) ≡ slot (even (g k)) r (c0 (bp k)) (cyl gdeg (O k) (bp k) (E k)) (c1 (bp k))
    at-bplus′ k r kN rl =
      trans (at-cylA 0c gdeg _ _ _ k r kN rl)
            (cong₃ (slot (even (g k)) r) (at-map c0 0c 0c (cyl-0 gdeg) bplus k)
                   (trans (at-zip3 (cyl gdeg) 0c 0c 0c 0c OdU bplus EvU k kN)
                          (cong₃ (cyl gdeg) (at-sel odd k kN) refl (at-sel even k kN)))
                   (at-map c1 0c 0c (cyl-0 gdeg) bplus k))

    +1 : ∀ a → a + 1 ≡ suc a
    +1 a = trans (+-suc a 0) (cong suc (+-zero a))

  ordm′ : ∀ n d → n ≤ d → at0 (at 0c bminus′ n) d ≡ 0
  ordm′ n d p with divmod n
  ... | (k , r , rl , refl) with ≤-dec N k
  ...   | inj₁ Nk = trans (cong (λ v → at0 v d) (at-out′ 0c bminus′ (k * 3 + r) (≤-trans (*3-mono′ Nk) (≤r′ (k * 3) r)))) (at-0c {N * 3} d)
  ...   | inj₂ kN = trans (cong (λ v → at0 v d) (at-bminus′ k r kN rl))
                      (slot-elim (λ V → at0 V d ≡ 0) (even (g k)) r _ _ _
                        (cyl-Lo gdeg k (bm k) 0c 0c LoK (Lo-0 {N} k) (Lo-0 {N} k) d kd)
                        (cyl-Lo gdeg k 0c 0c (bm k) (Lo-0 {N} k) (Lo-0 {N} k) LoK d kd)
                        mid-Lo)
    where
    LoK : Lo k (bm k)
    LoK = Hyp.ordm H k
    kd : k * 3 ≤ d
    kd = ≤-trans (≤r′ (k * 3) r) p
    mid-Lo : r ≡ 1 → at0 (cyl gdeg (E k) (bm k) (O k)) d ≡ 0
    mid-Lo refl =
      trans (cong (λ v → at0 v d) (split (E k) (bm k) (O k)))
        (Lo-+ (cyl gdeg (E k) 0c (O k)) (cyl gdeg 0c (bm k) 0c)
          (subst (Lo (suc (k * 3))) (sym (cyl-unit-lo gdeg k kN)) (unit-Lo {N * 3} (k * 3)))
          (Lo-weak {u = cyl gdeg 0c (bm k) 0c} (cyl-Lo gdeg k 0c (bm k) 0c (Lo-0 {N} k) LoK (Lo-0 {N} k)))
          d (subst (_≤ d) (+1 (k * 3)) p))

  ordp′ : ∀ n d → d ≤ n → at0 (at 0c bplus′ n) d ≡ 0
  ordp′ n d p with divmod n
  ... | (k , r , rl , refl) with ≤-dec N k
  ...   | inj₁ Nk = trans (cong (λ v → at0 v d) (at-out′ 0c bplus′ (k * 3 + r) (≤-trans (*3-mono′ Nk) (≤r′ (k * 3) r)))) (at-0c {N * 3} d)
  ...   | inj₂ kN = trans (cong (λ v → at0 v d) (at-bplus′ k r kN rl))
                      (slot-elim (λ V → at0 V d ≡ 0) (even (g k)) r _ _ _
                        (cyl-Hi gdeg (suc k) (bp k) 0c 0c HiK (Hi-0 {N} (suc k)) (Hi-0 {N} (suc k)) d dk)
                        (cyl-Hi gdeg (suc k) 0c 0c (bp k) (Hi-0 {N} (suc k)) (Hi-0 {N} (suc k)) HiK d dk)
                        mid-Hi)
    where
    HiK : Hi (suc k) (bp k)
    HiK d q = Hyp.ordp H k d (≤-pred q)
    dk : d < suc k * 3
    dk = ≤-trans (s≤s p) (s≤s (≤-trans (+-mono-r (k * 3) (≤-pred rl)) (≤-of (trans (+-suc (k * 3) 1) (cong suc (+1 (k * 3)))))))
      where
      ≤-of : ∀ {a b} → a ≡ b → a ≤ b
      ≤-of refl = ≤-refl _
    mid-Hi : r ≡ 1 → at0 (cyl gdeg (O k) (bp k) (E k)) d ≡ 0
    mid-Hi refl =
      trans (cong (λ v → at0 v d) (split (O k) (bp k) (E k)))
        (Hi-+ (cyl gdeg (O k) 0c (E k)) (cyl gdeg 0c (bp k) 0c)
          (subst (Hi (k * 3 + 2)) (sym (cyl-unit-hi gdeg k kN)) (unit-Hi {N * 3} (k * 3 + 2)))
          (Hi-mono {u = cyl gdeg 0c (bp k) 0c} (cyl-Hi gdeg (suc k) 0c (bp k) 0c (Hi-0 {N} (suc k)) HiK (Hi-0 {N} (suc k))) (≤-trans (≤-suc (≤-refl _)) (s≤s (≤-of2 (k * 3)))))
          d (≤-trans (s≤s p) (≤-of2′ (k * 3))))
      where
      ≤-of2 : ∀ a → a + 2 ≤ suc (suc a)
      ≤-of2 a rewrite +-suc a 1 | +1 a = ≤-refl _
      ≤-of2′ : ∀ a → suc (a + 1) ≤ a + 2
      ≤-of2′ a rewrite +-suc a 1 = ≤-refl _

  ----------------------------------------------------------------------
  -- Atoms of the cylinder: one step down.

  private
    0∸′ : ∀ d → 0 ∸ d ≡ 0
    0∸′ zero    = refl
    0∸′ (suc d) = refl

    ∸-absorb : ∀ m p → m ∸ (p + (m ∸ p)) ≡ 0
    ∸-absorb zero    p       = 0∸′ (p + (0 ∸ p))
    ∸-absorb (suc m) zero    = ∸-self m
      where
      ∸-self : ∀ m → m ∸ m ≡ 0
      ∸-self zero    = refl
      ∸-self (suc m) = ∸-self m
    ∸-absorb (suc m) (suc p) = ∸-absorb m p

    ∸c-absorb : ∀ (u v : Vec Nat N) → u ∸c (v +c (u ∸c v)) ≡ 0c
    ∸c-absorb u v = vext _ _ λ d →
      trans (at-∸c u (v +c (u ∸c v)) d)
      (trans (cong (at0 u d ∸_) (trans (at-+c v (u ∸c v) d) (cong (at0 v d +_) (at-∸c u v d))))
      (trans (∸-absorb (at0 u d) (at0 v d)) (sym (at-0c {N} d))))

    ∸c-0r : ∀ {m} (u : Vec Nat m) → u ∸c 0c ≡ u
    ∸c-0r []      = refl
    ∸c-0r (a ∷ u) = cong₂ _∷_ (∸0 a) (∸c-0r u)
      where
      ∸0 : ∀ a → a ∸ 0 ≡ a
      ∸0 zero    = refl
      ∸0 (suc a) = refl

    ∸c-0l : ∀ {m} (u : Vec Nat m) → 0c ∸c u ≡ 0c
    ∸c-0l []      = refl
    ∸c-0l (a ∷ u) = cong₂ _∷_ (0∸′ a) (∸c-0l u)

    dm0 : dm 0c ≡ 0c
    dm0 = lin-0 bminus
    dp0 : dp 0c ≡ 0c
    dp0 = lin-0 bplus

  F G : Bool → Vec Nat N → Vec Nat N → Vec Nat (N * 3)
  F e a b = cyl gdeg (if e then a else 0c) b (if e then 0c else a)
  G e a b = cyl gdeg (if e then 0c else a) b (if e then a else 0c)

  stepF : ∀ e a b → Ev b ≡ (if e then 0c else b) → Od b ≡ (if e then b else 0c) →
          dm a ∸c (dp a +c b) ≡ 0c → dm′ (F e a b) ∸c dp′ (F e a b) ≡ F (not e) b (dm b ∸c dp b)
  stepF true  a b ev od z =
    trans (cong₂ _∸c_ (dM-cyl a b 0c) (dP-cyl a b 0c))
    (trans (cyl-∸ gdeg _ _ _ _ _ _)
           (cong₃ (cyl gdeg)
              (trans (cong₂ (λ x y → (dm a +c x) ∸c (dp a +c y)) ev od) (trans (cong (_∸c (dp a +c b)) (r0 (dm a))) z))
              refl
              (trans (cong₂ (λ x y → (x +c dm 0c) ∸c (y +c dp 0c)) od ev)
                 (trans (cong₂ (λ x y → (b +c x) ∸c (0c +c y)) dm0 dp0) (trans (cong₂ _∸c_ (r0 b) (+c-id 0c)) (∸c-0r b))))))
  stepF false a b ev od z =
    trans (cong₂ _∸c_ (dM-cyl 0c b a) (dP-cyl 0c b a))
    (trans (cyl-∸ gdeg _ _ _ _ _ _)
           (cong₃ (cyl gdeg)
              (trans (cong₂ (λ x y → (dm 0c +c x) ∸c (dp 0c +c y)) ev od)
                 (trans (cong₂ (λ x y → (x +c b) ∸c (y +c 0c)) dm0 dp0) (trans (cong₂ _∸c_ (+c-id b) (+c-id 0c)) (∸c-0r b))))
              refl
              (trans (cong₂ (λ x y → (x +c dm a) ∸c (y +c dp a)) od ev)
                 (trans (cong₂ _∸c_ (+c-id (dm a)) (+c-comm b (dp a))) z))))

  stepG : ∀ e a b → Ev b ≡ (if e then 0c else b) → Od b ≡ (if e then b else 0c) →
          dp a ∸c (dm a +c b) ≡ 0c → dp′ (G e a b) ∸c dm′ (G e a b) ≡ G (not e) b (dp b ∸c dm b)
  stepG true  a b ev od z =
    trans (cong₂ _∸c_ (dP-cyl 0c b a) (dM-cyl 0c b a))
    (trans (cyl-∸ gdeg _ _ _ _ _ _)
           (cong₃ (cyl gdeg)
              (trans (cong₂ (λ x y → (dp 0c +c x) ∸c (dm 0c +c y)) od ev)
                 (trans (cong₂ (λ x y → (x +c b) ∸c (y +c 0c)) dp0 dm0) (trans (cong₂ _∸c_ (+c-id b) (+c-id 0c)) (∸c-0r b))))
              refl
              (trans (cong₂ (λ x y → (x +c dp a) ∸c (y +c dm a)) ev od)
                 (trans (cong₂ _∸c_ (+c-id (dp a)) (+c-comm b (dm a))) z))))
  stepG false a b ev od z =
    trans (cong₂ _∸c_ (dP-cyl a b 0c) (dM-cyl a b 0c))
    (trans (cyl-∸ gdeg _ _ _ _ _ _)
           (cong₃ (cyl gdeg)
              (trans (cong₂ (λ x y → (dp a +c x) ∸c (dm a +c y)) od ev) (trans (cong (_∸c (dm a +c b)) (r0 (dp a))) z))
              refl
              (trans (cong₂ (λ x y → (x +c dp 0c) ∸c (y +c dm 0c)) ev od)
                 (trans (cong₂ (λ x y → (b +c x) ∸c (0c +c y)) dp0 dm0) (trans (cong₂ _∸c_ (r0 b) (+c-id 0c)) (∸c-0r b))))))

  ----------------------------------------------------------------------
  -- Atoms of the cylinder.

  module A = Atom B
  module A′ = Atom B′

  open A.Cells dd using (module Deg)
  open Deg (Hyp.deg-dp H) (Hyp.deg-dm H) using (deg-entK)

  private
    not-not : ∀ b → not (not b) ≡ b
    not-not true  = refl
    not-not false = refl

    if-not : ∀ b (v : Vec Nat N) → (if b then v else 0c) ≡ (if not b then 0c else v)
    if-not true  v = refl
    if-not false v = refl

    sel-conc : ∀ p m (v : Vec Nat N) → prj m gdeg v ≡ v → sel p gdeg v ≡ (if p m then v else 0c)
    sel-conc p m v e with p m in q
    ... | true  = trans (cong (sel p gdeg) (sym e)) (trans (sel-prj-in p m gdeg v q) e)
    ... | false = trans (cong (sel p gdeg) (sym e)) (sel-prj-out p m gdeg v q)

    ∸-suc′ : ∀ g j → suc j ≤ g → g ∸ j ≡ suc (g ∸ suc j)
    ∸-suc′ (suc g) zero    _       = refl
    ∸-suc′ (suc g) (suc j) (s≤s l) = ∸-suc′ g j l

    ∸-split : ∀ g j → j ≤ g → g ≡ j + (g ∸ j)
    ∸-split g       zero    _       = refl
    ∸-split (suc g) (suc j) (s≤s l) = cong suc (∸-split g j l)

  -- Endpoint copies of K.
  Hc : Bool → Vec Nat N → Vec Nat (N * 3)
  Hc b v = cyl gdeg (if b then v else 0c) 0c (if b then 0c else v)

  private
    dM-H : ∀ b x → dm′ (Hc b x) ≡ Hc b (dm x)
    dM-H true  x = trans (dM-cyl x 0c 0c) (cong₃ (cyl gdeg) (trans (cong (dm x +c_) (sel-0 even gdeg)) (r0 (dm x)))
                                                       dm0 (trans (cong₂ _+c_ (sel-0 odd gdeg) dm0) (+c-id 0c)))
    dM-H false x = trans (dM-cyl 0c 0c x) (cong₃ (cyl gdeg) (trans (cong₂ _+c_ dm0 (sel-0 even gdeg)) (+c-id 0c))
                                                       dm0 (trans (cong (_+c dm x) (sel-0 odd gdeg)) (+c-id (dm x))))
    dP-H : ∀ b x → dp′ (Hc b x) ≡ Hc b (dp x)
    dP-H true  x = trans (dP-cyl x 0c 0c) (cong₃ (cyl gdeg) (trans (cong (dp x +c_) (sel-0 odd gdeg)) (r0 (dp x)))
                                                       dp0 (trans (cong₂ _+c_ (sel-0 even gdeg) dp0) (+c-id 0c)))
    dP-H false x = trans (dP-cyl 0c 0c x) (cong₃ (cyl gdeg) (trans (cong₂ _+c_ dp0 (sel-0 odd gdeg)) (+c-id 0c))
                                                       dp0 (trans (cong (_+c dp x) (sel-0 even gdeg)) (+c-id (dp x))))
    ∸-H : ∀ b x y → Hc b x ∸c Hc b y ≡ Hc b (x ∸c y)
    ∸-H true  x y = trans (cyl-∸ gdeg _ _ _ _ _ _) (cong₂ (λ p q → cyl gdeg (x ∸c y) p q) (∸c-0r 0c) (∸c-0r 0c))
    ∸-H false x y = trans (cyl-∸ gdeg _ _ _ _ _ _) (cong₂ (λ p q → cyl gdeg p q (x ∸c y)) (∸c-0r 0c) (∸c-0r 0c))

  entK-end : ∀ b n k → unit n ≡ Hc b (unit k) → ∀ j →
             A′.entK n j ≡ (Hc b (fst (A.entK k j)) , Hc b (snd (A.entK k j)))
  entK-end b n k u zero    = cong₂ _,_ u u
  entK-end b n k u (suc j) =
    trans (cong A′.step (entK-end b n k u j))
          (cong₂ _,_ (trans (cong₂ _∸c_ (dM-H b _) (dP-H b _)) (∸-H b _ _))
                     (trans (cong₂ _∸c_ (dP-H b _) (dM-H b _)) (∸-H b _ _)))

  augm-H : ∀ b v → augm gdeg′ (Hc b v) ≡ augm gdeg v
  augm-H true  v = trans (augm-cyl gdeg gdeg (mapV suc gdeg) gdeg _ _ _)
                     (trans (cong₂ (λ p q → (augm gdeg v + p) + q) (augm-suc gdeg 0c) (augm-0 gdeg)) (trans (+-zero _) (+-zero _)))
  augm-H false v = trans (augm-cyl gdeg gdeg (mapV suc gdeg) gdeg _ _ _)
                     (cong₂ (λ p q → (p + q) + augm gdeg v) (augm-0 gdeg) (augm-suc gdeg 0c))

  -- The middle atom ⟨k⊗i⟩.
  module Mid (k : Nat) (kN : k < N) where
    gk = A.deg k
    Am Ap : Nat → Vec Nat N
    Am j = fst (A.entK k j)
    Ap j = snd (A.entK k j)
    pm pp : Nat → Vec Nat N
    pm zero    = 0c
    pm (suc j) = Am j
    pp zero    = 0c
    pp (suc j) = Ap j
    P : Nat → Bool
    P j = not (even (gk ∸ j))

    private
      conc : ∀ j → j ≤ gk → (prj (gk ∸ j) gdeg (Am j) ≡ Am j) × (prj (gk ∸ j) gdeg (Ap j) ≡ Ap j)
      conc j l = deg-entK k j (gk ∸ j) (∸-split gk j l)

      ev : ∀ j (v : Vec Nat N) → j ≤ gk → prj (gk ∸ j) gdeg v ≡ v → Ev v ≡ (if P j then 0c else v)
      ev j v l c = trans (sel-conc even (gk ∸ j) v c) (if-not (even (gk ∸ j)) v)
      od : ∀ j (v : Vec Nat N) → j ≤ gk → prj (gk ∸ j) gdeg v ≡ v → Od v ≡ (if P j then v else 0c)
      od j v l c = sel-conc odd (gk ∸ j) v c

      zm : ∀ j → dm (pm j) ∸c (dp (pm j) +c Am j) ≡ 0c
      zm zero    = trans (cong (_∸c (dp 0c +c Am 0)) dm0) (∸c-0l _)
      zm (suc j) = ∸c-absorb (dm (Am j)) (dp (Am j))
      zp : ∀ j → dp (pp j) ∸c (dm (pp j) +c Ap j) ≡ 0c
      zp zero    = trans (cong (_∸c (dm 0c +c Ap 0)) dp0) (∸c-0l _)
      zp (suc j) = ∸c-absorb (dp (Ap j)) (dm (Ap j))

      Pstep : ∀ j → suc j ≤ gk → not (P j) ≡ P (suc j)
      Pstep j l = trans (not-not _) (trans (cong even (∸-suc′ gk j l)) (even-suc (gk ∸ suc j)))

      if-same′ : ∀ b → (if b then 0c else 0c) ≡ 0c {N}
      if-same′ true  = refl
      if-same′ false = refl

    claim : ∀ j → j ≤ gk → A′.entK (k * 3 + 1) j ≡ (F (P j) (pm j) (Am j) , G (P j) (pp j) (Ap j))
    claim zero    l = cong₂ _,_ u u
      where
      u : unit (k * 3 + 1) ≡ cyl gdeg (if P 0 then 0c else 0c) (unit k) (if P 0 then 0c else 0c)
      u = trans (sym (cyl-unit-mid gdeg k kN)) (cong₂ (λ p q → cyl gdeg p (unit k) q) (sym (if-same′ (P 0))) (sym (if-same′ (P 0))))
    claim (suc j) l =
      let l′ = ≤-trans (≤-suc (≤-refl j)) l
          (cm′ , cp′) = conc j l′ in
      trans (cong A′.step (claim j l′))
            (cong₂ _,_
              (trans (stepF (P j) (pm j) (Am j) (ev j (Am j) l′ cm′) (od j (Am j) l′ cm′) (zm j))
                     (cong (λ e → F e (Am j) (Am (suc j))) (Pstep j l)))
              (trans (stepG (P j) (pp j) (Ap j) (ev j (Ap j) l′ cp′) (od j (Ap j) l′ cp′) (zp j))
                     (cong (λ e → G e (Ap j) (Ap (suc j))) (Pstep j l))))

    top : A′.entK (k * 3 + 1) (suc gk) ≡ (F true (Am gk) (Am (suc gk)) , G true (Ap gk) (Ap (suc gk)))
    top =
      let (cm′ , cp′) = conc gk (≤-refl gk)
          P0 : P gk ≡ false
          P0 = cong (λ x → not (even x)) (∸-self gk)
      in trans (cong A′.step (claim gk (≤-refl gk)))
           (cong₂ _,_
             (trans (stepF (P gk) (pm gk) (Am gk) (ev gk (Am gk) (≤-refl gk) cm′) (od gk (Am gk) (≤-refl gk) cm′) (zm gk))
                    (cong (λ e → F (not e) (Am gk) (Am (suc gk))) P0))
             (trans (stepG (P gk) (pp gk) (Ap gk) (ev gk (Ap gk) (≤-refl gk) cp′) (od gk (Ap gk) (≤-refl gk) cp′) (zp gk))
                    (cong (λ e → G (not e) (Ap gk) (Ap (suc gk))) P0)))
      where
      ∸-self : ∀ m → m ∸ m ≡ 0
      ∸-self zero    = refl
      ∸-self (suc m) = ∸-self m

  ----------------------------------------------------------------------
  -- Unitality, and the hypotheses of `Generation` for the cylinder.

  private
    slot-0 : ∀ b (x y : Nat) → slot b 0 x y x ≡ x
    slot-0 true  x y = refl
    slot-0 false x y = refl
    slot-1 : ∀ b (x y z : Nat) → slot b 1 x y z ≡ y
    slot-1 true  x y z = refl
    slot-1 false x y z = refl
    slot-2 : ∀ b (x y : Nat) → slot b 2 x y x ≡ x
    slot-2 true  x y = refl
    slot-2 false x y = refl

    deg′ : ∀ k r → k < N → r < 3 → A′.deg (k * 3 + r) ≡ slot (even (g k)) r (g k) (suc (g k)) (g k)
    deg′ k r kN rl = trans (at-cylA 0 gdeg gdeg (mapV suc gdeg) gdeg k r kN rl)
                           (cong (λ y → slot (even (g k)) r (g k) y (g k)) (at-map-lt suc 0 0 gdeg k kN))

    E-not : ∀ b (u : Vec Nat N) → (if b then u else 0c) ≡ (if not b then 0c else u)
    E-not true  u = refl
    E-not false u = refl

    O-not : ∀ b (u : Vec Nat N) → (if not b then u else 0c) ≡ (if b then 0c else u)
    O-not true  u = refl
    O-not false u = refl

    U : ∀ n → Set
    U n = (augm gdeg′ (fst (A′.ent n 0)) ≡ 1) × (augm gdeg′ (snd (A′.ent n 0)) ≡ 1)

    via : ∀ n D → A′.deg n ≡ D →
          (augm gdeg′ (fst (A′.entK n D)) ≡ 1) × (augm gdeg′ (snd (A′.entK n D)) ≡ 1) → U n
    via n D e h rewrite e = h

    end : ∀ b n k → k < N → A′.deg n ≡ g k → unit n ≡ Hc b (unit k) → U n
    end b n k kN e u =
      via n (g k) e
        (trans (cong (augm gdeg′) (cong fst (entK-end b n k u (g k)))) (trans (augm-H b _) (fst (Hyp.unital H k kN))) ,
         trans (cong (augm gdeg′) (cong snd (entK-end b n k u (g k)))) (trans (augm-H b _) (snd (Hyp.unital H k kN))))

  unital′ : ∀ n → n < N * 3 → U n
  unital′ n nN with divmod n
  ... | (k , r , rl , refl) with ≤-dec N k
  ...   | inj₁ Nk = ⊥-elim (≤-<-⊥ (≤-trans (*3-mono′ Nk) (≤r′ (k * 3) r)) nN)
  ...   | inj₂ kN = go r rl
    where
    go : ∀ r → r < 3 → U (k * 3 + r)
    go zero l =
      end (even (g k)) (k * 3 + 0) k kN (trans (deg′ k 0 kN l) (slot-0 (even (g k)) (g k) (suc (g k))))
          (trans (cong unit (+-zero (k * 3))) (trans (sym (cyl-unit-lo gdeg k kN))
                 (cong (λ q → cyl gdeg (E k) 0c q) (O-not (even (g k)) (unit k)))))
    go (suc zero) l =
      via (k * 3 + 1) (suc (g k)) (trans (deg′ k 1 kN l) (slot-1 (even (g k)) (g k) (suc (g k)) (g k)))
        (trans (cong (augm gdeg′) (cong fst (Mid.top k kN)))
           (trans (augm-cyl gdeg gdeg (mapV suc gdeg) gdeg _ _ _)
             (trans (cong₂ (λ p q → (augm gdeg (fst (A.entK k (g k))) + p) + q) (augm-suc gdeg _) (augm-0 gdeg))
               (trans (trans (+-zero _) (+-zero _)) (fst (Hyp.unital H k kN))))) ,
         trans (cong (augm gdeg′) (cong snd (Mid.top k kN)))
           (trans (augm-cyl gdeg gdeg (mapV suc gdeg) gdeg _ _ _)
             (trans (cong₂ (λ p q → (p + q) + augm gdeg (snd (A.entK k (g k)))) (augm-0 gdeg) (augm-suc gdeg _))
                    (snd (Hyp.unital H k kN)))))
    go (suc (suc zero)) l =
      end (not (even (g k))) (k * 3 + 2) k kN (trans (deg′ k 2 kN l) (slot-2 (even (g k)) (g k) (suc (g k))))
          (trans (sym (cyl-unit-hi gdeg k kN)) (cong (λ q → cyl gdeg (O k) 0c q) (E-not (even (g k)) (unit k))))
    go (suc (suc (suc r))) (s≤s (s≤s (s≤s ())))

  Hyp′ : Hyp B′
  Hyp′ = record
    { dd = dd′ ; deg-dp = deg-dp′ ; deg-dm = deg-dm′
    ; ordm = ordm′ ; ordp = ordp′ ; aug1 = aug1′ ; unital = unital′ }

------------------------------------------------------------------------
-- Examples: the square λD¹ ⊗ λD¹ and the cylinder on the 2-globe.

module Square = CylDD BD¹ hyp-D¹ refl refl

-- The decision procedures of BasisCheck agree on the same basis.
square-check : Hyp (Cyl.B′ BD¹)
square-check = mkHyp (Cyl.B′ BD¹) refl refl refl tt tt refl tt

gen-square : ∀ x → IsCell (adc (Cyl.B′ BD¹)) 2 x → Gen.Gen (Cyl.B′ BD¹) Square.Hyp′ 2 x
gen-square = Gen.generation (Cyl.B′ BD¹) Square.Hyp′ 2

module CylD² = CylDD BD² hyp-D² refl refl

cylD²-check : Hyp (Cyl.B′ BD²)
cylD²-check = mkHyp (Cyl.B′ BD²) refl refl refl tt tt refl tt
