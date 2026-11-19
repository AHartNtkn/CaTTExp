------------------------------------------------------------------------
-- ν(λΓ) ≅ Free(Γ) for every pasting context Γ (ledger A5, (N3)).
--
-- `treeG T` (GlobBasis) lays out the generators of a Batanin tree T as
-- the wedge of the suspensions of its branches. `labT T i` is the
-- label of the i-th generator in that layout: for T = node x₀ [(T₁,
-- x₁), …] it reads x₀, the labels of T₁, x₁, the labels of T₂, …
--
-- For a well-typed tree (`FreeTV.TV`), and so for tr Γ when Γ is a
-- pasting context:
--   * the labelling respects the globular structure (`glT`): the i-th
--     generator is a variable of dimension deg i, and if deg i ≥ 1 its
--     type runs from the label of s i to the label of t i;
--   * it is a bijection from the generators onto the labels of T
--     (`memT`, `surjT`, `injT`), which for tr Γ are the variables of Γ
--     (`TrFlat.flat-tr`).
-- So (`Interp`, `PastingCtx`) a strict functor ν(λ(tr Γ)) → 𝒟 is the
-- same as a good labelling of Γ in 𝒟 (`Good`, the hypothesis of
-- `OmegaFree`: each variable goes to a cell of the dimension and with
-- the boundary its type prescribes): `FromGood.functor` extends a good
-- labelling, `FO.unique` makes the extension unique, and when L bounds
-- the dimensions of the variables (`dims`), `Restrict.OfFunctor.good`
-- restricts a functor to a good labelling, with `restrict-build` and
-- `build-restrict` the two round trips.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Strict.PsGlob (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; ≤-refl; ≤-trans; ≤-suc; ≤-<-⊥; <→≤; <-irrefl)
open import CaTTExp.Strict.Trees
open import CaTTExp.Strict.GlobBasis
open import CaTTExp.Strict.Generation using (≤-dec)
open import CaTTExp.Strict.Bag using (+-comm; +-zero; +-suc)
open import CaTTExp.Strict.PsFacts 𝕊 using (ArrOrd)
open import CaTTExp.Strict.FreeTV 𝕊 using (TV; TVB; Later; step<; sep; sep-y; lab-ext; no-P) renaming (labB to laterB)
open import CaTTExp.Strict.LabelSets using (_∈_; ∈-hd; ∈-tl; ∈-∷⁻; ∈-++ˡ; ∈-++ʳ; ∈-++⁻; inj₁; inj₂) renaming (_⊎_ to _⊎ˡ_)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)
open import CaTTExp.Strict.Omega using (ωCat)
open import CaTTExp.Strict.Expr using (Functor)
open import CaTTExp.Strict.FreeADC using (adc)
open import CaTTExp.Strict.Nu using (nu; ≡-cell)
open import CaTTExp.Strict.Generation using (module Gen)
open import CaTTExp.Strict.NuRows using (module Rows)
open import CaTTExp.Strict.GenericEnv 𝕊 using (vn)
open import CaTTExp.Strict.PsFacts 𝕊 using (ps-facts; ord; lookup-<; ==→≡)
open import CaTTExp.Pasting 𝕊 using (_⊢ps_∶_)
open import CaTTExp.Strict.PsTree 𝕊 using (tr)
open import CaTTExp.Strict.TrFlat 𝕊 using (tv-tr; flat-tr; upTo)
import CaTTExp.Strict.OmegaFree as OF

private
  <ℕ-complete′ : ∀ m n → m < n → (m <ℕ n) ≡ true
  <ℕ-complete′ zero    (suc n) _       = refl
  <ℕ-complete′ (suc m) (suc n) (s≤s l) = <ℕ-complete′ m n l

  <ℕ-irr′ : ∀ n → (n <ℕ n) ≡ false
  <ℕ-irr′ zero    = refl
  <ℕ-irr′ (suc n) = <ℕ-irr′ n

  +∸′ : ∀ j M → (j + M) ∸ M ≡ j
  +∸′ j zero    = +-zero j
  +∸′ j (suc M) = trans (cong (_∸ suc M) (+-suc j M)) (+∸′ j M)

  lt-right′ : ∀ j M → 1 ≤ j → (j + M <ℕ suc M) ≡ false
  lt-right′ (suc j) zero    _ = refl
  lt-right′ (suc j) (suc M) p = trans (cong (_<ℕ suc (suc M)) (+-suc (suc j) M)) (lt-right′ (suc j) M p)

  lt-left′ : ∀ i M → i ≤ M → (i <ℕ suc M) ≡ true
  lt-left′ zero    M       _       = refl
  lt-left′ (suc i) (suc M) (s≤s l) = lt-left′ i M l

  -- i ≤ M, or i = j + M with j ≥ 1.
  split′ : ∀ i M → (i ≤ M) ⊎ Σ Nat (λ j → (1 ≤ j) × (i ≡ j + M))
  split′ i M with ≤-dec i M
  ... | inj₁ p = inj₁ p
  ... | inj₂ p = inj₂ (i ∸ M , pos i M p , sym (∸+ i M p))
    where
    pos : ∀ i M → M < i → 1 ≤ i ∸ M
    pos (suc i) zero    _       = s≤s z≤n
    pos (suc i) (suc M) (s≤s l) = pos i M l
    ∸+ : ∀ i M → M < i → (i ∸ M) + M ≡ i
    ∸+ i       zero    _       = +-zero i
    ∸+ (suc i) (suc M) (s≤s l) = trans (+-suc (i ∸ M) M) (cong suc (∸+ i M l))

------------------------------------------------------------------------
-- Labels of the generators.

module _ {A : Set} where

  NT : LT A → Nat
  NT T = GData.N (treeG T)

  -- The suspension of T between x and y: x, the labels of T, y.
  labΣ : A → (Nat → A) → A → Nat → Nat → A
  labΣ x f y n zero    = x
  labΣ x f y n (suc k) = if k <ℕ n then f k else y

  mutual
    labT : LT A → Nat → A
    labT (node x r) = labB x r

    labB : A → Br A → Nat → A
    labB x nil          i = x
    labB x (cons T y r) i =
      if i <ℕ suc (suc (NT T)) then labΣ x (labT T) y (NT T) i else labB y r (i ∸ suc (NT T))

  -- The wedge in `branchP (cons T y r)`.
  module WB (T : LT A) (r : Br A) where
    open Wedge (Pointed.G (ΣP (treeG T))) (Pointed.G (branchP r)) (Pointed.M (ΣP (treeG T))) (Pointed.M (branchP r))
               (Pointed.eN (ΣP (treeG T))) (Pointed.eN (branchP r)) (Pointed.last0 (ΣP (treeG T))) (Pointed.first0 (branchP r))
      public

  lab0 : ∀ x r → labB x r 0 ≡ x
  lab0 x nil          = refl
  lab0 x (cons T y r) = refl

  labL : ∀ x T y r i → i ≤ suc (NT T) → labB x (cons T y r) i ≡ labΣ x (labT T) y (NT T) i
  labL x T y r i l rewrite lt-left′ i (suc (NT T)) l = refl

  labΣ-in : ∀ x f y n k → k < n → labΣ x f y n (suc k) ≡ f k
  labΣ-in x f y n k l rewrite <ℕ-complete′ k n l = refl

  labΣ-top : ∀ x f y n → labΣ x f y n (suc n) ≡ y
  labΣ-top x f y n rewrite <ℕ-irr′ n = refl

  labR : ∀ x T y r j → labB x (cons T y r) (j + suc (NT T)) ≡ labB y r j
  labR x T y r zero    = trans (labL x T y r (suc (NT T)) (≤-refl _)) (trans (labΣ-top x (labT T) y (NT T)) (sym (lab0 y r)))
  labR x T y r (suc j) rewrite lt-right′ (suc j) (suc (NT T)) (s≤s z≤n) = cong (labB y r) (+∸′ (suc j) (suc (NT T)))

private
  ≤-+ : ∀ a b → a ≤ a + b
  ≤-+ zero    b = z≤n
  ≤-+ (suc a) b = s≤s (≤-+ a b)

  bound-r : ∀ j M M′ → j < suc M′ → j + M < suc (M + M′)
  bound-r j zero    M′ l = subst (_< suc M′) (sym (+-zero j)) l
  bound-r j (suc M) M′ l = subst (_< suc (suc (M + M′))) (sym (+-suc j M)) (s≤s (bound-r j M M′ l))

  br′ : ∀ j M M′ → j + M < suc (M + M′) → j < suc M′
  br′ j zero    M′ l = subst (_< suc M′) (+-zero j) l
  br′ j (suc M) M′ l = br′ j M M′ (pred′ (subst (_< suc (suc (M + M′))) (+-suc j M) l))
    where
    pred′ : ∀ {a b} → suc a < suc b → a < b
    pred′ (s≤s p) = p

  ≤-antisym′ : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
  ≤-antisym′ z≤n     z≤n     = refl
  ≤-antisym′ (s≤s p) (s≤s q) = cong suc (≤-antisym′ p q)

------------------------------------------------------------------------
-- The generators of a branch cons T y r: x = 0, those of T, y, and
-- those of r after its first.

module _ {A : Set} where

  NB MB : Br A → Nat
  NB r = GData.N (Pointed.G (branchP r))
  MB r = Pointed.M (branchP r)

  0<NB : ∀ r → 0 < NB r
  0<NB r = subst (0 <_) (sym (Pointed.eN (branchP r))) (s≤s z≤n)

  data View (T : LT A) (r : Br A) : Nat → Set where
    v-x : View T r 0
    v-T : ∀ k → k < NT T → View T r (suc k)
    v-y : View T r (suc (NT T))
    v-r : ∀ j → 1 ≤ j → j < NB r → View T r (j + suc (NT T))

  private
    low : ∀ T r k → k ≤ NT T → (NT T ≤ k) ⊎ (k < NT T) → View T r (suc k)
    low T r k q (inj₁ p) = subst (λ m → View T r (suc m)) (≤-antisym′ p q) v-y
    low T r k q (inj₂ p) = v-T k p

  view : ∀ T r i → i < suc (suc (NT T) + MB r) → View T r i
  view T r i l with split′ i (suc (NT T))
  ... | inj₁ z≤n     = v-x
  ... | inj₁ (s≤s q) = low T r _ q (≤-dec (NT T) _)
  ... | inj₂ (j , q , refl) = v-r j q (subst (j <_) (sym (Pointed.eN (branchP r))) (br′ j (suc (NT T)) (MB r) l))

  lab-T : ∀ (x : A) T (y : A) r k → k < NT T → labB x (cons T y r) (suc k) ≡ labT T k
  lab-T x T y r k l = trans (labL x T y r (suc k) (s≤s (≤-trans (≤-suc (≤-refl k)) l))) (labΣ-in x (labT T) y (NT T) k l)

  lab-y : ∀ (x : A) T (y : A) r → labB x (cons T y r) (suc (NT T)) ≡ y
  lab-y x T y r = trans (labL x T y r (suc (NT T)) (≤-refl _)) (labΣ-top x (labT T) y (NT T))

------------------------------------------------------------------------
-- Every generator is labelled by a label of the tree, and every label
-- labels a generator.

mutual
  memT : ∀ (T : LT Nat) i → i < NT T → labT T i ∈ flat T
  memT (node x r) i l = memB x r i l

  memB : ∀ (x : Nat) (r : Br Nat) i → i < NB r → labB x r i ∈ (x ∷ flatB r)
  memB x nil          zero    _       = ∈-hd x []
  memB x nil          (suc i) (s≤s ())
  memB x (cons T y r) i       l       = memV x T y r i (view T r i l)

  memV : ∀ (x : Nat) (T : LT Nat) (y : Nat) (r : Br Nat) i → View T r i → labB x (cons T y r) i ∈ (x ∷ y ∷ (flat T ++ flatB r))
  memV x T y r _ v-x         = ∈-hd x (y ∷ (flat T ++ flatB r))
  memV x T y r _ (v-T k l)   =
    subst (_∈ (x ∷ y ∷ (flat T ++ flatB r))) (sym (lab-T x T y r k l))
      (∈-tl (labT T k) x (y ∷ (flat T ++ flatB r)) (∈-tl (labT T k) y (flat T ++ flatB r) (∈-++ˡ (labT T k) (flat T) (flatB r) (memT T k l))))
  memV x T y r _ v-y         =
    subst (_∈ (x ∷ y ∷ (flat T ++ flatB r))) (sym (lab-y x T y r)) (∈-tl y x (y ∷ (flat T ++ flatB r)) (∈-hd y (flat T ++ flatB r)))
  memV x T y r _ (v-r j q l) =
    subst (_∈ (x ∷ y ∷ (flat T ++ flatB r))) (sym (labR x T y r j)) (memR x T y r j (∈-∷⁻ (labB y r j) y (flatB r) (memB y r j l)))

  memR : ∀ (x : Nat) (T : LT Nat) (y : Nat) (r : Br Nat) j → (labB y r j ≡ y) ⊎ˡ (labB y r j ∈ flatB r) →
         labB y r j ∈ (x ∷ y ∷ (flat T ++ flatB r))
  memR x T y r j (inj₁ e) =
    subst (_∈ (x ∷ y ∷ (flat T ++ flatB r))) (sym e) (∈-tl y x (y ∷ (flat T ++ flatB r)) (∈-hd y (flat T ++ flatB r)))
  memR x T y r j (inj₂ m) =
    ∈-tl (labB y r j) x (y ∷ (flat T ++ flatB r)) (∈-tl (labB y r j) y (flat T ++ flatB r) (∈-++ʳ (labB y r j) (flat T) (flatB r) m))

mutual
  surjT : ∀ (T : LT Nat) v → v ∈ flat T → Σ Nat (λ i → (i < NT T) × (labT T i ≡ v))
  surjT (node x r) v m = surjB x r v (∈-∷⁻ v x (flatB r) m)

  surjB : ∀ (x : Nat) (r : Br Nat) v → (v ≡ x) ⊎ˡ (v ∈ flatB r) → Σ Nat (λ i → (i < NB r) × (labB x r i ≡ v))
  surjB x r v (inj₁ e) = 0 , 0<NB r , trans (lab0 x r) (sym e)
  surjB x r v (inj₂ m) = surjB′ x r v m

  surjB′ : ∀ (x : Nat) (r : Br Nat) v → v ∈ flatB r → Σ Nat (λ i → (i < NB r) × (labB x r i ≡ v))
  surjB′ x nil          v ()
  surjB′ x (cons T y r) v m = surjC x T y r v (∈-∷⁻ v y (flat T ++ flatB r) m)

  surjC : ∀ (x : Nat) (T : LT Nat) (y : Nat) (r : Br Nat) v → (v ≡ y) ⊎ˡ (v ∈ (flat T ++ flatB r)) →
          Σ Nat (λ i → (i < suc (suc (NT T) + MB r)) × (labB x (cons T y r) i ≡ v))
  surjC x T y r v (inj₁ e) = suc (NT T) , s≤s (s≤s (≤-+ (NT T) (MB r))) , trans (lab-y x T y r) (sym e)
  surjC x T y r v (inj₂ m) = surjD x T y r v (∈-++⁻ v (flat T) (flatB r) m)

  surjD : ∀ (x : Nat) (T : LT Nat) (y : Nat) (r : Br Nat) v → (v ∈ flat T) ⊎ˡ (v ∈ flatB r) →
          Σ Nat (λ i → (i < suc (suc (NT T) + MB r)) × (labB x (cons T y r) i ≡ v))
  surjD x T y r v (inj₁ mT) = surjE x T y r v (surjT T v mT)
  surjD x T y r v (inj₂ mr) = surjF x T y r v (surjB′ y r v mr)

  surjE : ∀ (x : Nat) (T : LT Nat) (y : Nat) (r : Br Nat) v → Σ Nat (λ k → (k < NT T) × (labT T k ≡ v)) →
          Σ Nat (λ i → (i < suc (suc (NT T) + MB r)) × (labB x (cons T y r) i ≡ v))
  surjE x T y r v (k , l , e) = suc k , s≤s (s≤s (≤-trans (<→≤ l) (≤-+ (NT T) (MB r)))) , trans (lab-T x T y r k l) e

  surjF : ∀ (x : Nat) (T : LT Nat) (y : Nat) (r : Br Nat) v → Σ Nat (λ j → (j < NB r) × (labB y r j ≡ v)) →
          Σ Nat (λ i → (i < suc (suc (NT T) + MB r)) × (labB x (cons T y r) i ≡ v))
  surjF x T y r v (j , l , e) =
    j + suc (NT T) , bound-r j (suc (NT T)) (MB r) (subst (j <_) (Pointed.eN (branchP r)) l) , trans (labR x T y r j) e

------------------------------------------------------------------------
-- Well-typed trees: the labelling is globular.

-- How the type A of the i-th label sits over the spine type P.
Bd : Ty → Nat → Ty → Nat → Nat → Set
Bd P zero    A sv tv = A ≡ P
Bd P (suc g) A sv tv = Σ Ty (λ A′ → A ≡ arr A′ (var sv) (var tv))

module Typed (Θ : Ctx) (ord : ArrOrd Θ) where

  GI : Ty → GData → (Nat → Nat) → Nat → Set
  GI P D lab i = Σ Ty (λ A → (lookup Θ (lab i) ≡ just A) × ((dim A ≡ dim P + GData.gd D i) ×
                 Bd P (GData.gd D i) A (lab (GData.s D i)) (lab (GData.t D i))))

  private
    Bd-tr : ∀ P g A {a a′ b b′} → a ≡ a′ → b ≡ b′ → Bd P g A a b → Bd P g A a′ b′
    Bd-tr P zero    A refl refl h = h
    Bd-tr P (suc g) A refl refl h = h

    -- Transport of GI along the wedge's description of gd, s, t, lab.
    GI-tr : ∀ P D D′ lab lab′ i i′ → GData.gd D i ≡ GData.gd D′ i′ →
            lab i ≡ lab′ i′ → lab (GData.s D i) ≡ lab′ (GData.s D′ i′) → lab (GData.t D i) ≡ lab′ (GData.t D′ i′) →
            GI P D′ lab′ i′ → GI P D lab i
    GI-tr P D D′ lab lab′ i i′ eg el es et (A , lA , dA , bA) =
      A , trans (cong (lookup Θ) el) lA , trans dA (cong (dim P +_) (sym eg)) ,
      subst (λ g → Bd P g A (lab (GData.s D i)) (lab (GData.t D i))) (sym eg) (Bd-tr P (GData.gd D′ i′) A (sym es) (sym et) bA)

  GI-0 : ∀ P D lab i → GData.gd D i ≡ 0 → lookup Θ (lab i) ≡ just P → GI P D lab i
  GI-0 P D lab i e l =
    P , l , trans (sym (+-zero (dim P))) (cong (dim P +_) (sym e)) ,
    subst (λ g → Bd P g P (lab (GData.s D i)) (lab (GData.t D i))) (sym e) refl

  -- Changing the labelling on the generators.
  GI-ext : ∀ P D lab lab′ i → i < GData.N D → (∀ j → j < GData.N D → lab j ≡ lab′ j) → GI P D lab′ i → GI P D lab i
  GI-ext P D lab lab′ i iN h (A , lA , dA , bA) =
    A , trans (cong (lookup Θ) (h i iN)) lA , dA , bd (GData.gd D i) refl bA
    where
    bd : ∀ g → GData.gd D i ≡ g → Bd P g A (lab′ (GData.s D i)) (lab′ (GData.t D i)) → Bd P g A (lab (GData.s D i)) (lab (GData.t D i))
    bd zero    e b = b
    bd (suc g) e b =
      Bd-tr P (suc g) A (sym (h (GData.s D i) (GData.sN D i iN p))) (sym (h (GData.t D i) (GData.tN D i iN p))) b
      where
      p : 1 ≤ GData.gd D i
      p = subst (1 ≤_) (sym e) (s≤s z≤n)

  -- The suspension of D between x and y.
  GIΣ : ∀ P D (f : Nat → Nat) x y → lookup Θ x ≡ just P → lookup Θ y ≡ just P →
        (∀ k → k < GData.N D → GI (arr P (var x) (var y)) D f k) →
        ∀ i → i < suc (suc (GData.N D)) → GI P (Σg D) (labΣ x f y (GData.N D)) i
  GIΣ P D f x y lx ly h zero    _ = GI-0 P (Σg D) (labΣ x f y (GData.N D)) 0 refl lx
  GIΣ P D f x y lx ly h (suc k) l with ≤-dec (GData.N D) k
  ... | inj₁ Nk =
    GI-0 P (Σg D) (labΣ x f y N) (suc k) (cong (λ b → if b then suc (GData.gd D k) else 0) e)
         (trans (cong (λ b → lookup Θ (if b then f k else y)) e) ly)
    where
    N = GData.N D
    <ℕ-false : ∀ k N → N ≤ k → (k <ℕ N) ≡ false
    <ℕ-false k       zero    _       = refl
    <ℕ-false (suc k) (suc N) (s≤s l) = <ℕ-false k N l
    e = <ℕ-false k N Nk
  ... | inj₂ kN with h k kN
  ...   | (A , lA , dA , bA) =
    A , trans (cong (lookup Θ) (labΣ-in x f y N k kN)) lA ,
    trans dA (trans (sym (+-suc (dim P) (GData.gd D k))) (cong (dim P +_) (sym eg))) ,
    subst (λ g → Bd P g A (labΣ x f y N (GData.s (Σg D) (suc k))) (labΣ x f y N (GData.t (Σg D) (suc k)))) (sym eg)
          (bdΣ (GData.gd D k) refl bA)
    where
    N = GData.N D
    eg : GData.gd (Σg D) (suc k) ≡ suc (GData.gd D k)
    eg = cong (λ b → if b then suc (GData.gd D k) else 0) (<ℕ-complete′ k N kN)
    bdΣ : ∀ g → GData.gd D k ≡ g → Bd (arr P (var x) (var y)) g A (f (GData.s D k)) (f (GData.t D k)) →
          Σ Ty (λ A′ → A ≡ arr A′ (var (labΣ x f y N (if g ==ℕ 0 then 0 else suc (GData.s D k))))
                                  (var (labΣ x f y N (if g ==ℕ 0 then suc N else suc (GData.t D k)))))
    bdΣ zero    e b = P , trans b (cong (λ v → arr P (var x) (var v)) (sym (labΣ-top x f y N)))
    bdΣ (suc g) e (A′ , b) =
      A′ , trans b (cong₂ (λ u v → arr A′ (var u) (var v))
                          (sym (labΣ-in x f y N (GData.s D k) (GData.sN D k kN p)))
                          (sym (labΣ-in x f y N (GData.t D k) (GData.tN D k kN p))))
      where
      p : 1 ≤ GData.gd D k
      p = subst (1 ≤_) (sym e) (s≤s z≤n)

  private
    br : ∀ j M M′ → j + M < suc (M + M′) → j < suc M′
    br j zero    M′ l = subst (_< suc M′) (+-zero j) l
    br j (suc M) M′ l = br j M M′ (pred′ (subst (_< suc (suc (M + M′))) (+-suc j M) l))
      where
      pred′ : ∀ {a b} → suc a < suc b → a < b
      pred′ (s≤s p) = p

    ≤-pred′ : ∀ {a b} → suc a ≤ suc b → a ≤ b
    ≤-pred′ (s≤s p) = p

  -- The wedge of D (last object M) and D′.
  GIW : ∀ P D D′ M M′ eN eN′ l0 f0 (lab : Nat → Nat) →
        (∀ i → i ≤ M → GI P D lab i) → (∀ j → j < GData.N D′ → GI P D′ (λ j → lab (j + M)) j) →
        ∀ i → i < suc (M + M′) → GI P (Wedge.wedge D D′ M M′ eN eN′ l0 f0) lab i
  GIW P D D′ M M′ eN eN′ l0 f0 lab hl hr i l with split′ i M
  ... | inj₁ q = GI-tr P W.wedge D lab lab i i (W.gdL i q) refl (cong lab (W.sL i q)) (cong lab (W.tL i q)) (hl i q)
    where module W = Wedge D D′ M M′ eN eN′ l0 f0
  ... | inj₂ (j , q , refl) =
    GI-tr P W.wedge D′ lab (λ j → lab (j + M)) (j + M) j (W.gdR′ j q) refl (cong lab (W.sR j q)) (cong lab (W.tR j q))
      (hr j (subst (j <_) (sym eN′) (br j M M′ l)))
    where module W = Wedge D D′ M M′ eN eN′ l0 f0

  mutual
    glT : ∀ P T → TV Θ ord P T → ∀ i → i < NT T → GI P (treeG T) (labT T) i
    glT P (node x r) (lx , tb) i l = glB P x r lx tb i l

    glB : ∀ P x r → lookup Θ x ≡ just P → TVB Θ ord P x r → ∀ i → i < GData.N (Pointed.G (branchP r)) →
          GI P (Pointed.G (branchP r)) (labB x r) i
    glB P x nil          lx _ zero    _       = P , lx , sym (+-zero (dim P)) , refl
    glB P x nil          lx _ (suc i) (s≤s ())
    glB P x (cons T y r) lx (tvT , ly , tvr) =
      GIW P (Σg (treeG T)) (Pointed.G (branchP r)) (suc (NT T)) (Pointed.M (branchP r))
          (Pointed.eN (ΣP (treeG T))) (Pointed.eN (branchP r)) (Pointed.last0 (ΣP (treeG T))) (Pointed.first0 (branchP r))
          (labB x (cons T y r)) left right
      where
      left : ∀ i → i ≤ suc (NT T) → GI P (Σg (treeG T)) (labB x (cons T y r)) i
      left i q = GI-ext P (Σg (treeG T)) _ _ i (s≤s q) (λ j jl → labL x T y r j (≤-pred′ jl))
                   (GIΣ P (treeG T) (labT T) x y lx ly (glT (arr P (var x) (var y)) T tvT) i (s≤s q))
      right : ∀ j → j < GData.N (Pointed.G (branchP r)) → GI P (Pointed.G (branchP r)) (λ j → labB x (cons T y r) (j + suc (NT T))) j
      right j jl = GI-ext P (Pointed.G (branchP r)) _ _ j jl (λ j′ _ → labR x T y r j′) (glB P y r ly tvr j jl)

  ----------------------------------------------------------------------
  -- On a well-typed tree, distinct generators have distinct labels.

  private
    conv : ∀ {a b c d : Nat} → a ≡ b → c ≡ d → a ≡ c → b ≡ d
    conv p q e = trans (sym p) (trans e q)

    -- A label after the spine label y is not a spine label x ≤ y.
    not-before : ∀ P x y r v → lookup Θ x ≡ just P → x ≤ y → TVB Θ ord P y r → v ∈ flatB r → v ≡ x → ⊥
    not-before P x y r v lx xy tr m e = nb (laterB Θ ord P y r v tr m)
      where
      nb : Later Θ ord P y v → ⊥
      nb (inj₁ (_ , yv))                 = ≤-<-⊥ (subst (_≤ y) (sym e) xy) yv
      nb (inj₂ (Q , s , t , lq , ex , _)) = no-P Θ ord lx (subst (λ w → lookup Θ w ≡ just Q) e lq) ex

    -- The left spine label x of a branch is not a label of the branch.
    not-left : ∀ P x y T v → TV Θ ord (arr P (var x) (var y)) T → lookup Θ x ≡ just P → v ∈ flat T → v ≡ x → ⊥
    not-left P x y T v tT lx m refl with lab-ext Θ ord _ T v tT m
    ... | (Q , lq , ex) = no-P Θ ord lx lq ex

    dxy : ∀ P x T y → TV Θ ord (arr P (var x) (var y)) T → x ≡ y → ⊥
    dxy P x T y tT refl = <-irrefl (step< Θ ord P x T x tT)

    dxT : ∀ P x T y → lookup Θ x ≡ just P → TV Θ ord (arr P (var x) (var y)) T → ∀ k → k < NT T → x ≡ labT T k → ⊥
    dxT P x T y lx tT k l e = not-left P x y T (labT T k) tT lx (memT T k l) (sym e)

    dxr : ∀ P x T y r → lookup Θ x ≡ just P → TV Θ ord (arr P (var x) (var y)) T → TVB Θ ord P y r →
          ∀ j → j < NB r → x ≡ labB y r j → ⊥
    dxr P x T y r lx tT tr j l e = go (∈-∷⁻ (labB y r j) y (flatB r) (memB y r j l))
      where
      go : (labB y r j ≡ y) ⊎ˡ (labB y r j ∈ flatB r) → ⊥
      go (inj₁ e′) = dxy P x T y tT (trans e e′)
      go (inj₂ m)  = not-before P x y r (labB y r j) lx (<→≤ (step< Θ ord P x T y tT)) tr m (sym e)

    dTy : ∀ P x T y → lookup Θ y ≡ just P → TV Θ ord (arr P (var x) (var y)) T → ∀ k → k < NT T → labT T k ≡ y → ⊥
    dTy P x T y ly tT k l e = sep-y Θ ord P x y T (labT T k) tT ly (memT T k l) e

    dTr : ∀ P x T y r → lookup Θ y ≡ just P → TV Θ ord (arr P (var x) (var y)) T → TVB Θ ord P y r →
          ∀ k → k < NT T → ∀ j → j < NB r → labT T k ≡ labB y r j → ⊥
    dTr P x T y r ly tT tr k l j l′ e = go (∈-∷⁻ (labB y r j) y (flatB r) (memB y r j l′))
      where
      go : (labB y r j ≡ y) ⊎ˡ (labB y r j ∈ flatB r) → ⊥
      go (inj₁ e′) = dTy P x T y ly tT k l (trans e e′)
      go (inj₂ m)  = sep Θ ord P x y T r (labT T k) tT tr (memT T k l) (subst (_∈ flatB r) (sym e) m)

  mutual
    injT : ∀ P T → TV Θ ord P T → ∀ i j → i < NT T → j < NT T → labT T i ≡ labT T j → i ≡ j
    injT P (node x r) (lx , tb) = injB P x r lx tb

    injB : ∀ P x r → lookup Θ x ≡ just P → TVB Θ ord P x r → ∀ i j → i < NB r → j < NB r → labB x r i ≡ labB x r j → i ≡ j
    injB P x nil          lx tb zero    zero    _       _       _ = refl
    injB P x nil          lx tb (suc i) _       (s≤s ()) _      _
    injB P x nil          lx tb zero    (suc j) _       (s≤s ()) _
    injB P x (cons T y r) lx tb i       j       li      lj      e = injV P x T y r lx tb i j (view T r i li) (view T r j lj) e

    injV : ∀ P x T y r → lookup Θ x ≡ just P → TVB Θ ord P x (cons T y r) → ∀ i j → View T r i → View T r j →
           labB x (cons T y r) i ≡ labB x (cons T y r) j → i ≡ j
    injV P x T y r lx (tT , ly , tr) _ _ v-x v-x e = refl
    injV P x T y r lx (tT , ly , tr) _ _ v-x (v-T k l) e = ⊥-elim (dxT P x T y lx tT k l (conv refl (lab-T x T y r k l) e))
    injV P x T y r lx (tT , ly , tr) _ _ v-x v-y e = ⊥-elim (dxy P x T y tT (conv refl (lab-y x T y r) e))
    injV P x T y r lx (tT , ly , tr) _ _ v-x (v-r j q l) e = ⊥-elim (dxr P x T y r lx tT tr j l (conv refl (labR x T y r j) e))
    injV P x T y r lx (tT , ly , tr) _ _ (v-T k l) v-x e = ⊥-elim (dxT P x T y lx tT k l (sym (conv (lab-T x T y r k l) refl e)))
    injV P x T y r lx (tT , ly , tr) _ _ (v-T k l) (v-T k′ l′) e =
      cong suc (injT (arr P (var x) (var y)) T tT k k′ l l′ (conv (lab-T x T y r k l) (lab-T x T y r k′ l′) e))
    injV P x T y r lx (tT , ly , tr) _ _ (v-T k l) v-y e = ⊥-elim (dTy P x T y ly tT k l (conv (lab-T x T y r k l) (lab-y x T y r) e))
    injV P x T y r lx (tT , ly , tr) _ _ (v-T k l) (v-r j q l′) e =
      ⊥-elim (dTr P x T y r ly tT tr k l j l′ (conv (lab-T x T y r k l) (labR x T y r j) e))
    injV P x T y r lx (tT , ly , tr) _ _ v-y v-x e = ⊥-elim (dxy P x T y tT (sym (conv (lab-y x T y r) refl e)))
    injV P x T y r lx (tT , ly , tr) _ _ v-y (v-T k l) e = ⊥-elim (dTy P x T y ly tT k l (sym (conv (lab-y x T y r) (lab-T x T y r k l) e)))
    injV P x T y r lx (tT , ly , tr) _ _ v-y v-y e = refl
    injV P x T y r lx (tT , ly , tr) _ _ v-y (v-r j q l) e = ⊥-elim (dyr P y r ly tr j q l (conv (lab-y x T y r) (labR x T y r j) e))
    injV P x T y r lx (tT , ly , tr) _ _ (v-r j q l) v-x e = ⊥-elim (dxr P x T y r lx tT tr j l (sym (conv (labR x T y r j) refl e)))
    injV P x T y r lx (tT , ly , tr) _ _ (v-r j q l) (v-T k l′) e =
      ⊥-elim (dTr P x T y r ly tT tr k l′ j l (sym (conv (labR x T y r j) (lab-T x T y r k l′) e)))
    injV P x T y r lx (tT , ly , tr) _ _ (v-r j q l) v-y e = ⊥-elim (dyr P y r ly tr j q l (sym (conv (labR x T y r j) (lab-y x T y r) e)))
    injV P x T y r lx (tT , ly , tr) _ _ (v-r j q l) (v-r j′ q′ l′) e =
      cong (_+ suc (NT T)) (injB P y r ly tr j j′ l l′ (conv (labR x T y r j) (labR x T y r j′) e))

    -- y is the label of the first generator of r only.
    dyr : ∀ P y r → lookup Θ y ≡ just P → TVB Θ ord P y r → ∀ j → 1 ≤ j → j < NB r → y ≡ labB y r j → ⊥
    dyr P y r ly tr j q l e = no0 (injB P y r ly tr 0 j (0<NB r) l (trans (lab0 y r) e)) q
      where
      no0 : 0 ≡ j → 1 ≤ j → ⊥
      no0 refl ()

------------------------------------------------------------------------
-- The generator with a given label.

private
  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

  lt-or-eq : ∀ i n → i < suc n → (i < n) ⊎ (i ≡ n)
  lt-or-eq zero    zero    _       = inj₂ refl
  lt-or-eq zero    (suc n) _       = inj₁ (s≤s z≤n)
  lt-or-eq (suc i) zero    (s≤s ())
  lt-or-eq (suc i) (suc n) (s≤s l) = up (lt-or-eq i n l)
    where
    up : (i < n) ⊎ (i ≡ n) → (suc i < suc n) ⊎ (suc i ≡ suc n)
    up (inj₁ p) = inj₁ (s≤s p)
    up (inj₂ e) = inj₂ (cong suc e)

  ==-true : ∀ a → (a ==ℕ a) ≡ true
  ==-true zero    = refl
  ==-true (suc a) = ==-true a

-- The last i < n with f i = v (0 if there is none).
fd : (Nat → Nat) → Nat → Nat → Nat
fd f v zero    = 0
fd f v (suc n) = if f n ==ℕ v then n else fd f v n

fd-≤ : ∀ (f : Nat → Nat) v n → fd f v n ≤ n
fd-≤ f v zero    = z≤n
fd-≤ f v (suc n) with f n ==ℕ v
... | true  = ≤-suc (≤-refl n)
... | false = ≤-suc (fd-≤ f v n)

fd-< : ∀ (f : Nat → Nat) v n → fd f v (suc n) < suc n
fd-< f v n with f n ==ℕ v
... | true  = s≤s (≤-refl n)
... | false = s≤s (fd-≤ f v n)

fd-ok : ∀ (f : Nat → Nat) v n i → i < n → f i ≡ v → f (fd f v n) ≡ v
fd-ok f v zero    i () e
fd-ok f v (suc n) i l e with f n ==ℕ v in eq
... | true  = ==→≡ (f n) v eq
... | false = go (lt-or-eq i n l)
  where
  go : (i < n) ⊎ (i ≡ n) → f (fd f v n) ≡ v
  go (inj₁ p)    = fd-ok f v n i p e
  go (inj₂ refl) = ⊥-elim (true≢false (trans (sym (trans (cong (_==ℕ v) e) (==-true v))) eq))
    where
    true≢false : true ≡ false → ⊥
    true≢false ()

------------------------------------------------------------------------
-- Strict functors ν(λT) → 𝒟 for a well-typed tree T whose labels are
-- all the variables of Θ: they are the good labellings of Θ in 𝒟, the
-- labellings that give each variable a cell with the dimension and
-- boundary its type prescribes (`Good`, the condition of
-- `OmegaFree.Good`).

module Interp (Θ : Ctx) (ord : ArrOrd Θ) (T : LT Nat) (tv : TV Θ ord ⋆ T)
              (cover : ∀ v A → lookup Θ v ≡ just A → v ∈ flat T)
              (L : Nat) (𝒟 : ωCat) where
  open ωCat 𝒟
  open Typed Θ ord

  D : GData
  D = treeG T

  module FO = FreeOn D L
  module GN = Gen (GB.basis D) (GB.hyp D) L

  private
    N = NT T
    gd = GData.gd D
    module RN = Rows (GB.basis D) (GB.hyp D) L

  -- ν(λT), with generators `GN.atom i iN iL`.
  νT : ωCat
  νT = nu (adc (GB.basis D)) L

  private
    module ν = ωCat νT

  BdL : (Nat → C) → C → Ty → Set
  BdL λ′ c ⋆           = ⊤
  BdL λ′ c (arr B a b) = (src (dim B) c ≡ λ′ (vn a)) × (tgt (dim B) c ≡ λ′ (vn b))

  Good : (Nat → C) → Set
  Good λ′ = ∀ v A → lookup Θ v ≡ just A → (src (dim A) (λ′ v) ≡ λ′ v) × BdL λ′ (λ′ v) A

  -- `Good` is `OmegaFree.Good` (which has an extra parameter Mk it does not use).
  module _ (Mk : K → C → Set) (λ′ : Nat → C) where
    private
      bd→ : ∀ c A → OF.BdL 𝕊 𝒟 Mk λ′ c A → BdL λ′ c A
      bd→ c ⋆           p = p
      bd→ c (arr B a b) p = p

      bd← : ∀ c A → BdL λ′ c A → OF.BdL 𝕊 𝒟 Mk λ′ c A
      bd← c ⋆           p = p
      bd← c (arr B a b) p = p

    good-OF : OF.Good 𝕊 𝒟 Mk λ′ Θ → Good λ′
    good-OF g v A l = fst (g v A l) , bd→ (λ′ v) A (snd (g v A l))

    OF-good : Good λ′ → OF.Good 𝕊 𝒟 Mk λ′ Θ
    OF-good g v A l = fst (g v A l) , bd← (λ′ v) A (snd (g v A l))

  gi : ∀ i → i < N → GI ⋆ D (labT T) i
  gi = glT ⋆ T tv

  -- Generators of degree at most L, when the variables have dimension at most L.
  dims : (∀ v A → lookup Θ v ≡ just A → dim A ≤ L) → ∀ i → i < N → gd i ≤ L
  dims h i iN = go (gi i iN)
    where
    go : GI ⋆ D (labT T) i → gd i ≤ L
    go (A , lA , dA , _) = subst (_≤ L) dA (h (labT T i) A lA)

  ----------------------------------------------------------------------
  -- A good labelling extends uniquely to a strict functor.

  module FromGood (λ′ : Nat → C) (good : Good λ′) where
    κ : FO.G → C
    κ (i , _ , _) = λ′ (labT T i)

    private
      bdv : ∀ v A a b h g → lookup Θ v ≡ just A → dim A ≡ h → h ≡ suc g → Bd ⋆ h A a b →
            (src g (λ′ v) ≡ λ′ a) × (tgt g (λ′ v) ≡ λ′ b)
      bdv v _ a b _ g lA dA refl (A′ , refl) =
        subst (λ k → (src k (λ′ v) ≡ λ′ a) × (tgt k (λ′ v) ≡ λ′ b)) (suc-inj dA) (snd (good v _ lA))

      sp : ∀ h → 1 ≤ h → h ≡ suc (h ∸ 1)
      sp (suc h) _ = refl

      bdκ : ∀ i (iN : i < N) → 1 ≤ gd i →
            (src (gd i ∸ 1) (λ′ (labT T i)) ≡ λ′ (labT T (GData.s D i))) ×
            (tgt (gd i ∸ 1) (λ′ (labT T i)) ≡ λ′ (labT T (GData.t D i)))
      bdκ i iN dg = go (gi i iN)
        where
        go : GI ⋆ D (labT T) i →
             (src (gd i ∸ 1) (λ′ (labT T i)) ≡ λ′ (labT T (GData.s D i))) ×
             (tgt (gd i ∸ 1) (λ′ (labT T i)) ≡ λ′ (labT T (GData.t D i)))
        go (A , lA , dA , bA) = bdv (labT T i) A _ _ (gd i) (gd i ∸ 1) lA dA (sp (gd i) dg) bA

      up : ∀ i iN iL → 1 ≤ FO.degG (i , iN , iL) → 1 ≤ gd i
      up i iN iL dg = subst (1 ≤_) (GB.gdeg-at D i iN) dg

    dimκ : ∀ g → src (FO.degG g) (κ g) ≡ κ g
    dimκ (i , iN , iL) = go (gi i iN)
      where
      go : GI ⋆ D (labT T) i → src (FO.degG (i , iN , iL)) (λ′ (labT T i)) ≡ λ′ (labT T i)
      go (A , lA , dA , _) =
        subst (λ k → src k (λ′ (labT T i)) ≡ λ′ (labT T i)) (trans dA (sym (GB.gdeg-at D i iN))) (fst (good (labT T i) A lA))

    κs : ∀ g (dg : 1 ≤ FO.degG g) → src (FO.degG g ∸ 1) (κ g) ≡ κ (FO.sG g dg)
    κs (i , iN , iL) dg =
      subst (λ k → src (k ∸ 1) (λ′ (labT T i)) ≡ λ′ (labT T (GData.s D i))) (sym (GB.gdeg-at D i iN))
            (fst (bdκ i iN (up i iN iL dg)))

    κt : ∀ g (dg : 1 ≤ FO.degG g) → tgt (FO.degG g ∸ 1) (κ g) ≡ κ (FO.tG g dg)
    κt (i , iN , iL) dg =
      subst (λ k → tgt (k ∸ 1) (λ′ (labT T i)) ≡ λ′ (labT T (GData.t D i))) (sym (GB.gdeg-at D i iN))
            (snd (bdκ i iN (up i iN iL dg)))

    functor : Functor νT 𝒟
    functor = FO.Free.functor 𝒟 κ dimκ κs κt

    functor-gen : ∀ i iN iL → Functor.F functor (GN.atom i iN iL) ≡ λ′ (labT T i)
    functor-gen i iN iL = FO.Free.functor-gen 𝒟 κ dimκ κs κt (i , iN , iL)

  ----------------------------------------------------------------------
  -- When every generator is in ν(λT) (degrees at most L), a strict
  -- functor restricts to a good labelling, and the two constructions
  -- are inverse.

  module Restrict (lim : ∀ i → i < N → gd i ≤ L) where
    private
      M = Pointed.M (treeP T)
      eN : N ≡ suc M
      eN = Pointed.eN (treeP T)

    -- The generator labelled v.
    find : Nat → Nat
    find v = fd (labT T) v (suc M)

    findN : ∀ v → find v < N
    findN v = subst (find v <_) (sym eN) (fd-< (labT T) v M)

    findL : ∀ v → FO.degG (find v , findN v , subst (_≤ L) (sym (GB.gdeg-at D (find v) (findN v))) (lim (find v) (findN v))) ≤ L
    findL v = subst (_≤ L) (sym (GB.gdeg-at D (find v) (findN v))) (lim (find v) (findN v))

    find-lab : ∀ v → v ∈ flat T → labT T (find v) ≡ v
    find-lab v m = go (surjT T v m)
      where
      go : Σ Nat (λ i → (i < NT T) × (labT T i ≡ v)) → labT T (find v) ≡ v
      go (i , l , e) = fd-ok (labT T) v (suc M) i (subst (i <_) eN l) e

    find-inj : ∀ i → i < N → find (labT T i) ≡ i
    find-inj i l = injT ⋆ T tv (find (labT T i)) i (findN (labT T i)) l (find-lab (labT T i) (memT T i l))

    private
      atom-irr : ∀ {i i′} → i ≡ i′ → ∀ p q p′ q′ → GN.atom i p q ≡ GN.atom i′ p′ q′
      atom-irr refl p q p′ q′ = ≡-cell (adc (GB.basis D)) L refl

    module OfFunctor (Φ : Functor νT 𝒟) where
      open Functor Φ

      λΦ : Nat → C
      λΦ v = F (GN.atom (find v) (findN v) (findL v))

      λΦ-lab : ∀ i iN iL → λΦ (labT T i) ≡ F (GN.atom i iN iL)
      λΦ-lab i iN iL = cong F (atom-irr (find-inj i iN) (findN (labT T i)) (findL (labT T i)) iN iL)

      private
        bdh : ∀ i iN iL (A : Ty) h → gd i ≡ h → dim A ≡ h → Bd ⋆ h A (labT T (GData.s D i)) (labT T (GData.t D i)) →
              BdL λΦ (F (GN.atom i iN iL)) A
        bdh i iN iL A zero e dA bA = subst (BdL λΦ (F (GN.atom i iN iL))) (sym bA) tt
        bdh i iN iL _ (suc g) e dA (A′ , refl) =
          trans (sym (F-src (dim A′) (GN.atom i iN iL)))
            (trans (cong (λ k → F (ν.src k (GN.atom i iN iL))) dg′)
              (trans (cong F (FO.atom-src i iN iL dg)) (sym (λΦ-lab (GData.s D i) (fst (snd (FO.sG (i , iN , iL) dg))) (snd (snd (FO.sG (i , iN , iL) dg))))))) ,
          trans (sym (F-tgt (dim A′) (GN.atom i iN iL)))
            (trans (cong (λ k → F (ν.tgt k (GN.atom i iN iL))) dg′)
              (trans (cong F (FO.atom-tgt i iN iL dg)) (sym (λΦ-lab (GData.t D i) (fst (snd (FO.tG (i , iN , iL) dg))) (snd (snd (FO.tG (i , iN , iL) dg)))))))
          where
          ed : FO.degG (i , iN , iL) ≡ suc g
          ed = trans (GB.gdeg-at D i iN) e
          dg : 1 ≤ FO.degG (i , iN , iL)
          dg = subst (1 ≤_) (sym ed) (s≤s z≤n)
          dg′ : dim A′ ≡ FO.degG (i , iN , iL) ∸ 1
          dg′ = trans (suc-inj dA) (cong (_∸ 1) (sym ed))

        goodAt : ∀ v A → lookup Θ v ≡ just A → labT T (find v) ≡ v → GI ⋆ D (labT T) (find v) →
                 (src (dim A) (λΦ v) ≡ λΦ v) × BdL λΦ (λΦ v) A
        goodAt v A lv fl (A* , lA* , dA* , bA*) =
          subst (λ B → (src (dim B) (λΦ v) ≡ λΦ v) × BdL λΦ (λΦ v) B) eqA
            (subst (λ k → src k (λΦ v) ≡ λΦ v) (trans (GB.gdeg-at D i iN) (sym dA*))
                   (trans (sym (F-src (FO.degG (i , iN , iL)) (GN.atom i iN iL))) (cong F (RN.dim-atom i iN iL))) ,
             bdh i iN iL A* (gd i) refl dA* bA*)
          where
          i = find v
          iN = findN v
          iL = findL v
          just-inj : ∀ {a b : Ty} → just a ≡ just b → a ≡ b
          just-inj refl = refl
          eqA : A* ≡ A
          eqA = just-inj (trans (sym lA*) (subst (λ w → lookup Θ w ≡ just A) (sym fl) lv))

      good : Good λΦ
      good v A lv = goodAt v A lv (find-lab v (cover v A lv)) (gi (find v) (findN v))

    -- good labelling → functor → good labelling: the same on the variables.
    restrict-build : ∀ λ′ (g : Good λ′) v A → lookup Θ v ≡ just A → OfFunctor.λΦ (FromGood.functor λ′ g) v ≡ λ′ v
    restrict-build λ′ g v A lv =
      trans (FromGood.functor-gen λ′ g (find v) (findN v) (findL v)) (cong λ′ (find-lab v (cover v A lv)))

    -- functor → good labelling → functor: the same functor.
    build-restrict : ∀ Φ x → Functor.F (FromGood.functor (OfFunctor.λΦ Φ) (OfFunctor.good Φ)) x ≡ Functor.F Φ x
    build-restrict Φ = FO.unique (FromGood.functor (OfFunctor.λΦ Φ) (OfFunctor.good Φ)) Φ h
      where
      h : ∀ g → Functor.F (FromGood.functor (OfFunctor.λΦ Φ) (OfFunctor.good Φ)) (GN.atom (fst g) (fst (snd g)) (snd (snd g))) ≡
                Functor.F Φ (GN.atom (fst g) (fst (snd g)) (snd (snd g)))
      h (i , iN , iL) = trans (FromGood.functor-gen (OfFunctor.λΦ Φ) (OfFunctor.good Φ) i iN iL) (OfFunctor.λΦ-lab Φ i iN iL)

------------------------------------------------------------------------
-- Pasting contexts: the labels of tr Γ are the variables of Γ, so
-- strict functors ν(λ(tr Γ)) → 𝒟 are the good labellings of Γ, that
-- is the interpretations of Γ in 𝒟.

upTo-∈ : ∀ n v → T (v <ℕ n) → v ∈ upTo n
upTo-∈ (suc n) v t with v <ℕ n in e
... | true  = ∈-++ˡ v (upTo n) (n ∷ []) (upTo-∈ n v (subst T (sym e) tt))
... | false = ∈-++ʳ v (upTo n) (n ∷ []) (subst (λ w → v ∈ (w ∷ [])) (eq v n t e) (∈-hd v []))
  where
  eq : ∀ v n → T (v <ℕ suc n) → (v <ℕ n) ≡ false → v ≡ n
  eq zero    zero    _ _ = refl
  eq zero    (suc n) _ ()
  eq (suc v) zero    () _
  eq (suc v) (suc n) t e = cong suc (eq v n t e)

module PastingCtx {Γ : Ctx} {x : Nat} {A : Ty} (d : Γ ⊢ps x ∶ A) (L : Nat) (𝒟 : ωCat) where
  cover : ∀ v B → lookup Γ v ≡ just B → v ∈ flat (tr Γ)
  cover v B l = subst (v ∈_) (sym (flat-tr d)) (upTo-∈ (len Γ) v (lookup-< Γ v l))

  open Interp Γ (ord (ps-facts d)) (tr Γ) (tv-tr d) cover L 𝒟 public
