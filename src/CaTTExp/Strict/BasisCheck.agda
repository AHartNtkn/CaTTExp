------------------------------------------------------------------------
-- The hypotheses of `Strict.Generation` from finite checks on a basis
-- (ledger A5).
--
-- `mkHyp` builds `Hyp B` from checks on the basis elements alone, each
-- decided by evaluation for a concrete basis:
--   * ∂∂ = 0: one equation between vectors of chains;
--   * ∂ lowers degree: ∂^±bᵢ has degree deg bᵢ − 1 (zero in degree 0);
--   * the order: supp ∂⁻bᵢ ⊆ [0, i), supp ∂⁺bᵢ ⊆ (i, N);
--   * ε∂ = 0 on 1-chains: ε∂⁺bᵢ = ε∂⁻bᵢ for deg bᵢ = 1;
--   * unitality: ε⟨bᵢ⟩₀^± = 1 for i < N.
-- Examples at the end: the arrow and the 2-globe, so the hypotheses
-- of `generation` are satisfiable.
------------------------------------------------------------------------
module CaTTExp.Strict.BasisCheck where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_)
open import CaTTExp.Strict.Tables using (CMon; Vec; []; _∷_)
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms
open import CaTTExp.Strict.Generation
open import CaTTExp.Strict.Nu using (IsCell)
open import CaTTExp.Strict.CMonSolver
open import CaTTExp.Strict.Bag using (+-comm; +-assoc; +-zero)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Vectors.

mapV : ∀ {A B : Set} {m} → (A → B) → Vec A m → Vec B m
mapV f []       = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

zipV : ∀ {A B C : Set} {m} → (A → B → C) → Vec A m → Vec B m → Vec C m
zipV f []       []       = []
zipV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipV f xs ys

at-map : ∀ {A B : Set} {m} (f : A → B) (d : A) (d′ : B) → f d ≡ d′ → (xs : Vec A m) → ∀ i →
         at d′ (mapV f xs) i ≡ f (at d xs i)
at-map f d d′ e []       i       = sym e
at-map f d d′ e (x ∷ xs) zero    = refl
at-map f d d′ e (x ∷ xs) (suc i) = at-map f d d′ e xs i

at-zip : ∀ {A B C : Set} {m} (f : A → B → C) (a : A) (b : B) (c : C) → f a b ≡ c →
         (xs : Vec A m) (ys : Vec B m) → ∀ i → at c (zipV f xs ys) i ≡ f (at a xs i) (at b ys i)
at-zip f a b c e []       []       i       = sym e
at-zip f a b c e (x ∷ xs) (y ∷ ys) zero    = refl
at-zip f a b c e (x ∷ xs) (y ∷ ys) (suc i) = at-zip f a b c e xs ys i

------------------------------------------------------------------------
-- Linear algebra on chains.

⊙-distrib : ∀ {M} k (v w : Vec Nat M) → k ⊙ (v +c w) ≡ (k ⊙ v) +c (k ⊙ w)
⊙-distrib zero    v w = sym (+c-id 0c)
⊙-distrib {M} (suc k) v w =
  trans (cong ((v +c w) +c_) (⊙-distrib k v w))
        (solve ((` 0 ⊞ ` 1) ⊞ (` 2 ⊞ ` 3)) ((` 0 ⊞ ` 2) ⊞ (` 1 ⊞ ` 3)) (lk (v ∷ w ∷ k ⊙ v ∷ k ⊙ w ∷ [])) tt)
  where open Solver (chainMon M)

lin-⊙ : ∀ {M m} k (v : Vec Nat m) (ws : Vec (Vec Nat M) m) → lin (k ⊙ v) ws ≡ k ⊙ lin v ws
lin-⊙ zero    v ws = lin-0 ws
lin-⊙ (suc k) v ws = trans (lin-+ v (k ⊙ v) ws) (cong (lin v ws +c_) (lin-⊙ k v ws))

lin-lin : ∀ {M K m} (c : Vec Nat m) (vs : Vec (Vec Nat K) m) (ws : Vec (Vec Nat M) K) →
          lin (lin c vs) ws ≡ lin c (mapV (λ v → lin v ws) vs)
lin-lin []      []       ws = lin-0 ws
lin-lin (k ∷ c) (v ∷ vs) ws = trans (lin-+ (k ⊙ v) (lin c vs) ws) (cong₂ _+c_ (lin-⊙ k v ws) (lin-lin c vs ws))

lin-zip : ∀ {M m} (c : Vec Nat m) (vs ws : Vec (Vec Nat M) m) → lin c vs +c lin c ws ≡ lin c (zipV _+c_ vs ws)
lin-zip []      []       []       = +c-id 0c
lin-zip {M} (k ∷ c) (v ∷ vs) (w ∷ ws) =
  trans (solve ((` 0 ⊞ ` 1) ⊞ (` 2 ⊞ ` 3)) ((` 0 ⊞ ` 2) ⊞ (` 1 ⊞ ` 3))
               (lk (k ⊙ v ∷ lin c vs ∷ k ⊙ w ∷ lin c ws ∷ [])) tt)
        (cong₂ _+c_ (sym (⊙-distrib k v w)) (lin-zip c vs ws))
  where open Solver (chainMon M)

⊙-0c : ∀ {M} k → k ⊙ 0c {M} ≡ 0c
⊙-0c zero    = refl
⊙-0c (suc k) = trans (+c-id (k ⊙ 0c)) (⊙-0c k)

-- lin c vs depends only on the columns where c is non-zero.
lin-supp-cong : ∀ {M m} (c : Vec Nat m) (vs ws : Vec (Vec Nat M) m) →
                (∀ i → (at 0 c i ≡ 0) ⊎ (at 0c vs i ≡ at 0c ws i)) → lin c vs ≡ lin c ws
lin-supp-cong []      []       []       h = refl
lin-supp-cong (k ∷ c) (v ∷ vs) (w ∷ ws) h = cong₂ _+c_ (hd (h 0)) (lin-supp-cong c vs ws (λ i → h (suc i)))
  where
  hd : (k ≡ 0) ⊎ (v ≡ w) → k ⊙ v ≡ k ⊙ w
  hd (inj₁ refl) = refl
  hd (inj₂ refl) = refl

prj-⊙ : ∀ {m} j (gs : Vec Nat m) k v → prj j gs (k ⊙ v) ≡ k ⊙ prj j gs v
prj-⊙ j gs zero    v = prj-0 j gs
prj-⊙ j gs (suc k) v = trans (prj-+ j gs v (k ⊙ v)) (cong (prj j gs v +c_) (prj-⊙ j gs k v))

prj-lin : ∀ {M m} j (gs : Vec Nat M) (c : Vec Nat m) (vs : Vec (Vec Nat M) m) →
          prj j gs (lin c vs) ≡ lin c (mapV (prj j gs) vs)
prj-lin j gs []      []       = prj-0 j gs
prj-lin j gs (k ∷ c) (v ∷ vs) =
  trans (prj-+ j gs (k ⊙ v) (lin c vs)) (cong₂ _+c_ (prj-⊙ j gs k v) (prj-lin j gs c vs))

augm-+′ : ∀ {m} (gs u v : Vec Nat m) → augm gs (u +c v) ≡ augm gs u + augm gs v
augm-+′ []       []      []      = refl
augm-+′ (g ∷ gs) (a ∷ u) (b ∷ v) with g ==ℕ 0
... | true  = trans (cong ((a + b) +_) (augm-+′ gs u v))
                (solve ((` 0 ⊞ ` 1) ⊞ (` 2 ⊞ ` 3)) ((` 0 ⊞ ` 2) ⊞ (` 1 ⊞ ` 3))
                       (lk (a ∷ b ∷ augm gs u ∷ augm gs v ∷ [])) tt)
  where open Solver (record { M = Nat ; ε = 0 ; _⊕_ = _+_ ; ⊕-id = λ _ → refl ; ⊕-comm = +-comm ; ⊕-assoc = +-assoc })
... | false = augm-+′ gs u v

augm-⊙ : ∀ {M} (gs : Vec Nat M) k (v w : Vec Nat M) → augm gs v ≡ augm gs w → augm gs (k ⊙ v) ≡ augm gs (k ⊙ w)
augm-⊙ gs zero    v w e = refl
augm-⊙ gs (suc k) v w e =
  trans (augm-+′ gs v (k ⊙ v)) (trans (cong₂ _+_ e (augm-⊙ gs k v w e)) (sym (augm-+′ gs w (k ⊙ w))))

augm-supp-cong : ∀ {M m} (gs : Vec Nat M) (c : Vec Nat m) (vs ws : Vec (Vec Nat M) m) →
                 (∀ i → (at 0 c i ≡ 0) ⊎ (augm gs (at 0c vs i) ≡ augm gs (at 0c ws i))) →
                 augm gs (lin c vs) ≡ augm gs (lin c ws)
augm-supp-cong gs []      []       []       h = refl
augm-supp-cong gs (k ∷ c) (v ∷ vs) (w ∷ ws) h =
  trans (augm-+′ gs (k ⊙ v) (lin c vs))
    (trans (cong₂ _+_ (hd (h 0)) (augm-supp-cong gs c vs ws (λ i → h (suc i))))
           (sym (augm-+′ gs (k ⊙ w) (lin c ws))))
  where
  hd : (k ≡ 0) ⊎ (augm gs v ≡ augm gs w) → augm gs (k ⊙ v) ≡ augm gs (k ⊙ w)
  hd (inj₁ refl) = refl
  hd (inj₂ e)    = augm-⊙ gs k v w e

-- A non-zero coefficient of a chain of degree j sits on a basis
-- element of degree j.
deg-at : ∀ {m} j (gs w : Vec Nat m) c → prj j gs w ≡ w → (at 0 w c ≡ 0) ⊎ (at 0 gs c ≡ j)
deg-at j []       []      c       p = inj₁ refl
deg-at j (g ∷ gs) (a ∷ w) (suc c) p = deg-at j gs w c (tl p)
  where
  tl : ∀ {m} {x y : Nat} {u v : Vec Nat m} → _≡_ {A = Vec Nat (suc m)} (x ∷ u) (y ∷ v) → u ≡ v
  tl refl = refl
deg-at j (g ∷ gs) (a ∷ w) zero    p with g ==ℕ j | ==ℕ-sound g j
... | true  | s = inj₂ (s tt)
... | false | _ = inj₁ (sym (hd p))
  where
  hd : ∀ {m} {x y : Nat} {u v : Vec Nat m} → _≡_ {A = Vec Nat (suc m)} (x ∷ u) (y ∷ v) → x ≡ y
  hd refl = refl

------------------------------------------------------------------------
-- Boolean checks for supports and finite ranges.

-- All entries at index ≥ t vanish.
loB : ∀ {m} → Nat → Vec Nat m → Bool
loB t       []      = true
loB zero    (a ∷ u) = (a ==ℕ 0) ∧ loB zero u
loB (suc t) (a ∷ u) = loB t u

-- All entries at index ≤ t vanish.
hiB : ∀ {m} → Nat → Vec Nat m → Bool
hiB t       []      = true
hiB zero    (a ∷ u) = a ==ℕ 0
hiB (suc t) (a ∷ u) = (a ==ℕ 0) ∧ hiB t u

loB-ok : ∀ {m} t (u : Vec Nat m) → T (loB t u) → ∀ d → t ≤ d → at 0 u d ≡ 0
loB-ok t       []      _ d       _       = refl
loB-ok zero    (a ∷ u) p zero    _       = ==ℕ-sound a 0 (∧-fst p)
loB-ok zero    (a ∷ u) p (suc d) _       = loB-ok zero u (∧-snd {a ==ℕ 0} p) d z≤n
loB-ok (suc t) (a ∷ u) p (suc d) (s≤s q) = loB-ok t u p d q

hiB-ok : ∀ {m} t (u : Vec Nat m) → T (hiB t u) → ∀ d → d ≤ t → at 0 u d ≡ 0
hiB-ok t       []      _ d       _       = refl
hiB-ok zero    (a ∷ u) p zero    _       = ==ℕ-sound a 0 p
hiB-ok (suc t) (a ∷ u) p zero    _       = ==ℕ-sound a 0 (∧-fst p)
hiB-ok (suc t) (a ∷ u) p (suc d) (s≤s q) = hiB-ok t u (∧-snd {a ==ℕ 0} p) d q

-- The i-th vector satisfies the check at i.
allIx : ∀ {M m} → (Nat → Vec Nat M → Bool) → Nat → Vec (Vec Nat M) m → Bool
allIx b i []       = true
allIx b i (v ∷ vs) = b i v ∧ allIx b (suc i) vs

allIx-ok : ∀ {M m} (b : Nat → Vec Nat M → Bool) i (vs : Vec (Vec Nat M) m) → T (allIx b i vs) →
           ∀ k → k < m → T (b (k + i) (at 0c vs k))
allIx-ok b i []       p k ()
allIx-ok b i (v ∷ vs) p zero    _       = ∧-fst p
allIx-ok b i (v ∷ vs) p (suc k) (s≤s q) =
  subst (λ n → T (b n (at 0c vs k))) (+-suc′ k i) (allIx-ok b (suc i) vs (∧-snd {b i v} p) k q)
  where
  +-suc′ : ∀ m n → m + suc n ≡ suc (m + n)
  +-suc′ zero    n = refl
  +-suc′ (suc m) n = cong suc (+-suc′ m n)

-- p holds below n.
below : Nat → (Nat → Bool) → Bool
below zero    p = true
below (suc n) p = below n p ∧ p n

below-ok : ∀ n p → T (below n p) → ∀ i → i < n → T (p i)
below-ok (suc n) p h i q with ==ℕ-sound i n
below-ok (suc n) p h i (s≤s q) | e = go (≤-cases q)
  where
  ≤-cases : ∀ {i n} → i ≤ n → (i < n) ⊎ (i ≡ n)
  ≤-cases {zero}  {zero}  z≤n     = inj₂ refl
  ≤-cases {zero}  {suc n} z≤n     = inj₁ (s≤s z≤n)
  ≤-cases {suc i} {suc n} (s≤s q) with ≤-cases q
  ... | inj₁ r = inj₁ (s≤s r)
  ... | inj₂ r = inj₂ (cong suc r)
  go : (i < n) ⊎ (i ≡ n) → T (p i)
  go (inj₁ r)    = below-ok n p (∧-fst h) i r
  go (inj₂ refl) = ∧-snd {below n p} h

------------------------------------------------------------------------
-- The checks and `mkHyp`.

module _ {N : Nat} (B : Basis N) where
  open Basis B

  -- ∂∂ on the basis, as vectors of chains.
  DD : Set
  DD = zipV _+c_ (mapV (λ v → lin v bplus) bplus) (mapV (λ v → lin v bminus) bminus)
     ≡ zipV _+c_ (mapV (λ v → lin v bplus) bminus) (mapV (λ v → lin v bminus) bplus)

  -- ∂^±bᵢ has degree deg bᵢ − 1, and is zero in degree 0.
  degFix : Nat → Vec Nat N → Vec Nat N
  degFix g v = if g ==ℕ 0 then 0c else prj (g ∸ 1) gdeg v

  DegP DegM : Set
  DegP = zipV degFix gdeg bplus ≡ bplus
  DegM = zipV degFix gdeg bminus ≡ bminus

  -- ε∂⁺ = ε∂⁻ on degree-1 elements.
  augFix : Nat → Vec Nat N → Nat
  augFix g v = if g ==ℕ 1 then augm gdeg v else 0

  Aug1 : Set
  Aug1 = zipV augFix gdeg bplus ≡ zipV augFix gdeg bminus

  OrdM OrdP : Set
  OrdM = T (allIx loB 0 bminus)
  OrdP = T (allIx hiB 0 bplus)

  dd-from : DD → ∀ c → dP B (dP B c) +c dM B (dM B c) ≡ dP B (dM B c) +c dM B (dP B c)
  dd-from E c =
    trans (cong₂ _+c_ (lin-lin c bplus bplus) (lin-lin c bminus bminus))
    (trans (lin-zip c _ _)
    (trans (cong (lin c) E)
    (trans (sym (lin-zip c _ _))
           (sym (cong₂ _+c_ (lin-lin c bminus bplus) (lin-lin c bplus bminus))))))

  deg-from : ∀ (bs : Vec (Vec Nat N) N) → zipV degFix gdeg bs ≡ bs →
             ∀ j c → prj (suc j) gdeg c ≡ c → prj j gdeg (lin c bs) ≡ lin c bs
  deg-from bs E j c dc = trans (prj-lin j gdeg c bs) (lin-supp-cong c (mapV (prj j gdeg) bs) bs col)
    where
    col : ∀ i → (at 0 c i ≡ 0) ⊎ (at 0c (mapV (prj j gdeg) bs) i ≡ at 0c bs i)
    col i with deg-at (suc j) gdeg c i dc
    ... | inj₁ z = inj₁ z
    ... | inj₂ g = inj₂ (trans (at-map (prj j gdeg) 0c 0c (prj-0 j gdeg) bs i)
                          (trans (cong (λ g′ → degFix g′ (at 0c bs i)) (sym g))
                                 (trans (sym (at-zip degFix 0 0c 0c refl gdeg bs i)) (cong (λ v → at 0c v i) E))))

  aug-from : Aug1 → ∀ c → prj 1 gdeg c ≡ c → augm gdeg (dP B c) ≡ augm gdeg (dM B c)
  aug-from E c dc = augm-supp-cong gdeg c bplus bminus col
    where
    col : ∀ i → (at 0 c i ≡ 0) ⊎ (augm gdeg (at 0c bplus i) ≡ augm gdeg (at 0c bminus i))
    col i with deg-at 1 gdeg c i dc
    ... | inj₁ z = inj₁ z
    ... | inj₂ g = inj₂ (trans (cong (λ g′ → augFix g′ (at 0c bplus i)) (sym g))
                          (trans (sym (at-zip augFix 0 0c 0 refl gdeg bplus i))
                            (trans (cong (λ v → at 0 v i) E)
                              (trans (at-zip augFix 0 0c 0 refl gdeg bminus i)
                                     (cong (λ g′ → augFix g′ (at 0c bminus i)) g)))))

  private
    at-out : ∀ {A : Set} {m} (d : A) (vs : Vec A m) i → m ≤ i → at d vs i ≡ d
    at-out d []       i       _       = refl
    at-out d (v ∷ vs) (suc i) (s≤s q) = at-out d vs i q

    +0 : ∀ i → i + 0 ≡ i
    +0 zero    = refl
    +0 (suc i) = cong suc (+0 i)

  ordm-from : OrdM → ∀ i d → i ≤ d → at 0 (at 0c bminus i) d ≡ 0
  ordm-from h i d p with ≤-dec N i
  ... | inj₁ Ni = trans (cong (λ v → at 0 v d) (at-out 0c bminus i Ni)) (at-0c {N} d)
  ... | inj₂ iN = loB-ok i (at 0c bminus i) (subst (λ n → T (loB n (at 0c bminus i))) (+0 i) (allIx-ok loB 0 bminus h i iN)) d p

  ordp-from : OrdP → ∀ i d → d ≤ i → at 0 (at 0c bplus i) d ≡ 0
  ordp-from h i d p with ≤-dec N i
  ... | inj₁ Ni = trans (cong (λ v → at 0 v d) (at-out 0c bplus i Ni)) (at-0c {N} d)
  ... | inj₂ iN = hiB-ok i (at 0c bplus i) (subst (λ n → T (hiB n (at 0c bplus i))) (+0 i) (allIx-ok hiB 0 bplus h i iN)) d p

  UnitalB : Set
  UnitalB = T (below N (λ i → (augm gdeg (fst (Atom.ent B i 0)) ==ℕ 1) ∧ (augm gdeg (snd (Atom.ent B i 0)) ==ℕ 1)))

  mkHyp : DD → DegP → DegM → OrdM → OrdP → Aug1 → UnitalB → Hyp B
  mkHyp dd dgp dgm om op au un = record
    { dd = dd-from dd
    ; deg-dp = deg-from bplus dgp
    ; deg-dm = deg-from bminus dgm
    ; ordm = ordm-from om
    ; ordp = ordp-from op
    ; aug1 = aug-from au
    ; unital = λ i iN → let t = below-ok N _ un i iN in
                        ==ℕ-sound _ 1 (∧-fst t) , ==ℕ-sound _ 1 (∧-snd {augm gdeg (fst (Atom.ent B i 0)) ==ℕ 1} t)
    }

------------------------------------------------------------------------
-- Examples.

private
  e : ∀ {m} → Nat → Vec Nat m
  e = unit

  z : ∀ {m} → Vec Nat m
  z = 0c

-- The arrow x → f → y, listed x, f, y.
BD¹ : Basis 3
BD¹ = record { gdeg = 0 ∷ 1 ∷ 0 ∷ [] ; bplus = z ∷ e 2 ∷ z ∷ [] ; bminus = z ∷ e 0 ∷ z ∷ [] }

hyp-D¹ : Hyp BD¹
hyp-D¹ = mkHyp BD¹ refl refl refl tt tt refl tt

-- The 2-globe α : f ⇒ g : x → y, listed x, f, α, g, y.
BD² : Basis 5
BD² = record { gdeg   = 0 ∷ 1 ∷ 2 ∷ 1 ∷ 0 ∷ []
             ; bplus  = z ∷ e 4 ∷ e 3 ∷ e 4 ∷ z ∷ []
             ; bminus = z ∷ e 0 ∷ e 1 ∷ e 0 ∷ z ∷ [] }

hyp-D² : Hyp BD²
hyp-D² = mkHyp BD² refl refl refl tt tt refl tt

-- So generation applies: every cell of ν(λD²) is a composite of atoms.
gen-D² : ∀ x → IsCell (adc BD²) 2 x → Gen.Gen BD² hyp-D² 2 x
gen-D² = Gen.generation BD² hyp-D² 2
