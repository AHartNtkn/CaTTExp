------------------------------------------------------------------------
-- Splitting off an atom (ledger A5, (N3), collapse step 4).
--
-- In an ordered unital basis, let x be a cell whose rows above s are
-- the single row a + b (a < b, both of degree s + 1). If x has the
-- s-source of the atom ⟨a⟩, then x = ⟨a⟩ #ₛ z for a cell z whose rows
-- above s are the single row b; dually, if x has the s-target of ⟨b⟩,
-- then x = z #ₛ ⟨b⟩ with z's rows above s the single row a. (Steiner's
-- peeling, `Gen.peel`, with disjointness from the order, and the
-- factor identified with the atom by `Lifting.Det.det`.)
------------------------------------------------------------------------
module CaTTExp.Strict.Split where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Tables
open import CaTTExp.Strict.Nu
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms
open import CaTTExp.Strict.Generation
open import CaTTExp.Strict.Lifting
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

module Split {N : Nat} (B : Basis N) (H : Hyp B) (L : Nat) where
  open Basis B
  open Hyp H
  open Atom B
  open Gen B H L
  open Det K L using (det; Above)

  private
    𝕄 = ADC.𝕄 K

    at-out : ∀ {A : Set} {m} (d : A) (vs : Vec A m) i → m ≤ i → at d vs i ≡ d
    at-out d []       i       _       = refl
    at-out d (v ∷ vs) (suc i) (s≤s q) = at-out d vs i q

    at-tabG : ∀ {m} (d : Row) (f : RF) k j → j < m → at d (tabG {m = m} f k) j ≡ f (j + k)
    at-tabG {suc m} d f k zero    _       = refl
    at-tabG {suc m} d f k (suc j) (s≤s l) = trans (at-tabG {m} d f (suc k) j l) (cong f (+-suc′ j k))
      where
      +-suc′ : ∀ j k → j + suc k ≡ suc (j + k)
      +-suc′ zero    k = refl
      +-suc′ (suc j) k = cong suc (+-suc′ j k)

    +0 : ∀ j → j + 0 ≡ j
    +0 zero    = refl
    +0 (suc j) = cong suc (+0 j)

    -- Rows of tables of length L + 1.
    rowT : ∀ (f : RF) j → j ≤ L → at 0R (tabG {m = suc L} f 0) j ≡ f j
    rowT f j l = trans (at-tabG 0R f 0 j (s≤s l)) (cong f (+0 j))

    -- Tables agreeing above s.
    above : ∀ {m} s (x y : Tab 𝕄 m) → (∀ j → s < j → at 0R x j ≡ at 0R y j) → Above s x y
    above s       []      []        h = tt
    above zero    (e ∷ r) (e′ ∷ r′) h = vext′ r r′ (λ j → h (suc j) (s≤s z≤n))
      where
      vext′ : ∀ {m} (r r′ : Tab 𝕄 m) → (∀ j → at 0R r j ≡ at 0R r′ j) → r ≡ r′
      vext′ []      []        h = refl
      vext′ (e ∷ r) (e′ ∷ r′) h = cong₂ _∷_ (h 0) (vext′ r r′ (λ j → h (suc j)))
    above (suc s) (e ∷ r) (e′ ∷ r′) h = above s r r′ (λ j l → h (suc j) (s≤s l))

    W-add : ∀ s u v j → W s (u +c v) j ≡ W s u j +R W s v j
    W-add s u v j with cmp3 j (suc s)
    ... | LT = sym (cong₂ _,_ (+c-id 0c) (+c-id 0c))
    ... | EQ = refl
    ... | GT = sym (cong₂ _,_ (+c-id 0c) (+c-id 0c))

    ==-refl′ : ∀ n → (n ==ℕ n) ≡ true
    ==-refl′ zero    = refl
    ==-refl′ (suc n) = ==-refl′ n

    prj-unit : ∀ {m} (gs : Vec Nat m) a j → a < m → at 0 gs a ≡ j → prj j gs (unit a) ≡ unit a
    prj-unit (g ∷ gs) zero    j _       e rewrite e | ==-refl′ j = cong (1 ∷_) (prj-0 j gs)
    prj-unit (g ∷ gs) (suc a) j (s≤s l) e = cong₂ _∷_ (if-z (g ==ℕ j)) (prj-unit gs a j l e)
      where
      if-z : ∀ b → (if b then 0 else 0) ≡ 0
      if-z true  = refl
      if-z false = refl

    lin-unit : ∀ {M m} i → i < m → (vs : Vec (Vec Nat M) m) → lin (unit {m} i) vs ≡ at 0c vs i
    lin-unit {M} {suc m} zero    _       (v ∷ vs) =
      trans (cong₂ _+c_ (trans (+c-comm v 0c) (+c-id v)) (lin-0 vs)) (trans (+c-comm v 0c) (+c-id v))
    lin-unit {M} {suc m} (suc i) (s≤s l) (v ∷ vs) = trans (+c-id (lin (unit {m} i) vs)) (lin-unit i l vs)

    ∸-z : ∀ a b → a ≡ 0 → a ∸ b ≡ 0
    ∸-z zero zero    _ = refl
    ∸-z zero (suc b) _ = refl

    -- The order makes the boundaries of a < b disjoint as Steiner requires.
    disj : ∀ s a b → a < N → b < N → a < b → Disj s (W s (unit a)) (W s (unit b))
    disj s a b aN bN ab d rewrite W-top s (unit a) | W-top s (unit b) with ≤-dec a d
    ... | inj₁ ad = inj₁ (trans (at-∸c (dM B (unit a)) (dP B (unit a)) d)
                          (∸-z _ (at0 (dP B (unit a)) d) (trans (cong (λ v → at0 v d) (lin-unit a aN bminus)) (ordm a d ad))))
    ... | inj₂ da = inj₂ (trans (at-∸c (dP B (unit b)) (dM B (unit b)) d)
                          (∸-z _ (at0 (dM B (unit b)) d) (trans (cong (λ v → at0 v d) (lin-unit b bN bplus)) (ordp b d (≤-trans (<→≤ da) (<→≤ ab))))))

    -- The rows of an atom above s, for deg a = s + 1.
    atom-above : ∀ s a → deg a ≡ suc s → suc s ≤ L → ∀ j → s < j → at 0R (atomT L a) j ≡ W s (unit a) j
    atom-above s a da sL j sj with ≤-dec j L
    ... | inj₂ Lj = trans (at-out 0R (atomT L a) j Lj) (sym (W-above s (unit a) j (≤-trans (s≤s sL) Lj)))
    ... | inj₁ jL = trans (cong (λ t → at 0R t j) (atomT≡ {suc L} (ent a) 0)) (trans (rowT (ent a) j jL) (go j sj))
      where
      go : ∀ j → s < j → ent a j ≡ W s (unit a) j
      go j sj with tri j (suc s)
      ... | tri< l = ⊥-elim (≤-<-⊥ sj l)
      ... | tri≡ refl = trans (top a da) (sym (W-top s (unit a)))
        where
        <ℕ-suc : ∀ n → (n <ℕ suc n) ≡ true
        <ℕ-suc zero    = refl
        <ℕ-suc (suc n) = <ℕ-suc n
        ∸-self : ∀ n → n ∸ n ≡ 0
        ∸-self zero    = refl
        ∸-self (suc n) = ∸-self n
        top : ∀ a → deg a ≡ suc s → ent a (suc s) ≡ (unit a , unit a)
        top a e rewrite e | <ℕ-suc (suc s) | ∸-self s = refl
      ... | tri> l = trans (ent-zero a j (subst (_< j) (sym da) l)) (sym (W-above s (unit a) j l))

    rows-above : ∀ s (f g : RF) → (∀ j → s < j → f j ≡ g j) → suc s ≤ L → (∀ j → L < j → g j ≡ 0R) →
                 ∀ j → s < j → at 0R (tabG {m = suc L} f 0) j ≡ g j
    rows-above s f g h sL gz j sj with ≤-dec j L
    ... | inj₁ jL = trans (rowT f j jL) (h j sj)
    ... | inj₂ Lj = trans (at-out 0R (tabG {m = suc L} f 0) j Lj) (sym (gz j Lj))

  ----------------------------------------------------------------------
  -- A cell's s-source is determined by its s-target and its rows above s.

  private
    vextT : ∀ {m} (r r′ : Tab 𝕄 m) → (∀ j → at 0R r j ≡ at 0R r′ j) → r ≡ r′
    vextT []      []        h = refl
    vextT (e ∷ r) (e′ ∷ r′) h = cong₂ _∷_ (h 0) (vextT r r′ (λ j → h (suc j)))

    at-src-lt : ∀ {m} n (x : Tab 𝕄 m) j → j < n → at 0R (srcT 𝕄 n x) j ≡ at 0R x j
    at-src-lt (suc n) []      j       _       = refl
    at-src-lt (suc n) (e ∷ r) zero    _       = refl
    at-src-lt (suc n) (e ∷ r) (suc j) (s≤s l) = at-src-lt n r j l
    at-tgt-lt : ∀ {m} n (x : Tab 𝕄 m) j → j < n → at 0R (tgtT 𝕄 n x) j ≡ at 0R x j
    at-tgt-lt (suc n) []      j       _       = refl
    at-tgt-lt (suc n) (e ∷ r) zero    _       = refl
    at-tgt-lt (suc n) (e ∷ r) (suc j) (s≤s l) = at-tgt-lt n r j l
    at-src-eq : ∀ {m} n (x : Tab 𝕄 m) → at 0R (srcT 𝕄 n x) n ≡ (fst (at 0R x n) , fst (at 0R x n))
    at-src-eq n       []            = refl
    at-src-eq zero    ((a , b) ∷ r) = refl
    at-src-eq (suc n) (e ∷ r)       = at-src-eq n r
    at-tgt-eq : ∀ {m} n (x : Tab 𝕄 m) → at 0R (tgtT 𝕄 n x) n ≡ (snd (at 0R x n) , snd (at 0R x n))
    at-tgt-eq n       []            = refl
    at-tgt-eq zero    ((a , b) ∷ r) = refl
    at-tgt-eq (suc n) (e ∷ r)       = at-tgt-eq n r
    at-src-gt : ∀ {m} n (x : Tab 𝕄 m) j → n < j → at 0R (srcT 𝕄 n x) j ≡ 0R
    at-src-gt n       []            j       l       = refl
    at-src-gt {suc m} zero ((a , b) ∷ r) (suc j) l = at-z {m} j
      where
      at-z : ∀ {m} j → at 0R (zeros 𝕄 {m}) j ≡ 0R
      at-z {zero}  j       = refl
      at-z {suc m} zero    = refl
      at-z {suc m} (suc j) = at-z {m} j
    at-src-gt (suc n) (e ∷ r) (suc j) (s≤s l) = at-src-gt n r j l

    above-at : ∀ {m} s (x y : Tab 𝕄 m) → Above s x y → ∀ j → s < j → at 0R x j ≡ at 0R y j
    above-at s       []      []        a j       l       = refl
    above-at zero    (e ∷ r) (e′ ∷ r′) a (suc j) l       = cong (λ t → at 0R t j) a
    above-at (suc s) (e ∷ r) (e′ ∷ r′) a (suc j) (s≤s l) = above-at s r r′ a j l

  src-from-tgt : ∀ n (x y : Tb) → IsCell K L x → IsCell K L y → tgtT 𝕄 n x ≡ tgtT 𝕄 n y → Above n x y →
                 srcT 𝕄 n x ≡ srcT 𝕄 n y
  src-from-tgt n x y cx cy t a = vextT _ _ pt
    where
    lt : ∀ j → j < n → at 0R x j ≡ at 0R y j
    lt j l = trans (sym (at-tgt-lt n x j l)) (trans (cong (λ q → at 0R q j) t) (at-tgt-lt n y j l))
    plus : snd (at 0R x n) ≡ snd (at 0R y n)
    plus = cong snd (trans (sym (at-tgt-eq n x)) (trans (cong (λ q → at 0R q n) t) (at-tgt-eq n y)))
    minus : fst (at 0R x n) ≡ fst (at 0R y n)
    minus with IsCell→CellF x cx | IsCell→CellF y cy | tri n L
    ... | (_ , ex , _) | (_ , ey , _) | tri< nL =
      cancel _ _ (dP B u) (trans (+c-comm _ (dP B u))
        (trans (fst (snd (snd (ex n nL))))
          (trans (cong₂ (λ v w → dM B v +c w) u≡ plus)
            (trans (sym (fst (snd (snd (ey n nL))))) (trans (cong (λ v → dP B v +c fst (at 0R y n)) (sym u≡)) (+c-comm (dP B u) _))))))
      where
      u = fst (at 0R x (suc n))
      u≡ : u ≡ fst (at 0R y (suc n))
      u≡ = cong fst (above-at n x y a (suc n) (≤-refl _))
      cancel = +c-cancel
    ... | (_ , _ , lx) | (_ , _ , ly) | tri≡ refl = trans lx (trans plus (sym ly))
    ... | _ | _ | tri> Ln = cong fst (trans (at-out 0R x n Ln) (sym (at-out 0R y n Ln)))
    pt : ∀ j → at 0R (srcT 𝕄 n x) j ≡ at 0R (srcT 𝕄 n y) j
    pt j with tri j n
    ... | tri< l = trans (at-src-lt n x j l) (trans (lt j l) (sym (at-src-lt n y j l)))
    ... | tri≡ refl = trans (at-src-eq j x) (trans (cong (λ v → v , v) minus) (sym (at-src-eq j y)))
    ... | tri> l = trans (at-src-gt n x j l) (sym (at-src-gt n y j l))

  Rest : Nat → Nat → Set
  Rest s b = Σ Tb (λ z → IsCell K L z × (∀ j → s < j → at 0R z j ≡ W s (unit b) j))

  -- x = ⟨a⟩ #ₛ z.
  split-src : ∀ s a b → a < N → b < N → a < b → deg a ≡ suc s → deg b ≡ suc s → suc s ≤ L →
              (x : Tb) → IsCell K L x → (∀ j → s < j → at 0R x j ≡ W s (unit a +c unit b) j) →
              srcT 𝕄 s x ≡ srcT 𝕄 s (atomT L a) →
              Σ (Rest s b) (λ r → (tgtT 𝕄 s (atomT L a) ≡ srcT 𝕄 s (fst r)) × (compT 𝕄 s (atomT L a) (fst r) ≡ x))
  split-src s a b aN bN ab da db sL x cx xr xs =
    (Z , CellF→IsCell _ (Split.cz S) , zrows) ,
    subst (λ t → tgtT 𝕄 s t ≡ srcT 𝕄 s Z) Y≡A (Split.match S) ,
    trans (cong (λ t → compT 𝕄 s t Z) (sym Y≡A)) (trans (Split.comp S) (sym (tab-at 0R x)))
    where
    f = at 0R x
    S = peel s sL f (W s (unit a)) (W s (unit b)) (IsCell→CellF x cx)
          (Good-W s (unit a) (prj-unit gdeg a (suc s) aN da)) (Good-W s (unit b) (prj-unit gdeg b (suc s) bN db))
          (λ j sj _ → trans (xr j sj) (W-add s (unit a) (unit b) j)) (disj s a b aN bN ab)
    Y = tabG {m = suc L} (Split.y S) 0
    Z = tabG {m = suc L} (Split.z S) 0
    A = atomT L a
    cA : IsCell K L A
    cA = gen-cell (g-atom a aN (subst (_≤ L) (sym da) sL))
    Y≡A : Y ≡ A
    Y≡A = det s Y A (CellF→IsCell _ (Split.cy S)) cA
            (trans (sym (s-comp 𝕄 s Y Z)) (trans (cong (srcT 𝕄 s) (Split.comp S)) (trans (cong (srcT 𝕄 s) (sym (tab-at 0R x))) xs)))
            (above s Y A (λ j sj → trans (rows-above s (Split.y S) (W s (unit a)) (Split.yp S) sL
                                              (λ j Lj → W-above s (unit a) j (≤-trans (s≤s sL) Lj)) j sj)
                                         (sym (atom-above s a da sL j sj))))
    zrows : ∀ j → s < j → at 0R Z j ≡ W s (unit b) j
    zrows = rows-above s (Split.z S) (W s (unit b)) (Split.zq S) sL (λ j Lj → W-above s (unit b) j (≤-trans (s≤s sL) Lj))

  -- x = z #ₛ ⟨b⟩.
  split-tgt : ∀ s a b → a < N → b < N → a < b → deg a ≡ suc s → deg b ≡ suc s → suc s ≤ L →
              (x : Tb) → IsCell K L x → (∀ j → s < j → at 0R x j ≡ W s (unit a +c unit b) j) →
              tgtT 𝕄 s x ≡ tgtT 𝕄 s (atomT L b) →
              Σ (Rest s a) (λ r → (tgtT 𝕄 s (fst r) ≡ srcT 𝕄 s (atomT L b)) × (compT 𝕄 s (fst r) (atomT L b) ≡ x))
  split-tgt s a b aN bN ab da db sL x cx xr xt =
    (Y , CellF→IsCell _ (Split.cy S) , yrows) ,
    subst (λ t → tgtT 𝕄 s Y ≡ srcT 𝕄 s t) Z≡B (Split.match S) ,
    trans (cong (compT 𝕄 s Y) (sym Z≡B)) (trans (Split.comp S) (sym (tab-at 0R x)))
    where
    f = at 0R x
    S = peel s sL f (W s (unit a)) (W s (unit b)) (IsCell→CellF x cx)
          (Good-W s (unit a) (prj-unit gdeg a (suc s) aN da)) (Good-W s (unit b) (prj-unit gdeg b (suc s) bN db))
          (λ j sj _ → trans (xr j sj) (W-add s (unit a) (unit b) j)) (disj s a b aN bN ab)
    Y = tabG {m = suc L} (Split.y S) 0
    Z = tabG {m = suc L} (Split.z S) 0
    Bt = atomT L b
    cB : IsCell K L Bt
    cB = gen-cell (g-atom b bN (subst (_≤ L) (sym db) sL))
    Z≡B : Z ≡ Bt
    Z≡B = det′ (CellF→IsCell _ (Split.cz S)) cB
            (trans (sym (t-comp 𝕄 s Y Z (Split.match S))) (trans (cong (tgtT 𝕄 s) (Split.comp S)) (trans (cong (tgtT 𝕄 s) (sym (tab-at 0R x))) xt)))
            (above s Z Bt (λ j sj → trans (rows-above s (Split.z S) (W s (unit b)) (Split.zq S) sL
                                              (λ j Lj → W-above s (unit b) j (≤-trans (s≤s sL) Lj)) j sj)
                                         (sym (atom-above s b db sL j sj))))
      where
      det′ : IsCell K L Z → IsCell K L Bt → tgtT 𝕄 s Z ≡ tgtT 𝕄 s Bt → Above s Z Bt → Z ≡ Bt
      det′ cz cb t a = det s Z Bt cz cb (src-from-tgt s Z Bt cz cb t a) a
    yrows : ∀ j → s < j → at 0R Y j ≡ W s (unit a) j
    yrows = rows-above s (Split.y S) (W s (unit a)) (Split.yp S) sL (λ j Lj → W-above s (unit a) j (≤-trans (s≤s sL) Lj))
