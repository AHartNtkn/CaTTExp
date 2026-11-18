------------------------------------------------------------------------
-- The collapse of the Gray cylinder (ledger A5, (N3), collapse step 2).
--
-- For an ordered globular presentation D (CaTTExp.Strict.GlobBasis)
-- with Steiner complex K = λD, the cylinder K ⊗ λD¹ (CaTTExp.Strict.
-- Cylinder) collapses onto the suspension Σ K:
--     q(k ⊗ 0) = ⊥,  q(k ⊗ 1) = ⊤     (deg k = 0)
--     q(k ⊗ 0) = q(k ⊗ 1) = 0          (deg k ≥ 1)
--     q(k ⊗ i) = Σk.
-- q is a morphism of complexes in the sense of CaTTExp.Strict.NuMap (a
-- chain map, degree-preserving and augmentation-preserving; it does not
-- respect ∂⁺, ∂⁻ separately on the killed elements), so ν(q) is a
-- strict functor ν(K ⊗ λD¹) → ν(Σ K). This is the finite-basis form of
-- `LaxColimPoint.lax`.
------------------------------------------------------------------------
module CaTTExp.Strict.Collapse where

open import CaTTExp.Prelude
open import Agda.Builtin.Nat using (_*_)
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; ≤-refl; ≤-suc; ≤-trans; ≤-<-⊥)
open import CaTTExp.Strict.Tables using (Vec; []; _∷_)
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms using (at; unit; module Atom)
open import CaTTExp.Strict.Generation using (≤-dec)
open import CaTTExp.Strict.BasisCheck
open import CaTTExp.Strict.Cylinder
open import CaTTExp.Strict.GlobBasis
open import CaTTExp.Strict.NuMap
open import CaTTExp.Strict.Expr using (Functor)
open import CaTTExp.Strict.GlobAtoms
open import CaTTExp.Strict.Bag using (+-comm; +-assoc; +-zero)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Unit vectors.

private
  if-same : ∀ {A : Set} b {v : A} → (if b then v else v) ≡ v
  if-same true  = refl
  if-same false = refl

  lin-unit : ∀ {M m} i → i < m → (vs : Vec (Vec Nat M) m) → lin (unit {m} i) vs ≡ at 0c vs i
  lin-unit {M} {suc m} zero    _       (v ∷ vs) =
    trans (cong₂ _+c_ (trans (+c-comm v 0c) (+c-id v)) (lin-0 vs)) (trans (+c-comm v 0c) (+c-id v))
  lin-unit {M} {suc m} (suc i) (s≤s l) (v ∷ vs) = trans (+c-id (lin (unit {m} i) vs)) (lin-unit i l vs)

  prj-unit : ∀ {m} (gs : Vec Nat m) k j → k < m → prj j gs (unit k) ≡ (if at 0 gs k ==ℕ j then unit k else 0c)
  prj-unit (g ∷ gs) zero    j _ with g ==ℕ j
  ... | true  = cong (1 ∷_) (prj-0 j gs)
  ... | false = cong (0 ∷_) (prj-0 j gs)
  prj-unit {suc m} (g ∷ gs) (suc k) j (s≤s l) = trans (cong₂ _∷_ (if-same (g ==ℕ j)) (prj-unit gs k j l)) (go (at 0 gs k ==ℕ j))
    where
    go : ∀ b → _≡_ {A = Vec Nat (suc m)} (0 ∷ (if b then unit k else 0c)) (if b then unit (suc k) else 0c)
    go true  = refl
    go false = refl

  augm-unit : ∀ {m} (gs : Vec Nat m) k → k < m → augm gs (unit k) ≡ (if at 0 gs k ==ℕ 0 then 1 else 0)
  augm-unit (g ∷ gs) zero    _ with g ==ℕ 0
  ... | true  = cong (1 +_) (augm-0 gs)
  ... | false = augm-0 gs
  augm-unit (g ∷ gs) (suc k) (s≤s l) with g ==ℕ 0
  ... | true  = augm-unit gs k l
  ... | false = augm-unit gs k l

  <ℕ-irr : ∀ n → (n <ℕ n) ≡ false
  <ℕ-irr zero    = refl
  <ℕ-irr (suc n) = <ℕ-irr n

  <ℕ-complete : ∀ m n → m < n → (m <ℕ n) ≡ true
  <ℕ-complete zero    (suc n) _       = refl
  <ℕ-complete (suc m) (suc n) (s≤s l) = <ℕ-complete m n l

  ≤r : ∀ a r → a ≤ a + r
  ≤r zero    r = z≤n
  ≤r (suc a) r = s≤s (≤r a r)

  *3-mono : ∀ {a b} → a ≤ b → a * 3 ≤ b * 3
  *3-mono z≤n     = z≤n
  *3-mono (s≤s p) = s≤s (s≤s (s≤s (*3-mono p)))

  -- Which of the three copies a position of the layout holds.
  data Which : Set where
    W0 Wi W1 : Which

  pick : ∀ {A : Set} → Which → A → A → A → A
  pick W0 x y z = x
  pick Wi x y z = y
  pick W1 x y z = z

  which : Bool → Nat → Which
  which true  zero          = W0
  which true  (suc zero)    = Wi
  which true  (suc (suc _)) = W1
  which false zero          = W1
  which false (suc zero)    = Wi
  which false (suc (suc _)) = W0

  slot-pick : ∀ {A : Set} b r (x y z : A) → slot b r x y z ≡ pick (which b r) x y z
  slot-pick true  zero          x y z = refl
  slot-pick true  (suc zero)    x y z = refl
  slot-pick true  (suc (suc _)) x y z = refl
  slot-pick false zero          x y z = refl
  slot-pick false (suc zero)    x y z = refl
  slot-pick false (suc (suc _)) x y z = refl

  at-pick : ∀ {A : Set} {m} (d : A) (gs : Vec Nat m) X Y Z k r → k < m → r < 3 →
            at d (cylA gs X Y Z) (k * 3 + r) ≡ pick (which (even (at 0 gs k)) r) (at d X k) (at d Y k) (at d Z k)
  at-pick d gs X Y Z k r kN rl = trans (at-cylA d gs X Y Z k r kN rl) (slot-pick (even (at 0 gs k)) r (at d X k) (at d Y k) (at d Z k))

  -- Every position below m * 3 is k * 3 + r with k < m, r < 3.
  pos : ∀ m i → i < m * 3 → Σ Nat (λ k → Σ Nat (λ r → (k < m) × ((r < 3) × (i ≡ k * 3 + r))))
  pos m i iN with divmod i
  ... | (k , r , rl , e) with ≤-dec m k
  ...   | inj₁ mk = ⊥-elim (≤-<-⊥ (≤-trans (*3-mono mk) (≤r (k * 3) r)) (subst (_< m * 3) e iN))
  ...   | inj₂ km = k , r , km , rl , e

------------------------------------------------------------------------
-- The collapse.

module Collapse (D : GData) where
  open GData D
  private
    module K = GB D
    module S = GB (Σg D)
  open Basis K.basis
  open Cyl K.basis

  NS : Nat
  NS = suc (suc N)

  gsΣ : Vec Nat NS
  gsΣ = Basis.gdeg S.basis

  e⊥ e⊤ : Chn NS
  e⊥ = unit 0
  e⊤ = unit (suc N)

  end : Chn NS → Nat → Chn NS
  end e g = if g ==ℕ 0 then e else 0c

  X Y Z : Vec (Chn NS) N
  X = mapV (end e⊥) gdeg
  Y = tab N (λ k → unit (suc k)) 0
  Z = mapV (end e⊤) gdeg

  Q : Vec (Chn NS) (N * 3)
  Q = cylA gdeg X Y Z

  module LH = LinHom B′ S.basis Q

  module Aux where
    g = λ k → at 0 gdeg k

    X-at : ∀ k → k < N → at 0c X k ≡ end e⊥ (g k)
    X-at k kN = at-map-lt (end e⊥) 0 0c gdeg k kN
    Z-at : ∀ k → k < N → at 0c Z k ≡ end e⊤ (g k)
    Z-at k kN = at-map-lt (end e⊤) 0 0c gdeg k kN
    Y-at : ∀ k → k < N → at 0c Y k ≡ unit (suc k)
    Y-at k kN = at-tab0 0c (λ k → unit (suc k)) k kN

    -- Degrees in Σ D.
    gΣ0 : at 0 gsΣ 0 ≡ 0
    gΣ0 = S.gdeg-at 0 (s≤s z≤n)
    gΣ⊤ : at 0 gsΣ (suc N) ≡ 0
    gΣ⊤ = trans (S.gdeg-at (suc N) (≤-refl _)) (cong (λ b → if b then suc (gd N) else 0) (<ℕ-irr N))
    gΣk : ∀ k → k < N → at 0 gsΣ (suc k) ≡ suc (gd k)
    gΣk k kN = trans (S.gdeg-at (suc k) (s≤s (≤-suc kN))) (cong (λ b → if b then suc (gd k) else 0) (<ℕ-complete k N kN))

    gk : ∀ k → k < N → g k ≡ gd k
    gk = K.gdeg-at

    lin-c0 : ∀ v → lin (c0 v) Q ≡ lin v X
    lin-c0 v = trans (lin-cyl gdeg v 0c 0c X Y Z)
                 (trans (cong₂ (λ p q → (lin v X +c p) +c q) (lin-0 Y) (lin-0 Z))
                        (trans (+c-comm _ 0c) (trans (+c-id _) (trans (+c-comm _ 0c) (+c-id _)))))
    lin-c1 : ∀ v → lin (c1 v) Q ≡ lin v Z
    lin-c1 v = trans (lin-cyl gdeg 0c 0c v X Y Z)
                 (trans (cong₂ (λ p q → (p +c q) +c lin v Z) (lin-0 X) (lin-0 Y)) (trans (cong (_+c lin v Z) (+c-id 0c)) (+c-id _)))

    at-zip3′ : ∀ {A B C D : Set} {m} (f : A → B → C → D) (a : A) (b : B) (c : C) (d : D) →
               (xs : Vec A m) (ys : Vec B m) (zs : Vec C m) → ∀ k → k < m →
               at d (zip3 f xs ys zs) k ≡ f (at a xs k) (at b ys k) (at c zs k)
    at-zip3′ f a b c d (x ∷ xs) (y ∷ ys) (z ∷ zs) zero    _       = refl
    at-zip3′ f a b c d (x ∷ xs) (y ∷ ys) (z ∷ zs) (suc k) (s≤s l) = at-zip3′ f a b c d xs ys zs k l

    at-selU : ∀ (p : Nat → Bool) k → k < N → at 0c (selV p gdeg (units N)) k ≡ (if p (g k) then unit k else 0c)
    at-selU p k kN = trans (at-zip (λ h v → if p h then v else 0c) 0 0c 0c (if-same (p 0)) gdeg (units N) k)
                           (cong (λ v → if p (g k) then v else 0c) (at-units N k kN))

    -- The ends of Σ D have zero boundary.
    end-∂ : ∀ (bs : Vec (Chn NS) NS) → at 0c bs 0 ≡ 0c → at 0c bs (suc N) ≡ 0c →
            ∀ e h → (e ≡ e⊥) ⊎ (e ≡ e⊤) → lin (end e h) bs ≡ 0c
    end-∂ bs b0 b1 e h w with h ==ℕ 0
    ... | false = lin-0 bs
    end-∂ bs b0 b1 e h (inj₁ refl) | true = trans (lin-unit 0 (s≤s z≤n) bs) b0
    end-∂ bs b0 b1 e h (inj₂ refl) | true = trans (lin-unit (suc N) (≤-refl _) bs) b1

    bdΣ0 : ∀ f → S.bd f 0 ≡ 0c
    bdΣ0 f = refl

    bdΣ⊤ : ∀ f → S.bd f (suc N) ≡ 0c
    bdΣ⊤ f rewrite <ℕ-irr N = refl

    bpΣ0 : at 0c (Basis.bplus S.basis) 0 ≡ 0c
    bpΣ0 = S.bp-at 0 (s≤s z≤n)
    bmΣ0 : at 0c (Basis.bminus S.basis) 0 ≡ 0c
    bmΣ0 = S.bm-at 0 (s≤s z≤n)
    bpΣ⊤ : at 0c (Basis.bplus S.basis) (suc N) ≡ 0c
    bpΣ⊤ = trans (S.bp-at (suc N) (≤-refl _)) (bdΣ⊤ (GData.t (Σg D)))
    bmΣ⊤ : at 0c (Basis.bminus S.basis) (suc N) ≡ 0c
    bmΣ⊤ = trans (S.bm-at (suc N) (≤-refl _)) (bdΣ⊤ (GData.s (Σg D)))

    -- An end copy: both boundaries of k ⊗ e go to the same point or to 0.
    end-bd : ∀ e k → k < N → lin (K.bd t k) (mapV (end e) gdeg) ≡ lin (K.bd s k) (mapV (end e) gdeg)
    end-bd e k kN with gd k in eq
    ... | zero  = refl
    ... | suc j =
      trans (lin-unit (t k) tl _) (trans (at-map-lt (end e) 0 0c gdeg (t k) tl)
      (trans (cong (end e) (trans (K.gdeg-at (t k) tl) (trans (dt k kN p) (trans (sym (ds k kN p)) (sym (K.gdeg-at (s k) sl))))))
      (sym (trans (lin-unit (s k) sl _) (at-map-lt (end e) 0 0c gdeg (s k) sl)))))
      where
      p : 1 ≤ gd k
      p = subst (1 ≤_) (sym eq) (s≤s z≤n)
      tl = tN k kN p
      sl = sN k kN p

    bdΣk : ∀ f k → k < N → S.bd f (suc k) ≡ unit (f (suc k))
    bdΣk f k kN rewrite <ℕ-complete k N kN = refl

    lin-if : ∀ {M} b (v : Chn N) (vs : Vec (Chn M) N) → lin (if b then v else 0c) vs ≡ (if b then lin v vs else 0c)
    lin-if true  v vs = refl
    lin-if false v vs = lin-0 vs

    lin-X : ∀ k → k < N → lin (unit k) X ≡ end e⊥ (gd k)
    lin-X k kN = trans (lin-unit k kN X) (trans (X-at k kN) (cong (end e⊥) (gk k kN)))
    lin-Z : ∀ k → k < N → lin (unit k) Z ≡ end e⊤ (gd k)
    lin-Z k kN = trans (lin-unit k kN Z) (trans (Z-at k kN) (cong (end e⊤) (gk k kN)))

    open import CaTTExp.Strict.CMonSolver
    open Solver (chainMon NS)

    -- The middle copy k ⊗ i.
    mid-core : ∀ k → k < N →
      (((if odd (gd k) then end e⊥ (gd k) else 0c) +c lin (K.bd t k) Y) +c (if even (gd k) then end e⊤ (gd k) else 0c))
        +c unit (if gd k ==ℕ 0 then 0 else suc (s k))
      ≡ (((if even (gd k) then end e⊥ (gd k) else 0c) +c lin (K.bd s k) Y) +c (if odd (gd k) then end e⊤ (gd k) else 0c))
        +c unit (if gd k ==ℕ 0 then suc N else suc (t k))
    mid-core k kN with gd k in eq
    ... | zero =
      trans (cong (λ a → ((0c +c a) +c e⊤) +c e⊥) (lin-0 Y))
        (trans (solve (((∅ ⊞ ∅) ⊞ ` 0) ⊞ ` 1) (((` 1 ⊞ ∅) ⊞ ∅) ⊞ ` 0) (lk (e⊤ ∷ e⊥ ∷ [])) tt)
               (sym (cong (λ a → ((e⊥ +c a) +c 0c) +c e⊤) (lin-0 Y))))
    ... | suc j = trans lhs (trans mid (sym rhs))
      where
      p : 1 ≤ gd k
      p = subst (1 ≤_) (sym eq) (s≤s z≤n)
      tl = tN k kN p
      sl = sN k kN p
      lhs : (((if odd (suc j) then 0c else 0c) +c lin (unit (t k)) Y) +c (if even (suc j) then 0c else 0c)) +c unit (suc (s k))
            ≡ ((0c +c unit (suc (t k))) +c 0c) +c unit (suc (s k))
      lhs = cong₂ (λ a b → (a +c b) +c unit (suc (s k)))
              (cong₂ _+c_ (if-same (odd (suc j))) (trans (lin-unit (t k) tl Y) (Y-at (t k) tl)))
              (if-same (even (suc j)))
      rhs : (((if even (suc j) then 0c else 0c) +c lin (unit (s k)) Y) +c (if odd (suc j) then 0c else 0c)) +c unit (suc (t k))
            ≡ ((0c +c unit (suc (s k))) +c 0c) +c unit (suc (t k))
      rhs = cong₂ (λ a b → (a +c b) +c unit (suc (t k)))
              (cong₂ _+c_ (if-same (even (suc j))) (trans (lin-unit (s k) sl Y) (Y-at (s k) sl)))
              (if-same (odd (suc j)))
      mid = solve (((∅ ⊞ ` 0) ⊞ ∅) ⊞ ` 1) (((∅ ⊞ ` 1) ⊞ ∅) ⊞ ` 0) (lk (unit (suc (t k)) ∷ unit (suc (s k)) ∷ [])) tt

    sideX : ∀ (p : Nat → Bool) k → k < N → lin (at 0c (selV p gdeg (units N)) k) X ≡ (if p (gd k) then end e⊥ (gd k) else 0c)
    sideX p k kN =
      trans (cong (λ v → lin v X) (at-selU p k kN))
        (trans (lin-if (p (g k)) (unit k) X)
          (trans (cong (λ b → if b then lin (unit k) X else 0c) (cong p (gk k kN)))
                 (cong (λ v → if p (gd k) then v else 0c) (lin-X k kN))))

    sideZ : ∀ (p : Nat → Bool) k → k < N → lin (at 0c (selV p gdeg (units N)) k) Z ≡ (if p (gd k) then end e⊤ (gd k) else 0c)
    sideZ p k kN =
      trans (cong (λ v → lin v Z) (at-selU p k kN))
        (trans (lin-if (p (g k)) (unit k) Z)
          (trans (cong (λ b → if b then lin (unit k) Z else 0c) (cong p (gk k kN)))
                 (cong (λ v → if p (gd k) then v else 0c) (lin-Z k kN))))

    YΣ : ∀ (bs : Vec (Chn NS) NS) f → (∀ i → i < NS → at 0c bs i ≡ S.bd f i) → ∀ k → k < N →
         lin (at 0c Y k) bs ≡ unit (f (suc k))
    YΣ bs f bat k kN =
      trans (cong (λ v → lin v bs) (Y-at k kN))
        (trans (lin-unit (suc k) (s≤s (≤-suc kN)) bs) (trans (bat (suc k) (s≤s (≤-suc kN))) (bdΣk f k kN)))

    mid-ch : ∀ k → k < N →
      lin (at 0c (zip3 (cyl gdeg) OdU bplus EvU) k) Q +c lin (at 0c Y k) (Basis.bminus S.basis)
      ≡ lin (at 0c (zip3 (cyl gdeg) EvU bminus OdU) k) Q +c lin (at 0c Y k) (Basis.bplus S.basis)
    mid-ch k kN = trans (cong₂ _+c_ L (YΣ _ _ S.bm-at k kN)) (trans (mid-core k kN) (sym (cong₂ _+c_ R (YΣ _ _ S.bp-at k kN))))
      where
      L = trans (cong (λ v → lin v Q) (at-zip3′ (cyl gdeg) 0c 0c 0c 0c OdU bplus EvU k kN))
            (trans (lin-cyl gdeg _ _ _ X Y Z)
              (cong₂ _+c_ (cong₂ _+c_ (sideX odd k kN) (cong (λ v → lin v Y) (K.bp-at k kN))) (sideZ even k kN)))
      R = trans (cong (λ v → lin v Q) (at-zip3′ (cyl gdeg) 0c 0c 0c 0c EvU bminus OdU k kN))
            (trans (lin-cyl gdeg _ _ _ X Y Z)
              (cong₂ _+c_ (cong₂ _+c_ (sideX even k kN) (cong (λ v → lin v Y) (K.bm-at k kN))) (sideZ odd k kN)))

    endX : ∀ bs → at 0c bs 0 ≡ 0c → at 0c bs (suc N) ≡ 0c → ∀ k → k < N → lin (at 0c X k) bs ≡ 0c
    endX bs b0 b1 k kN = trans (cong (λ v → lin v bs) (X-at k kN)) (end-∂ bs b0 b1 e⊥ (g k) (inj₁ refl))
    endZ : ∀ bs → at 0c bs 0 ≡ 0c → at 0c bs (suc N) ≡ 0c → ∀ k → k < N → lin (at 0c Z k) bs ≡ 0c
    endZ bs b0 b1 k kN = trans (cong (λ v → lin v bs) (Z-at k kN)) (end-∂ bs b0 b1 e⊤ (g k) (inj₂ refl))

    c0-bd : ∀ (bs : Vec (Chn N) N) f → (∀ i → i < N → at 0c bs i ≡ K.bd f i) → ∀ k → k < N →
            lin (at 0c (mapV c0 bs) k) Q ≡ lin (K.bd f k) X
    c0-bd bs f bat k kN = trans (cong (λ v → lin v Q) (at-map-lt c0 0c 0c bs k kN)) (trans (lin-c0 _) (cong (λ v → lin v X) (bat k kN)))
    c1-bd : ∀ (bs : Vec (Chn N) N) f → (∀ i → i < N → at 0c bs i ≡ K.bd f i) → ∀ k → k < N →
            lin (at 0c (mapV c1 bs) k) Q ≡ lin (K.bd f k) Z
    c1-bd bs f bat k kN = trans (cong (λ v → lin v Q) (at-map-lt c1 0c 0c bs k kN)) (trans (lin-c1 _) (cong (λ v → lin v Z) (bat k kN)))

    chW : ∀ k → k < N → ∀ w →
      lin (pick w (at 0c (mapV c0 bplus) k) (at 0c (zip3 (cyl gdeg) OdU bplus EvU) k) (at 0c (mapV c1 bplus) k)) Q
        +c lin (pick w (at 0c X k) (at 0c Y k) (at 0c Z k)) (Basis.bminus S.basis)
      ≡ lin (pick w (at 0c (mapV c0 bminus) k) (at 0c (zip3 (cyl gdeg) EvU bminus OdU) k) (at 0c (mapV c1 bminus) k)) Q
        +c lin (pick w (at 0c X k) (at 0c Y k) (at 0c Z k)) (Basis.bplus S.basis)
    chW k kN W0 = cong₂ _+c_ (trans (c0-bd bplus t K.bp-at k kN) (trans (end-bd e⊥ k kN) (sym (c0-bd bminus s K.bm-at k kN))))
                             (trans (endX _ bmΣ0 bmΣ⊤ k kN) (sym (endX _ bpΣ0 bpΣ⊤ k kN)))
    chW k kN Wi = mid-ch k kN
    chW k kN W1 = cong₂ _+c_ (trans (c1-bd bplus t K.bp-at k kN) (trans (end-bd e⊤ k kN) (sym (c1-bd bminus s K.bm-at k kN))))
                             (trans (endZ _ bmΣ0 bmΣ⊤ k kN) (sym (endZ _ bpΣ0 bpΣ⊤ k kN)))

  open Aux

  ch : LH.ChainQ
  ch i iN with pos N i iN
  ... | (k , r , kN , rl , refl) =
    trans (cong₂ _+c_ (cong (λ v → lin v Q) (at-pick 0c gdeg (mapV c0 bplus) (zip3 (cyl gdeg) OdU bplus EvU) (mapV c1 bplus) k r kN rl))
                      (cong (λ v → lin v (Basis.bminus S.basis)) (at-pick 0c gdeg X Y Z k r kN rl)))
      (trans (chW k kN (which (even (g k)) r))
        (sym (cong₂ _+c_ (cong (λ v → lin v Q) (at-pick 0c gdeg (mapV c0 bminus) (zip3 (cyl gdeg) EvU bminus OdU) (mapV c1 bminus) k r kN rl))
                         (cong (λ v → lin v (Basis.bplus S.basis)) (at-pick 0c gdeg X Y Z k r kN rl)))))

  private
    ==-refl′ : ∀ n → (n ==ℕ n) ≡ true
    ==-refl′ zero    = refl
    ==-refl′ (suc n) = ==-refl′ n

    endDeg : ∀ i → i < NS → at 0 gsΣ i ≡ 0 → ∀ h → prj h gsΣ (end (unit i) h) ≡ end (unit i) h
    endDeg i iS gi h with h ==ℕ 0 in eq
    ... | false = prj-0 h gsΣ
    ... | true rewrite ==ℕ-sound h 0 (subst T (sym eq) tt) =
      trans (prj-unit gsΣ i 0 iS) (cong (λ x → if x ==ℕ 0 then unit i else 0c) gi)

    endAug : ∀ i → i < NS → at 0 gsΣ i ≡ 0 → ∀ h → augm gsΣ (end (unit i) h) ≡ (if h ==ℕ 0 then 1 else 0)
    endAug i iS gi h with h ==ℕ 0
    ... | false = augm-0 gsΣ
    ... | true  = trans (augm-unit gsΣ i iS) (cong (λ x → if x ==ℕ 0 then 1 else 0) gi)

    gsuc : ∀ k → k < N → at 0 (mapV suc gdeg) k ≡ suc (g k)
    gsuc k kN = at-map-lt suc 0 0 gdeg k kN

    degW : ∀ k → k < N → ∀ w →
      prj (pick w (g k) (at 0 (mapV suc gdeg) k) (g k)) gsΣ (pick w (at 0c X k) (at 0c Y k) (at 0c Z k))
      ≡ pick w (at 0c X k) (at 0c Y k) (at 0c Z k)
    degW k kN W0 = trans (cong (prj (g k) gsΣ) (X-at k kN)) (trans (endDeg 0 (s≤s z≤n) gΣ0 (g k)) (sym (X-at k kN)))
    degW k kN W1 = trans (cong (prj (g k) gsΣ) (Z-at k kN)) (trans (endDeg (suc N) (≤-refl _) gΣ⊤ (g k)) (sym (Z-at k kN)))
    degW k kN Wi =
      trans (cong₂ (λ h v → prj h gsΣ v) (gsuc k kN) (Y-at k kN))
        (trans (prj-unit gsΣ (suc k) (suc (g k)) (s≤s (≤-suc kN)))
          (trans (cong (λ x → if x ==ℕ suc (g k) then unit (suc k) else 0c) (trans (gΣk k kN) (cong suc (sym (gk k kN)))))
            (trans (cong (λ b → if b then unit (suc k) else 0c) (==-refl′ (g k))) (sym (Y-at k kN)))))

    augW : ∀ k → k < N → ∀ w →
      augm gsΣ (pick w (at 0c X k) (at 0c Y k) (at 0c Z k))
      ≡ (if pick w (g k) (at 0 (mapV suc gdeg) k) (g k) ==ℕ 0 then 1 else 0)
    augW k kN W0 = trans (cong (augm gsΣ) (X-at k kN)) (endAug 0 (s≤s z≤n) gΣ0 (g k))
    augW k kN W1 = trans (cong (augm gsΣ) (Z-at k kN)) (endAug (suc N) (≤-refl _) gΣ⊤ (g k))
    augW k kN Wi =
      trans (cong (augm gsΣ) (Y-at k kN))
        (trans (augm-unit gsΣ (suc k) (s≤s (≤-suc kN)))
          (trans (cong (λ x → if x ==ℕ 0 then 1 else 0) (gΣk k kN))
                 (cong (λ x → if x ==ℕ 0 then 1 else 0) (sym (gsuc k kN)))))

  dq : LH.DegQ
  dq i iN with pos N i iN
  ... | (k , r , kN , rl , refl) =
    trans (cong₂ (λ h v → prj h gsΣ v) (at-pick 0 gdeg gdeg (mapV suc gdeg) gdeg k r kN rl) (at-pick 0c gdeg X Y Z k r kN rl))
      (trans (degW k kN (which (even (g k)) r)) (sym (at-pick 0c gdeg X Y Z k r kN rl)))

  aq : LH.AugQ
  aq i iN with pos N i iN
  ... | (k , r , kN , rl , refl) =
    trans (cong (augm gsΣ) (at-pick 0c gdeg X Y Z k r kN rl))
      (trans (augW k kN (which (even (g k)) r))
             (sym (cong (λ x → if x ==ℕ 0 then 1 else 0) (at-pick 0 gdeg gdeg (mapV suc gdeg) gdeg k r kN rl))))

  -- q is a morphism of complexes, so ν(q) is a strict functor.
  q : Hom (adc B′) (adc S.basis)
  q = LH.hom ch dq aq

  νq : ∀ L → Functor (ν B′ L) (ν S.basis L)
  νq L = LH.νQ ch dq aq L

------------------------------------------------------------------------
-- Example: the square λD¹ ⊗ λD¹ collapses onto Σ λD¹ = λD². The square
-- is laid out x⊗0, x⊗i, x⊗1, f⊗1, f⊗i, f⊗0, y⊗0, y⊗i, y⊗1; λD² is
-- ⊥, Σx, Σf, Σy, ⊤.

private
  module CD¹ = Collapse D¹

  _ : CD¹.Q ≡ unit 0 ∷ unit 1 ∷ unit 4 ∷ 0c ∷ unit 2 ∷ 0c ∷ unit 0 ∷ unit 3 ∷ unit 4 ∷ []
  _ = refl

  -- ν(q) on a table: the 2-cell f⊗i of the square goes to the atom Σf.
  _ : mapT CD¹.q 2 (Atom.atomT (Cyl.B′ BD¹) 2 4)
      ≡ (unit 0 , unit 4) ∷ (unit 1 , unit 3) ∷ (unit 2 , unit 2) ∷ []
  _ = refl

------------------------------------------------------------------------
-- ν(q) on the middle atoms: q sends the rows of ⟨k ⊗ i⟩ to those of ⟨Σk⟩.

module CollapseAtoms (D : GData) where
  open GData D
  open Collapse D
  private
    module K  = GB D
    module S  = GB (Σg D)
    module GK = GA D
    module GS = GA (Σg D)
    module CD = CylDD K.basis K.hyp K.DegP-ok K.DegM-ok
    module AK = Atom K.basis
    module AS = Atom S.basis
  open Basis K.basis
  open Cyl K.basis

  open Aux

  private
    end-pos : ∀ e h → 1 ≤ h → end e h ≡ 0c
    end-pos e (suc h) _ = refl

    -- The middle of F e a b, when a lies in positive degree.
    qF : ∀ e a b → lin a X ≡ 0c → lin a Z ≡ 0c → lin (CD.F e a b) Q ≡ lin b Y
    qF e a b ax az =
      trans (lin-cyl gdeg _ _ _ X Y Z) (go e)
      where
      go : ∀ e → (lin (if e then a else 0c) X +c lin b Y) +c lin (if e then 0c else a) Z ≡ lin b Y
      go true  = trans (cong₂ (λ p q → (p +c lin b Y) +c q) ax (lin-0 Z)) (trans (+c-comm _ 0c) (trans (+c-id _) (+c-id _)))
      go false = trans (cong₂ (λ p q → (p +c lin b Y) +c q) (lin-0 X) az) (trans (+c-comm _ 0c) (trans (+c-id _) (+c-id _)))
    qG : ∀ e a b → lin a X ≡ 0c → lin a Z ≡ 0c → lin (CD.G e a b) Q ≡ lin b Y
    qG e a b ax az =
      trans (lin-cyl gdeg _ _ _ X Y Z) (go e)
      where
      go : ∀ e → (lin (if e then 0c else a) X +c lin b Y) +c lin (if e then a else 0c) Z ≡ lin b Y
      go false = trans (cong₂ (λ p q → (p +c lin b Y) +c q) ax (lin-0 Z)) (trans (+c-comm _ 0c) (trans (+c-id _) (+c-id _)))
      go true  = trans (cong₂ (λ p q → (p +c lin b Y) +c q) (lin-0 X) az) (trans (+c-comm _ 0c) (trans (+c-id _) (+c-id _)))

    lin-Y : ∀ p → p < N → lin (unit p) Y ≡ unit (suc p)
    lin-Y p pN = trans (lin-unit p pN Y) (Y-at p pN)

    -- Iterated faces of Σk.
    iterΣ : ∀ f fΣ → (∀ x → 1 ≤ gd x → fΣ (suc x) ≡ suc (f x)) →
            (∀ x → x < N → 1 ≤ gd x → f x < N) → (∀ x → x < N → 1 ≤ gd x → gd (f x) ≡ gd x ∸ 1) →
            ∀ d x → x < N → d ≤ gd x → iter fΣ d (suc x) ≡ suc (iter f d x)
    iterΣ f fΣ e fN df zero    x xN l = refl
    iterΣ f fΣ e fN df (suc d) x xN l =
      trans (cong (iter fΣ d) (e x p))
        (iterΣ f fΣ e fN df d (f x) (fN x xN p) (subst (d ≤_) (sym (df x xN p)) (pr (gd x) d l)))
      where
      p = ≤-trans (s≤s z≤n) l
      pr : ∀ g d → suc d ≤ g → d ≤ g ∸ 1
      pr (suc g) d (s≤s l) = l

    sΣ-in : ∀ x → 1 ≤ gd x → GData.s (Σg D) (suc x) ≡ suc (s x)
    sΣ-in x p with gd x
    ... | suc _ = refl
    tΣ-in : ∀ x → 1 ≤ gd x → GData.t (Σg D) (suc x) ≡ suc (t x)
    tΣ-in x p with gd x
    ... | suc _ = refl

    gdΣ-in : ∀ k → k < N → GData.gd (Σg D) (suc k) ≡ suc (gd k)
    gdΣ-in k kN rewrite <ℕ-complete k N kN = refl

    pos-deg : ∀ d k → k < N → suc d ≤ gd k → 1 ≤ gd (iter s d k)
    pos-deg d k kN l = subst (1 ≤_) (sym (snd (GK.iter-ok s sN ds d k kN (≤-trans (≤-suc (≤-refl d)) l)))) (go (gd k) d l)
      where
      go : ∀ g d → suc d ≤ g → 1 ≤ g ∸ d
      go (suc g) zero    _       = s≤s z≤n
      go (suc g) (suc d) (s≤s l) = go g d l
    pos-deg-t : ∀ d k → k < N → suc d ≤ gd k → 1 ≤ gd (iter t d k)
    pos-deg-t d k kN l = subst (1 ≤_) (sym (snd (GK.iter-ok t tN dt d k kN (≤-trans (≤-suc (≤-refl d)) l)))) (go (gd k) d l)
      where
      go : ∀ g d → suc d ≤ g → 1 ≤ g ∸ d
      go (suc g) zero    _       = s≤s z≤n
      go (suc g) (suc d) (s≤s l) = go g d l

    -- An element of positive degree goes to 0 under X and Z.
    XZ0 : ∀ p → p < N → 1 ≤ gd p → (lin (unit p) X ≡ 0c) × (lin (unit p) Z ≡ 0c)
    XZ0 p pN l = trans (lin-X p pN) (end-pos e⊥ (gd p) l) , trans (lin-Z p pN) (end-pos e⊤ (gd p) l)

  -- Rows of ⟨k ⊗ i⟩ at depth d ≤ deg k.
  row-mid : ∀ k (kN : k < N) d → d ≤ gd k →
            (lin (fst (CD.A′.entK (k * 3 + 1) d)) Q , lin (snd (CD.A′.entK (k * 3 + 1) d)) Q) ≡ AS.entK (suc k) d
  row-mid k kN d l =
    trans (cong (λ r → (lin (fst r) Q , lin (snd r) Q)) (CD.Mid.claim k kN d (subst (d ≤_) (sym (gk k kN)) l)))
      (trans (cong₂ _,_ (qF (M.P d) (M.pm d) (M.Am d) (fst (pmXZ d l)) (snd (pmXZ d l))) (qG (M.P d) (M.pp d) (M.Ap d) (fst (ppXZ d l)) (snd (ppXZ d l))))
        (trans (cong₂ _,_ (trans (cong (λ v → lin v Y) (cong fst (GK.entK-glob d k kN l))) (lin-Y _ (fst (GK.iter-ok s sN ds d k kN l))))
                          (trans (cong (λ v → lin v Y) (cong snd (GK.entK-glob d k kN l))) (lin-Y _ (fst (GK.iter-ok t tN dt d k kN l)))))
          (sym (trans (GS.entK-glob d (suc k) (s≤s (≤-suc kN)) (subst (d ≤_) (sym (gdΣ-in k kN)) (≤-suc l)))
                 (cong₂ _,_ (cong unit (iterΣ s (GData.s (Σg D)) sΣ-in sN ds d k kN l))
                            (cong unit (iterΣ t (GData.t (Σg D)) tΣ-in tN dt d k kN l)))))))
    where
    module M = CD.Mid k kN
    pmXZ : ∀ d → d ≤ gd k → (lin (M.pm d) X ≡ 0c) × (lin (M.pm d) Z ≡ 0c)
    pmXZ zero    _ = lin-0 X , lin-0 Z
    pmXZ (suc d) l =
      let e = cong fst (GK.entK-glob d k kN (≤-trans (≤-suc (≤-refl d)) l))
          sok = GK.iter-ok s sN ds d k kN (≤-trans (≤-suc (≤-refl d)) l)
          xz = XZ0 _ (fst sok) (pos-deg d k kN l)
      in trans (cong (λ v → lin v X) e) (fst xz) , trans (cong (λ v → lin v Z) e) (snd xz)
    ppXZ : ∀ d → d ≤ gd k → (lin (M.pp d) X ≡ 0c) × (lin (M.pp d) Z ≡ 0c)
    ppXZ zero    _ = lin-0 X , lin-0 Z
    ppXZ (suc d) l =
      let e = cong snd (GK.entK-glob d k kN (≤-trans (≤-suc (≤-refl d)) l))
          tok = GK.iter-ok t tN dt d k kN (≤-trans (≤-suc (≤-refl d)) l)
          xz = XZ0 _ (fst tok) (pos-deg-t d k kN l)
      in trans (cong (λ v → lin v X) e) (fst xz) , trans (cong (λ v → lin v Z) e) (snd xz)

  -- The bottom row of ⟨k ⊗ i⟩ goes to (⊥, ⊤).
  row-bot : ∀ k (kN : k < N) →
            (lin (fst (CD.A′.entK (k * 3 + 1) (suc (AK.deg k)))) Q , lin (snd (CD.A′.entK (k * 3 + 1) (suc (AK.deg k)))) Q)
            ≡ AS.entK (suc k) (suc (gd k))
  row-bot k kN =
    trans (cong (λ r → (lin (fst r) Q , lin (snd r) Q)) M.top)
      (trans (cong₂ _,_ lhs⁻ lhs⁺) (sym rhs))
    where
    module M = CD.Mid k kN
    l = ≤-refl (gd k)
    sok = GK.iter-ok s sN ds (gd k) k kN l
    tok = GK.iter-ok t tN dt (gd k) k kN l
    ∸-self : ∀ n → n ∸ n ≡ 0
    ∸-self zero    = refl
    ∸-self (suc n) = ∸-self n
    s0 : gd (iter s (gd k) k) ≡ 0
    s0 = trans (snd sok) (∸-self (gd k))
    t0 : gd (iter t (gd k) k) ≡ 0
    t0 = trans (snd tok) (∸-self (gd k))
    am : M.Am (AK.deg k) ≡ unit (iter s (gd k) k)
    am = trans (cong (λ d → fst (AK.entK k d)) (gk k kN)) (cong fst (GK.entK-glob (gd k) k kN l))
    ap : M.Ap (AK.deg k) ≡ unit (iter t (gd k) k)
    ap = trans (cong (λ d → snd (AK.entK k d)) (gk k kN)) (cong snd (GK.entK-glob (gd k) k kN l))
    am′ : M.Am (suc (AK.deg k)) ≡ 0c
    am′ = trans (cong (λ d → fst (AK.entK k (suc d))) (gk k kN)) (cong fst (GK.entK-bot k kN))
    ap′ : M.Ap (suc (AK.deg k)) ≡ 0c
    ap′ = trans (cong (λ d → snd (AK.entK k (suc d))) (gk k kN)) (cong snd (GK.entK-bot k kN))
    lhs⁻ : lin (CD.F true (M.Am (AK.deg k)) (M.Am (suc (AK.deg k)))) Q ≡ e⊥
    lhs⁻ = trans (lin-cyl gdeg _ _ _ X Y Z)
             (trans (cong₂ (λ a b → (lin a X +c lin b Y) +c lin 0c Z) am am′)
               (trans (cong₂ (λ p q → (p +c q) +c lin 0c Z) (trans (lin-X _ (fst sok)) (cong (end e⊥) s0)) (lin-0 Y))
                 (trans (cong ((e⊥ +c 0c) +c_) (lin-0 Z)) (trans (+c-comm _ 0c) (trans (+c-id _) (trans (+c-comm _ 0c) (+c-id _)))))))
    lhs⁺ : lin (CD.G true (M.Ap (AK.deg k)) (M.Ap (suc (AK.deg k)))) Q ≡ e⊤
    lhs⁺ = trans (lin-cyl gdeg _ _ _ X Y Z)
             (trans (cong₂ (λ a b → (lin 0c X +c lin b Y) +c lin a Z) ap ap′)
               (trans (cong₂ (λ p q → (p +c q) +c lin (unit (iter t (gd k) k)) Z) (lin-0 X) (lin-0 Y))
                 (trans (cong ((0c +c 0c) +c_) (trans (lin-Z _ (fst tok)) (cong (end e⊤) t0))) (trans (cong (_+c e⊤) (+c-id 0c)) (+c-id e⊤)))))
    rhs : AS.entK (suc k) (suc (gd k)) ≡ (e⊥ , e⊤)
    rhs = trans (GS.entK-glob (suc (gd k)) (suc k) (s≤s (≤-suc kN)) (subst (suc (gd k) ≤_) (sym (gdΣ-in k kN)) (≤-refl _)))
            (cong₂ _,_
              (cong unit (trans (iter-suc (GData.s (Σg D)) (gd k) (suc k))
                 (trans (cong (GData.s (Σg D)) (iterΣ s (GData.s (Σg D)) sΣ-in sN ds (gd k) k kN l))
                        (cong (λ h → if h ==ℕ 0 then 0 else suc (s (iter s (gd k) k))) s0))))
              (cong unit (trans (iter-suc (GData.t (Σg D)) (gd k) (suc k))
                 (trans (cong (GData.t (Σg D)) (iterΣ t (GData.t (Σg D)) tΣ-in tN dt (gd k) k kN l))
                        (cong (λ h → if h ==ℕ 0 then suc N else suc (t (iter t (gd k) k))) t0)))))

  private
    which-1 : ∀ b → which b 1 ≡ Wi
    which-1 true  = refl
    which-1 false = refl

    degC : ∀ k → k < N → CD.A′.deg (k * 3 + 1) ≡ suc (gd k)
    degC k kN =
      trans (at-pick 0 gdeg gdeg (mapV suc gdeg) gdeg k 1 kN (s≤s (s≤s z≤n)))
        (trans (cong (λ w → pick w (g k) (at 0 (mapV suc gdeg) k) (g k)) (which-1 (even (g k))))
               (trans (at-map-lt suc 0 0 gdeg k kN) (cong suc (gk k kN))))

    ∸-le : ∀ g j → g ∸ j ≤ g
    ∸-le zero    zero    = z≤n
    ∸-le zero    (suc j) = z≤n
    ∸-le (suc g) zero    = ≤-refl _
    ∸-le (suc g) (suc j) = ≤-suc (∸-le g j)

  -- ν(q) on rows of ⟨k ⊗ i⟩.
  ent-mid : ∀ k (kN : k < N) j →
            (lin (fst (CD.A′.ent (k * 3 + 1) j)) Q , lin (snd (CD.A′.ent (k * 3 + 1) j)) Q) ≡ AS.ent (suc k) j
  ent-mid k kN j = go (CD.A′.deg (k * 3 + 1)) (AS.deg (suc k)) (degC k kN) (gΣk k kN) j
    where
    go : ∀ n n′ → n ≡ suc (gd k) → n′ ≡ suc (gd k) → ∀ j →
         (lin (fst (if j <ℕ suc n then CD.A′.entK (k * 3 + 1) (n ∸ j) else (0c , 0c))) Q ,
          lin (snd (if j <ℕ suc n then CD.A′.entK (k * 3 + 1) (n ∸ j) else (0c , 0c))) Q)
         ≡ (if j <ℕ suc n′ then AS.entK (suc k) (n′ ∸ j) else (0c , 0c))
    go n n′ refl refl zero = trans (cong (λ d → (lin (fst (CD.A′.entK (k * 3 + 1) (suc d))) Q , lin (snd (CD.A′.entK (k * 3 + 1) (suc d))) Q))
                                          (sym (gk k kN)))
                                   (row-bot k kN)
    go n n′ refl refl (suc j) with j <ℕ suc (gd k)
    ... | true  = row-mid k kN (gd k ∸ j) (∸-le (gd k) j)
    ... | false = cong₂ _,_ (lin-0 Q) (lin-0 Q)

  private
    mapT-tabF : ∀ L′ {m} (f : Nat → Vec Nat (N * 3) × Vec Nat (N * 3)) j →
                mapT q L′ (Atom.tabF B′ {m} f j) ≡ Atom.tabF S.basis {m} (λ i → lin (fst (f i)) Q , lin (snd (f i)) Q) j
    mapT-tabF L′ {zero}  f j = refl
    mapT-tabF L′ {suc m} f j = cong (_ ∷_) (mapT-tabF L′ {m} f (suc j))

    tabF-cong : ∀ {m} (f g : Nat → Chn NS × Chn NS) → (∀ i → f i ≡ g i) → ∀ j →
                Atom.tabF S.basis {m} f j ≡ Atom.tabF S.basis {m} g j
    tabF-cong {zero}  f g h j = refl
    tabF-cong {suc m} f g h j = cong₂ _∷_ (h j) (tabF-cong {m} f g h (suc j))

  -- ν(q)⟨k ⊗ i⟩ = ⟨Σk⟩, as tables.
  atom-mid : ∀ L k → k < N → mapT q L (Atom.atomT B′ L (k * 3 + 1)) ≡ Atom.atomT S.basis L (suc k)
  atom-mid L k kN = trans (mapT-tabF L (CD.A′.ent (k * 3 + 1)) 0) (tabF-cong _ _ (ent-mid k kN) 0)
