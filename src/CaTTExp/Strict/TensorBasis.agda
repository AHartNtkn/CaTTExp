------------------------------------------------------------------------
-- The Gray tensor K ⊗ L of two finite bases (ledger A5, (N3)).
--
-- The basis of K ⊗ L is k⊗l for k in K, l in L, of degree
-- deg k + deg l, with the Leibniz rule (Steiner 2004 §7)
--     ∂^α(k⊗l) = ∂^α k ⊗ l + k ⊗ ∂^{(−1)^{deg k} α} l.
-- A chain is a matrix X (row k, column l). In matrix form
--     ∂^α X = osum (∂^α_K) X + rowD α X     (`Tensor.D`),
-- where `osum F X = Σ_k F k ⊗ X k` applies ∂_K to the columns and
-- `rowD α` applies ∂^α_L to the rows of even degree and ∂^{−α}_L to the
-- rows of odd degree.
--
-- For finite bases K, L satisfying `Hyp` whose boundaries have the
-- right degrees (`DegP`, `DegM`):
--   `dd⊗`   ∂∂ = 0; the Koszul sign is `rowD-osum`: moving a column
--           boundary past a row boundary flips it, since ∂_K lowers
--           degrees by one;
--   `deg⊗`  ∂ lowers degrees by one (`SupM`: row k sits in L-degree
--           j − deg k);
--   `aug⊗`  ε∂⁺ = ε∂⁻ on 1-chains.
-- The layout `TensorLay.B⊗` lists block k = the row k⊗l, in the order
-- of L when deg k is even and reversed when deg k is odd (as in
-- `Cylinder`; `square-is-cyl`, `D²⊗D¹-is-cyl` check that L = λD¹ gives
-- the cylinder exactly). `TensorHyp` carries ∂∂ = 0, degrees and
-- augmentation over to the layout, and `TensorOrd` proves its order
-- (negative faces before, positive faces after: ∂⁻ of k⊗l lives in
-- earlier blocks ∂⁻k⊗l and in block k at k⊗∂^{∓}l, which comes earlier
-- in either direction of the block). So `TensorAll.hyp⊗` gives
-- `Hyp (K ⊗ L)` from unitality of its atoms alone. Unitality
-- (Steiner's ⟨k⊗l⟩ = ⟨k⟩⊗⟨l⟩) is not proved here in general; for
-- λD¹ ⊗ λD² and λD² ⊗ λD² it is checked, with the rest, by the
-- decision procedures of `BasisCheck`.
------------------------------------------------------------------------
module CaTTExp.Strict.TensorBasis where

open import CaTTExp.Prelude
open import Agda.Builtin.Nat using (_*_)
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; ≤-refl; ≤-trans; ≤-suc; <→≤; ≤-<-⊥)
open import CaTTExp.Strict.Tables using (CMon; Vec; []; _∷_)
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms using (at; unit)
open import CaTTExp.Strict.Generation using (Hyp; dP; dM; at0; at-0c; Lo; Hi; ≤-dec; ≤-pred)
open import CaTTExp.Strict.BasisCheck using (mapV; zipV; at-zip; at-map; ⊙-distrib; ⊙-0c; lin-⊙; lin-lin; DegP; DegM; degFix)
open import CaTTExp.Strict.Cylinder using (even; even-suc; units; lin-units; lin-hom; at-units)
open import CaTTExp.Strict.GlobBasis using (vextV)
open import CaTTExp.Strict.CMonSolver
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Matrices.

Mat : Nat → Nat → Set
Mat N M = Vec (Vec Nat M) N

0m : ∀ {N M} → Mat N M
0m {zero}  = []
0m {suc N} = 0c ∷ 0m

infixl 6 _+m_
_+m_ : ∀ {N M} → Mat N M → Mat N M → Mat N M
[]      +m []      = []
(x ∷ X) +m (y ∷ Y) = (x +c y) ∷ (X +m Y)

+m-id : ∀ {N M} (X : Mat N M) → 0m +m X ≡ X
+m-id []      = refl
+m-id (x ∷ X) = cong₂ _∷_ (+c-id x) (+m-id X)

+m-comm : ∀ {N M} (X Y : Mat N M) → X +m Y ≡ Y +m X
+m-comm []      []      = refl
+m-comm (x ∷ X) (y ∷ Y) = cong₂ _∷_ (+c-comm x y) (+m-comm X Y)

+m-assoc : ∀ {N M} (X Y Z : Mat N M) → (X +m Y) +m Z ≡ X +m (Y +m Z)
+m-assoc []      []      []      = refl
+m-assoc (x ∷ X) (y ∷ Y) (z ∷ Z) = cong₂ _∷_ (+c-assoc x y z) (+m-assoc X Y Z)

matMon : Nat → Nat → CMon
matMon N M = record
  { M = Mat N M ; ε = 0m ; _⊕_ = _+m_
  ; ⊕-id = +m-id ; ⊕-comm = +m-comm ; ⊕-assoc = +m-assoc }

private
  r0m : ∀ {N M} (X : Mat N M) → X +m 0m ≡ X
  r0m X = trans (+m-comm X 0m) (+m-id X)

  mid : ∀ {N M} (a b c d : Mat N M) → (a +m b) +m (c +m d) ≡ (a +m c) +m (b +m d)
  mid {N} {M} a b c d = solve ((` 0 ⊞ ` 1) ⊞ (` 2 ⊞ ` 3)) ((` 0 ⊞ ` 2) ⊞ (` 1 ⊞ ` 3)) (lk (a ∷ b ∷ c ∷ d ∷ [])) tt
    where open Solver (matMon N M)

-- outer f x : row k′ is f k′ ⊙ x.
outer : ∀ {N M} → Vec Nat N → Vec Nat M → Mat N M
outer f x = mapV (λ a → a ⊙ x) f

outer-0l : ∀ {N M} (x : Vec Nat M) → outer (0c {N}) x ≡ 0m
outer-0l {zero}  x = refl
outer-0l {suc N} x = cong (0c ∷_) (outer-0l {N} x)

outer-+l : ∀ {N M} (u v : Vec Nat N) (x : Vec Nat M) → outer (u +c v) x ≡ outer u x +m outer v x
outer-+l []      []      x = refl
outer-+l (a ∷ u) (b ∷ v) x = cong₂ _∷_ (⊙-+ a b x) (outer-+l u v x)

outer-0r : ∀ {N M} (f : Vec Nat N) → outer f (0c {M}) ≡ 0m
outer-0r []      = refl
outer-0r (a ∷ f) = cong₂ _∷_ (⊙-0c a) (outer-0r f)

outer-+r : ∀ {N M} (f : Vec Nat N) (x y : Vec Nat M) → outer f (x +c y) ≡ outer f x +m outer f y
outer-+r []      x y = refl
outer-+r (a ∷ f) x y = cong₂ _∷_ (⊙-distrib a x y) (outer-+r f x y)

outer-⊙ : ∀ {N M} k (f : Vec Nat N) (x : Vec Nat M) → outer f (k ⊙ x) ≡ outer (k ⊙ f) x
outer-⊙ zero    f x = trans (outer-0r f) (sym (outer-0l x))
outer-⊙ (suc k) f x = trans (outer-+r f x (k ⊙ x)) (trans (cong (outer f x +m_) (outer-⊙ k f x)) (sym (outer-+l f (k ⊙ f) x)))

-- osum F X = Σ_k F k ⊗ X k.
osum : ∀ {N P M} → Vec (Vec Nat N) P → Mat P M → Mat N M
osum []      []      = 0m
osum (f ∷ F) (x ∷ X) = outer f x +m osum F X

osum-0 : ∀ {N P M} (F : Vec (Vec Nat N) P) → osum F (0m {P} {M}) ≡ 0m
osum-0 []      = refl
osum-0 (f ∷ F) = trans (cong₂ _+m_ (outer-0r f) (osum-0 F)) (+m-id 0m)

osum-+ : ∀ {N P M} (F : Vec (Vec Nat N) P) (X Y : Mat P M) → osum F (X +m Y) ≡ osum F X +m osum F Y
osum-+ []      []      []      = sym (+m-id 0m)
osum-+ (f ∷ F) (x ∷ X) (y ∷ Y) =
  trans (cong₂ _+m_ (outer-+r f x y) (osum-+ F X Y)) (mid (outer f x) (outer f y) (osum F X) (osum F Y))

osum-+F : ∀ {N P M} (F G : Vec (Vec Nat N) P) (X : Mat P M) → osum (zipV _+c_ F G) X ≡ osum F X +m osum G X
osum-+F []      []      []      = sym (+m-id 0m)
osum-+F (f ∷ F) (g ∷ G) (x ∷ X) =
  trans (cong₂ _+m_ (outer-+l f g x) (osum-+F F G X)) (mid (outer f x) (outer g x) (osum F X) (osum G X))

osum-outer : ∀ {N P M} (F : Vec (Vec Nat N) P) (g : Vec Nat P) (x : Vec Nat M) → osum F (outer g x) ≡ outer (lin g F) x
osum-outer []      []      x = sym (outer-0l x)
osum-outer (f ∷ F) (a ∷ g) x =
  trans (cong₂ _+m_ (outer-⊙ a f x) (osum-outer F g x)) (sym (outer-+l (a ⊙ f) (lin g F) x))

osum-osum : ∀ {N P Q M} (F : Vec (Vec Nat N) P) (G : Vec (Vec Nat P) Q) (X : Mat Q M) →
            osum F (osum G X) ≡ osum (mapV (λ g → lin g F) G) X
osum-osum F []      []      = osum-0 F
osum-osum F (g ∷ G) (x ∷ X) = trans (osum-+ F (outer g x) (osum G X)) (cong₂ _+m_ (osum-outer F g x) (osum-osum F G X))

------------------------------------------------------------------------
-- Rows.

-- sg b α: the sign of the row boundary on a row of parity b.
sg : Bool → Bool → Bool
sg b α = if b then α else not α

-- rowW gs h X: row k ↦ lin (X k) (h (sg (even (gs k)) α)).
rowW : ∀ {N M} → Vec Nat N → (Bool → Vec (Vec Nat M) M) → Bool → Mat N M → Mat N M
rowW gs h α X = zipV (λ g x → lin x (h (sg (even g) α))) gs X

rowW-+ : ∀ {N M} (gs : Vec Nat N) h α (X Y : Mat N M) → rowW gs h α (X +m Y) ≡ rowW gs h α X +m rowW gs h α Y
rowW-+ []       h α []      []      = refl
rowW-+ (g ∷ gs) h α (x ∷ X) (y ∷ Y) = cong₂ _∷_ (lin-+ x y (h (sg (even g) α))) (rowW-+ gs h α X Y)

rowW-0 : ∀ {N M} (gs : Vec Nat N) h α → rowW gs h α (0m {N} {M}) ≡ 0m
rowW-0 []       h α = refl
rowW-0 (g ∷ gs) h α = cong₂ _∷_ (lin-0 (h (sg (even g) α))) (rowW-0 gs h α)

private
  not-not : ∀ b → not (not b) ≡ b
  not-not true  = refl
  not-not false = refl

  sg-flip : ∀ b α → sg (not b) α ≡ sg b (not α)
  sg-flip true  α = refl
  sg-flip false α = sym (not-not α)

-- Rows of f-parity opposite to b: rowW on outer f x flips the sign.
outer-row : ∀ {N M} (gs : Vec Nat N) h α (f : Vec Nat N) (x : Vec Nat M) b →
            (∀ k → at 0 f k ≡ 0 ⊎ even (at 0 gs k) ≡ not b) →
            rowW gs h α (outer f x) ≡ outer f (lin x (h (sg b (not α))))
outer-row []       h α []      x b p = refl
outer-row (g ∷ gs) h α (a ∷ f) x b p =
  cong₂ _∷_ (trans (lin-⊙ a x (h (sg (even g) α))) (hd (p 0))) (outer-row gs h α f x b (λ k → p (suc k)))
  where
  hd : (a ≡ 0) ⊎ (even g ≡ not b) → a ⊙ lin x (h (sg (even g) α)) ≡ a ⊙ lin x (h (sg b (not α)))
  hd (inj₁ refl) = refl
  hd (inj₂ e)    = cong (λ s → a ⊙ lin x (h s)) (trans (cong (λ c → sg c α) e) (sg-flip b α))

-- F k has parity opposite to gs′ k.
rowW-osum : ∀ {N P M} (gs : Vec Nat N) (gs′ : Vec Nat P) h α (F : Vec (Vec Nat N) P) (X : Mat P M) →
            (∀ k → k < P → ∀ k′ → at 0 (at 0c F k) k′ ≡ 0 ⊎ even (at 0 gs k′) ≡ not (even (at 0 gs′ k))) →
            rowW gs h α (osum F X) ≡ osum F (rowW gs′ h (not α) X)
rowW-osum gs []        h α []      []      p = rowW-0 gs h α
rowW-osum gs (g′ ∷ gs′) h α (f ∷ F) (x ∷ X) p =
  trans (rowW-+ gs h α (outer f x) (osum F X))
    (cong₂ _+m_ (outer-row gs h α f x (even g′) (p 0 (s≤s z≤n)))
                (rowW-osum gs gs′ h α F X (λ k l → p (suc k) (s≤s l))))

------------------------------------------------------------------------
-- The tensor of two bases.

module Tensor {N M : Nat} (B : Basis N) (C : Basis M) where
  private
    module B = Basis B
    module C = Basis C

  bK : Bool → Vec (Vec Nat N) N
  bK true  = B.bplus
  bK false = B.bminus

  bL : Bool → Vec (Vec Nat M) M
  bL true  = C.bplus
  bL false = C.bminus

  rowD : Bool → Mat N M → Mat N M
  rowD = rowW B.gdeg bL

  -- ∂^α on chains of K ⊗ L.
  D : Bool → Mat N M → Mat N M
  D α X = osum (bK α) X +m rowD α X

  D-+ : ∀ α X Y → D α (X +m Y) ≡ D α X +m D α Y
  D-+ α X Y = trans (cong₂ _+m_ (osum-+ (bK α) X Y) (rowW-+ B.gdeg bL α X Y))
                    (mid (osum (bK α) X) (osum (bK α) Y) (rowD α X) (rowD α Y))

  D-0 : ∀ α → D α 0m ≡ 0m
  D-0 α = trans (cong₂ _+m_ (osum-0 (bK α)) (rowW-0 B.gdeg bL α)) (+m-id 0m)

------------------------------------------------------------------------
-- ∂∂ = 0.

module TensorDD {N M : Nat} (B : Basis N) (C : Basis M) (HB : Hyp B) (HC : Hyp C)
                (dgp : DegP B) (dgm : DegM B) where
  open Tensor B C
  private
    module B = Basis B
    module C = Basis C

    lin-unit : ∀ {P m} i → i < m → (vs : Vec (Vec Nat P) m) → lin (unit {m} i) vs ≡ at 0c vs i
    lin-unit {P} {suc m} zero    _       (v ∷ vs) =
      trans (cong₂ _+c_ (trans (+c-comm v 0c) (+c-id v)) (lin-0 vs)) (trans (+c-comm v 0c) (+c-id v))
    lin-unit {P} {suc m} (suc i) (s≤s l) (v ∷ vs) = trans (+c-id (lin (unit {m} i) vs)) (lin-unit i l vs)

    at-prj : ∀ {m} j (gs v : Vec Nat m) k → at 0 (prj j gs v) k ≡ (if at 0 gs k ==ℕ j then at 0 v k else 0)
    at-prj j []       []      k       = sym (if0 (0 ==ℕ j))
      where
      if0 : ∀ b → (if b then 0 else 0) ≡ 0
      if0 true  = refl
      if0 false = refl
    at-prj j (g ∷ gs) (a ∷ v) zero    = refl
    at-prj j (g ∷ gs) (a ∷ v) (suc k) = at-prj j gs v k

    ==-sound : ∀ m n → (m ==ℕ n) ≡ true → m ≡ n
    ==-sound zero    zero    _ = refl
    ==-sound (suc m) (suc n) e = cong suc (==-sound m n e)
    ==-sound zero    (suc n) ()
    ==-sound (suc m) zero    ()

    -- Entries of degFix g v sit in degree g − 1, so their parity is not that of g.
    fix-par : ∀ g (v : Vec Nat N) k → at 0 (degFix B g v) k ≡ 0 ⊎ even (at 0 B.gdeg k) ≡ not (even g)
    fix-par zero    v k = inj₁ (at-0c {N} k)
    fix-par (suc g) v k = go (at 0 B.gdeg k ==ℕ g) refl
      where
      go : ∀ b → (at 0 B.gdeg k ==ℕ g) ≡ b → at 0 (prj g B.gdeg v) k ≡ 0 ⊎ even (at 0 B.gdeg k) ≡ not (even (suc g))
      go true  e = inj₂ (trans (cong even (==-sound (at 0 B.gdeg k) g e)) (sym (trans (cong not (even-suc g)) (not-not (even g)))))
      go false e = inj₁ (trans (at-prj g B.gdeg v k) (cong (λ b → if b then at 0 v k else 0) e))

    par : ∀ (bs : Vec (Vec Nat N) N) → zipV (degFix B) B.gdeg bs ≡ bs →
          ∀ k → k < N → ∀ k′ → at 0 (at 0c bs k) k′ ≡ 0 ⊎ even (at 0 B.gdeg k′) ≡ not (even (at 0 B.gdeg k))
    par bs E k kN k′ = subst (λ w → at 0 w k′ ≡ 0 ⊎ even (at 0 B.gdeg k′) ≡ not (even (at 0 B.gdeg k)))
                             (trans (sym (at-zip (degFix B) 0 0c 0c refl B.gdeg bs k)) (cong (λ V → at 0c V k) E))
                             (fix-par (at 0 B.gdeg k) (at 0c bs k) k′)

  parK : ∀ β → ∀ k → k < N → ∀ k′ → at 0 (at 0c (bK β) k) k′ ≡ 0 ⊎ even (at 0 B.gdeg k′) ≡ not (even (at 0 B.gdeg k))
  parK true  = par B.bplus dgp
  parK false = par B.bminus dgm

  -- The Koszul sign.
  rowD-osum : ∀ α β (X : Mat N M) → rowD α (osum (bK β) X) ≡ osum (bK β) (rowD (not α) X)
  rowD-osum α β X = rowW-osum B.gdeg B.gdeg bL α (bK β) X (parK β)

  -- ∂∂ = 0 on columns, from ∂∂ = 0 in K.
  osum-dd : ∀ (X : Mat N M) → osum B.bplus (osum B.bplus X) +m osum B.bminus (osum B.bminus X) ≡
                  osum B.bplus (osum B.bminus X) +m osum B.bminus (osum B.bplus X)
  osum-dd X =
    trans (cong₂ _+m_ (osum-osum B.bplus B.bplus X) (osum-osum B.bminus B.bminus X))
    (trans (sym (osum-+F (mapV (λ g → lin g B.bplus) B.bplus) (mapV (λ g → lin g B.bminus) B.bminus) X))
    (trans (cong (λ F → osum F X) fam)
    (trans (osum-+F (mapV (λ g → lin g B.bplus) B.bminus) (mapV (λ g → lin g B.bminus) B.bplus) X)
           (sym (cong₂ _+m_ (osum-osum B.bplus B.bminus X) (osum-osum B.bminus B.bplus X))))))
    where
    fam : zipV _+c_ (mapV (λ g → lin g B.bplus) B.bplus) (mapV (λ g → lin g B.bminus) B.bminus) ≡
          zipV _+c_ (mapV (λ g → lin g B.bplus) B.bminus) (mapV (λ g → lin g B.bminus) B.bplus)
    fam = vextV 0c _ _ λ i l →
      trans (at-zip _+c_ 0c 0c 0c (+c-id 0c) (mapV (λ g → lin g B.bplus) B.bplus) (mapV (λ g → lin g B.bminus) B.bminus) i)
      (trans (cong₂ _+c_ (at-mp B.bplus B.bplus i) (at-mp B.bminus B.bminus i))
      (trans (cong₂ _+c_ (cong (λ v → lin v B.bplus) (sym (lin-unit i l B.bplus)))
                         (cong (λ v → lin v B.bminus) (sym (lin-unit i l B.bminus))))
      (trans (Hyp.dd HB (unit i))
      (trans (cong₂ _+c_ (cong (λ v → lin v B.bplus) (lin-unit i l B.bminus))
                         (cong (λ v → lin v B.bminus) (lin-unit i l B.bplus)))
      (trans (sym (cong₂ _+c_ (at-mp B.bplus B.bminus i) (at-mp B.bminus B.bplus i)))
             (sym (at-zip _+c_ 0c 0c 0c (+c-id 0c) (mapV (λ g → lin g B.bplus) B.bminus) (mapV (λ g → lin g B.bminus) B.bplus) i)))))))
      where
      at-mp : ∀ (F G : Vec (Vec Nat N) N) i → at 0c (mapV (λ g → lin g F) G) i ≡ lin (at 0c G i) F
      at-mp F G i = at-map (λ g → lin g F) 0c 0c (lin-0 F) G i

  -- ∂∂ = 0 on rows, from ∂∂ = 0 in L.
  rowD-dd : ∀ (X : Mat N M) → rowD true (rowD true X) +m rowD false (rowD false X) ≡ rowD true (rowD false X) +m rowD false (rowD true X)
  rowD-dd X = go B.gdeg X
    where
    ddL : ∀ x → lin (lin x C.bplus) C.bplus +c lin (lin x C.bminus) C.bminus ≡ lin (lin x C.bminus) C.bplus +c lin (lin x C.bplus) C.bminus
    ddL x = Hyp.dd HC x
    go : ∀ {P} (gs : Vec Nat P) (X : Mat P M) →
         rowW gs bL true (rowW gs bL true X) +m rowW gs bL false (rowW gs bL false X) ≡
         rowW gs bL true (rowW gs bL false X) +m rowW gs bL false (rowW gs bL true X)
    go []       []      = refl
    go (g ∷ gs) (x ∷ X) = cong₂ _∷_ (row (even g)) (go gs X)
      where
      row : ∀ b → lin (lin x (bL (sg b true))) (bL (sg b true)) +c lin (lin x (bL (sg b false))) (bL (sg b false)) ≡
                  lin (lin x (bL (sg b false))) (bL (sg b true)) +c lin (lin x (bL (sg b true))) (bL (sg b false))
      row true  = ddL x
      row false = trans (+c-comm _ _) (trans (ddL x) (+c-comm _ _))

  dd⊗ : ∀ (X : Mat N M) → D true (D true X) +m D false (D false X) ≡ D true (D false X) +m D false (D true X)
  dd⊗ X =
    trans (cong₂ _+m_ (ex true true) (ex false false))
    (trans (solve LHS (cc⁺ ⊞ (cr ⊞ rr⁺)) (lk ρ) tt)
    (trans (cong₂ (λ a b → a +m (cr′ +m b)) (osum-dd X) (rowD-dd X))
    (trans (solve (cc⁻ ⊞ (cr ⊞ rr⁻)) RHS (lk ρ) tt)
           (sym (cong₂ _+m_ (ex true false) (ex false true))))))
    where
    open Solver (matMon N M)
    -- D α (D β X), expanded.
    ex : ∀ α β → D α (D β X) ≡ ((osum (bK α) (osum (bK β) X) +m osum (bK α) (rowD β X)) +m
                               (osum (bK β) (rowD (not α) X) +m rowD α (rowD β X)))
    ex α β =
      trans (D-+ α (osum (bK β) X) (rowD β X))
        (trans (mid (osum (bK α) (osum (bK β) X)) (rowD α (osum (bK β) X)) (osum (bK α) (rowD β X)) (rowD α (rowD β X)))
               (cong (λ z → (osum (bK α) (osum (bK β) X) +m osum (bK α) (rowD β X)) +m (z +m rowD α (rowD β X)))
                     (rowD-osum α β X)))
    -- atoms: 0 c⁺c⁺, 1 c⁻c⁻, 2 c⁺c⁻, 3 c⁻c⁺, 4 c⁺R⁺, 5 c⁺R⁻, 6 c⁻R⁺, 7 c⁻R⁻, 8 R⁺R⁺, 9 R⁻R⁻, 10 R⁺R⁻, 11 R⁻R⁺
    ρ = osum B.bplus (osum B.bplus X) ∷ osum B.bminus (osum B.bminus X) ∷
        osum B.bplus (osum B.bminus X) ∷ osum B.bminus (osum B.bplus X) ∷
        osum B.bplus (rowD true X) ∷ osum B.bplus (rowD false X) ∷
        osum B.bminus (rowD true X) ∷ osum B.bminus (rowD false X) ∷
        rowD true (rowD true X) ∷ rowD false (rowD false X) ∷
        rowD true (rowD false X) ∷ rowD false (rowD true X) ∷ []
    LHS = ((` 0 ⊞ ` 4) ⊞ (` 5 ⊞ ` 8)) ⊞ ((` 1 ⊞ ` 7) ⊞ (` 6 ⊞ ` 9))
    RHS = ((` 2 ⊞ ` 5) ⊞ (` 7 ⊞ ` 10)) ⊞ ((` 3 ⊞ ` 6) ⊞ (` 4 ⊞ ` 11))
    cc⁺ = ` 0 ⊞ ` 1
    cc⁻ = ` 2 ⊞ ` 3
    rr⁺ = ` 8 ⊞ ` 9
    rr⁻ = ` 10 ⊞ ` 11
    cr  = (` 4 ⊞ ` 5) ⊞ (` 6 ⊞ ` 7)
    cr′ = (osum B.bplus (rowD true X) +m osum B.bplus (rowD false X)) +m (osum B.bminus (rowD true X) +m osum B.bminus (rowD false X))

------------------------------------------------------------------------
-- Supports: v vanishes outside the generators whose degree satisfies P.

Sup : ∀ {m} → (Nat → Set) → Vec Nat m → Vec Nat m → Set
Sup P gs v = ∀ i → at 0 v i ≡ 0 ⊎ P (at 0 gs i)

private
  at-+c : ∀ {m} (u v : Vec Nat m) i → at 0 (u +c v) i ≡ at 0 u i + at 0 v i
  at-+c []      []      i       = refl
  at-+c (a ∷ u) (b ∷ v) zero    = refl
  at-+c (a ∷ u) (b ∷ v) (suc i) = at-+c u v i

  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

sup-0 : ∀ {m} P (gs : Vec Nat m) → Sup P gs 0c
sup-0 {m} P gs i = inj₁ (at-0c {m} i)

sup-+ : ∀ {m} P (gs u v : Vec Nat m) → Sup P gs u → Sup P gs v → Sup P gs (u +c v)
sup-+ P gs u v su sv i = go (su i) (sv i)
  where
  go : at 0 u i ≡ 0 ⊎ P (at 0 gs i) → at 0 v i ≡ 0 ⊎ P (at 0 gs i) → at 0 (u +c v) i ≡ 0 ⊎ P (at 0 gs i)
  go (inj₁ a) (inj₁ b) = inj₁ (trans (at-+c u v i) (cong₂ _+_ a b))
  go (inj₂ p) _        = inj₂ p
  go (inj₁ _) (inj₂ p) = inj₂ p

sup-⊙ : ∀ {m} P (gs v : Vec Nat m) a → Sup P gs v → Sup P gs (a ⊙ v)
sup-⊙ P gs v zero    s = sup-0 P gs
sup-⊙ P gs v (suc a) s = sup-+ P gs v (a ⊙ v) s (sup-⊙ P gs v a s)

sup-lin : ∀ {m n} P (gs : Vec Nat m) (x : Vec Nat n) (vs : Vec (Vec Nat m) n) →
          (∀ i → at 0 x i ≡ 0 ⊎ Sup P gs (at 0c vs i)) → Sup P gs (lin x vs)
sup-lin P gs []      []       h = sup-0 P gs
sup-lin P gs (a ∷ x) (v ∷ vs) h = sup-+ P gs (a ⊙ v) (lin x vs) (hd (h 0)) (sup-lin P gs x vs (λ i → h (suc i)))
  where
  hd : a ≡ 0 ⊎ Sup P gs v → Sup P gs (a ⊙ v)
  hd (inj₁ refl) = sup-0 P gs
  hd (inj₂ s)    = sup-⊙ P gs v a s

sup-mono : ∀ {m} (P Q : Nat → Set) (gs v : Vec Nat m) → (∀ g → P g → Q g) → Sup P gs v → Sup Q gs v
sup-mono P Q gs v f s i with s i
... | inj₁ z = inj₁ z
... | inj₂ p = inj₂ (f _ p)

-- With DegP/DegM, the boundary of generator k sits in degree deg k − 1.
supFix : ∀ {N} (B : Basis N) (bs : Vec (Vec Nat N) N) → zipV (degFix B) (Basis.gdeg B) bs ≡ bs →
         ∀ k → Sup (λ g → suc g ≡ at 0 (Basis.gdeg B) k) (Basis.gdeg B) (at 0c bs k)
supFix {N} B bs E k k′ =
  subst (λ w → at 0 w k′ ≡ 0 ⊎ suc (at 0 gs k′) ≡ at 0 gs k)
        (trans (sym (at-zip (degFix B) 0 0c 0c refl gs bs k)) (cong (λ V → at 0c V k) E))
        (fx (at 0 gs k) (at 0c bs k))
  where
  gs = Basis.gdeg B
  ==-sound : ∀ m n → (m ==ℕ n) ≡ true → m ≡ n
  ==-sound zero    zero    _ = refl
  ==-sound (suc m) (suc n) e = cong suc (==-sound m n e)
  ==-sound zero    (suc n) ()
  ==-sound (suc m) zero    ()
  at-prj : ∀ {m} j (hs v : Vec Nat m) i → at 0 (prj j hs v) i ≡ (if at 0 hs i ==ℕ j then at 0 v i else 0)
  at-prj j []       []      i       = sym (if0 (0 ==ℕ j))
    where
    if0 : ∀ b → (if b then 0 else 0) ≡ 0
    if0 true  = refl
    if0 false = refl
  at-prj j (h ∷ hs) (a ∷ v) zero    = refl
  at-prj j (h ∷ hs) (a ∷ v) (suc i) = at-prj j hs v i
  fx : ∀ g v → at 0 (degFix B g v) k′ ≡ 0 ⊎ suc (at 0 gs k′) ≡ g
  fx zero    v = inj₁ (at-0c {N} k′)
  fx (suc g) v = go (at 0 gs k′ ==ℕ g) refl
    where
    go : ∀ b → (at 0 gs k′ ==ℕ g) ≡ b → at 0 (prj g gs v) k′ ≡ 0 ⊎ suc (at 0 gs k′) ≡ suc g
    go true  e = inj₂ (cong suc (==-sound (at 0 gs k′) g e))
    go false e = inj₁ (trans (at-prj g gs v k′) (cong (λ b → if b then at 0 v k′ else 0) e))

------------------------------------------------------------------------
-- Degrees: ∂ lowers the degree of a chain of K ⊗ L by one.

-- Row k of X sits in L-degree j − deg k.
SupM : ∀ {N M} → Vec Nat N → Vec Nat M → Nat → Mat N M → Set
SupM gK gL j X = ∀ k → Sup (λ h → at 0 gK k + h ≡ j) gL (at 0c X k)

private
  at-+m : ∀ {N M} (X Y : Mat N M) k → at 0c (X +m Y) k ≡ at 0c X k +c at 0c Y k
  at-+m []      []      k       = sym (+c-id 0c)
  at-+m (x ∷ X) (y ∷ Y) zero    = refl
  at-+m (x ∷ X) (y ∷ Y) (suc k) = at-+m X Y k

  at-0m : ∀ {N M} k → at 0c (0m {N} {M}) k ≡ 0c
  at-0m {zero}  k       = refl
  at-0m {suc N} zero    = refl
  at-0m {suc N} (suc k) = at-0m {N} k

supM-0 : ∀ {N M} (gK : Vec Nat N) (gL : Vec Nat M) j → SupM gK gL j 0m
supM-0 {N} gK gL j k = subst (Sup (λ h → at 0 gK k + h ≡ j) gL) (sym (at-0m {N} k)) (sup-0 (λ h → at 0 gK k + h ≡ j) gL)

supM-+ : ∀ {N M} (gK : Vec Nat N) (gL : Vec Nat M) j X Y → SupM gK gL j X → SupM gK gL j Y → SupM gK gL j (X +m Y)
supM-+ gK gL j X Y sx sy k = subst (Sup (λ h → at 0 gK k + h ≡ j) gL) (sym (at-+m X Y k)) (sup-+ (λ h → at 0 gK k + h ≡ j) gL (at 0c X k) (at 0c Y k) (sx k) (sy k))

-- f in degree g − 1 and x in L-degree j + 1 − g: outer f x in degree j.
supM-outer : ∀ {N M} (gK : Vec Nat N) (gL : Vec Nat M) j g (f : Vec Nat N) (x : Vec Nat M) →
             Sup (λ g′ → suc g′ ≡ g) gK f → Sup (λ h → g + h ≡ suc j) gL x → SupM gK gL j (outer f x)
supM-outer gK gL j g f x sf sx k =
  subst (Sup (λ h → at 0 gK k + h ≡ j) gL) (sym (at-map (λ a → a ⊙ x) 0 0c refl f k)) (go (sf k))
  where
  go : at 0 f k ≡ 0 ⊎ suc (at 0 gK k) ≡ g → Sup (λ h → at 0 gK k + h ≡ j) gL (at 0 f k ⊙ x)
  go (inj₁ z) = subst (λ a → Sup (λ h → at 0 gK k + h ≡ j) gL (a ⊙ x)) (sym z) (sup-0 (λ h → at 0 gK k + h ≡ j) gL)
  go (inj₂ e) = sup-⊙ (λ h → at 0 gK k + h ≡ j) gL x (at 0 f k) (sup-mono (λ h → g + h ≡ suc j) (λ h → at 0 gK k + h ≡ j) gL x (λ h p → suc-inj (trans (cong (_+ h) e) p)) sx)

supM-osum : ∀ {N P M} (gK : Vec Nat N) (gL : Vec Nat M) j (gs′ : Vec Nat P) (F : Vec (Vec Nat N) P) (X : Mat P M) →
            (∀ k → Sup (λ g′ → suc g′ ≡ at 0 gs′ k) gK (at 0c F k)) →
            (∀ k → Sup (λ h → at 0 gs′ k + h ≡ suc j) gL (at 0c X k)) →
            SupM gK gL j (osum F X)
supM-osum gK gL j []         []      []      sF sX = supM-0 gK gL j
supM-osum gK gL j (g ∷ gs′) (f ∷ F) (x ∷ X) sF sX =
  supM-+ gK gL j (outer f x) (osum F X) (supM-outer gK gL j g f x (sF 0) (sX 0))
         (supM-osum gK gL j gs′ F X (λ k → sF (suc k)) (λ k → sX (suc k)))

-- Rows: x in L-degree j + 1 − g, and ∂_L lowers L-degrees by one.
supM-row : ∀ {N M} (gK : Vec Nat N) (gL : Vec Nat M) j (bs : Bool → Vec (Vec Nat M) M) α (X : Mat N M) →
           (∀ σ l → Sup (λ h′ → suc h′ ≡ at 0 gL l) gL (at 0c (bs σ) l)) →
           SupM gK gL (suc j) X → SupM gK gL j (rowW gK bs α X)
supM-row gK gL j bs α X sb sX = go gK X sX
  where
  go : ∀ {P} (hs : Vec Nat P) (Y : Mat P _) → SupM hs gL (suc j) Y → SupM hs gL j (rowW hs bs α Y)
  go []       []      s k       = subst (Sup (λ h′ → at 0 [] k + h′ ≡ j) gL) (sym (at-0m {0} k)) (sup-0 (λ h′ → at 0 [] k + h′ ≡ j) gL)
  go (h ∷ hs) (y ∷ Y) s zero    =
    sup-lin (λ h′ → h + h′ ≡ j) gL y (bs (sg (even h) α)) λ l → step l (s 0 l)
    where
    step : ∀ l → at 0 y l ≡ 0 ⊎ h + at 0 gL l ≡ suc j → at 0 y l ≡ 0 ⊎ Sup (λ h′ → h + h′ ≡ j) gL (at 0c (bs (sg (even h) α)) l)
    step l (inj₁ z) = inj₁ z
    step l (inj₂ e) = inj₂ (sup-mono (λ h′ → suc h′ ≡ at 0 gL l) (λ h′ → h + h′ ≡ j) gL (at 0c (bs (sg (even h) α)) l) (λ h′ p → suc-inj (trans (sym (+-suc′ h h′)) (trans (cong (h +_) p) e)))
                                         (sb (sg (even h) α) l))
      where
      +-suc′ : ∀ m n → m + suc n ≡ suc (m + n)
      +-suc′ zero    n = refl
      +-suc′ (suc m) n = cong suc (+-suc′ m n)
  go (h ∷ hs) (y ∷ Y) s (suc k) = go hs Y (λ k → s (suc k)) k

module TensorDeg {N M : Nat} (B : Basis N) (C : Basis M)
                 (dgpB : DegP B) (dgmB : DegM B) (dgpC : DegP C) (dgmC : DegM C) where
  open Tensor B C
  private
    module B = Basis B
    module C = Basis C

  supK : ∀ β k → Sup (λ g → suc g ≡ at 0 B.gdeg k) B.gdeg (at 0c (bK β) k)
  supK true  = supFix B B.bplus dgpB
  supK false = supFix B B.bminus dgmB

  supL : ∀ σ l → Sup (λ h → suc h ≡ at 0 C.gdeg l) C.gdeg (at 0c (bL σ) l)
  supL true  = supFix C C.bplus dgpC
  supL false = supFix C C.bminus dgmC

  deg⊗ : ∀ α j X → SupM B.gdeg C.gdeg (suc j) X → SupM B.gdeg C.gdeg j (D α X)
  deg⊗ α j X sX =
    supM-+ B.gdeg C.gdeg j (osum (bK α) X) (rowD α X)
      (supM-osum B.gdeg C.gdeg j B.gdeg (bK α) X (supK α) sX)
      (supM-row B.gdeg C.gdeg j bL α X supL sX)

------------------------------------------------------------------------
-- Augmentation: ε∂⁺ = ε∂⁻ on 1-chains of K ⊗ L.

private
  if-+ : ∀ b x y → (if b then x + y else 0) ≡ (if b then x else 0) + (if b then y else 0)
  if-+ true  x y = refl
  if-+ false x y = refl

  if-0′ : ∀ b → (if b then 0 else 0) ≡ 0
  if-0′ true  = refl
  if-0′ false = refl

  *-distribʳ : ∀ a b c → (a + b) * c ≡ a * c + b * c
  *-distribʳ zero    b c = refl
  *-distribʳ (suc a) b c = trans (cong (c +_) (*-distribʳ a b c)) (sym (+-assoc c (a * c) (b * c)))
    where open import CaTTExp.Strict.Bag using (+-assoc)

  *-zeroʳ : ∀ n → n * 0 ≡ 0
  *-zeroʳ zero    = refl
  *-zeroʳ (suc n) = *-zeroʳ n

  ==-refl′ : ∀ n → (n ==ℕ n) ≡ true
  ==-refl′ zero    = refl
  ==-refl′ (suc n) = ==-refl′ n

  open import CaTTExp.Strict.Bag using (+-interchange)

augm-+ : ∀ {m} (gs u v : Vec Nat m) → augm gs (u +c v) ≡ augm gs u + augm gs v
augm-+ []       []      []      = refl
augm-+ (g ∷ gs) (a ∷ u) (b ∷ v) =
  trans (cong₂ _+_ (if-+ (g ==ℕ 0) a b) (augm-+ gs u v))
        (+-interchange (if g ==ℕ 0 then a else 0) (if g ==ℕ 0 then b else 0) (augm gs u) (augm gs v))

augm-0 : ∀ {m} (gs : Vec Nat m) → augm gs 0c ≡ 0
augm-0 []       = refl
augm-0 (g ∷ gs) = trans (cong (_+ augm gs 0c) (if-0′ (g ==ℕ 0))) (augm-0 gs)

augm-⊙ : ∀ {m} (gs v : Vec Nat m) a → augm gs (a ⊙ v) ≡ a * augm gs v
augm-⊙ gs v zero    = augm-0 gs
augm-⊙ gs v (suc a) = trans (augm-+ gs v (a ⊙ v)) (cong (augm gs v +_) (augm-⊙ gs v a))

-- A chain supported on no degree has augmentation 0.
augm-none : ∀ {m} P (gs v : Vec Nat m) → Sup P gs v → (∀ g → P g → ⊥) → augm gs v ≡ 0
augm-none P []       []      s n = refl
augm-none P (g ∷ gs) (a ∷ v) s n = trans (cong₂ _+_ (hd (s 0)) (augm-none P gs v (λ i → s (suc i)) n)) refl
  where
  hd : a ≡ 0 ⊎ P g → (if g ==ℕ 0 then a else 0) ≡ 0
  hd (inj₁ refl) = if-0′ (g ==ℕ 0)
  hd (inj₂ p)    = ⊥-elim (n g p)

-- A chain supported in degree j is fixed by prj j.
sup-prj : ∀ {m} j (gs v : Vec Nat m) → Sup (λ h → h ≡ j) gs v → prj j gs v ≡ v
sup-prj j []       []      s = refl
sup-prj j (g ∷ gs) (a ∷ v) s = cong₂ _∷_ (hd (s 0)) (sup-prj j gs v (λ i → s (suc i)))
  where
  hd : a ≡ 0 ⊎ g ≡ j → (if g ==ℕ j then a else 0) ≡ a
  hd (inj₁ refl) = if-0′ (g ==ℕ j)
  hd (inj₂ refl) = cong (λ b → if b then a else 0) (==-refl′ g)

augM : ∀ {N M} → Vec Nat N → Vec Nat M → Mat N M → Nat
augM []       gL []      = 0
augM (g ∷ gK) gL (x ∷ X) = (if g ==ℕ 0 then augm gL x else 0) + augM gK gL X

augM-+ : ∀ {N M} (gK : Vec Nat N) (gL : Vec Nat M) X Y → augM gK gL (X +m Y) ≡ augM gK gL X + augM gK gL Y
augM-+ []       gL []      []      = refl
augM-+ (g ∷ gK) gL (x ∷ X) (y ∷ Y) =
  trans (cong₂ _+_ (trans (cong (λ n → if g ==ℕ 0 then n else 0) (augm-+ gL x y)) (if-+ (g ==ℕ 0) (augm gL x) (augm gL y)))
                   (augM-+ gK gL X Y))
        (+-interchange (if g ==ℕ 0 then augm gL x else 0) (if g ==ℕ 0 then augm gL y else 0) (augM gK gL X) (augM gK gL Y))

augM-0 : ∀ {N M} (gK : Vec Nat N) (gL : Vec Nat M) → augM gK gL 0m ≡ 0
augM-0 []       gL = refl
augM-0 (g ∷ gK) gL = trans (cong₂ _+_ (trans (cong (λ n → if g ==ℕ 0 then n else 0) (augm-0 gL)) (if-0′ (g ==ℕ 0))) (augM-0 gK gL)) refl

augM-outer : ∀ {N M} (gK : Vec Nat N) (gL : Vec Nat M) f x → augM gK gL (outer f x) ≡ augm gK f * augm gL x
augM-outer []       gL []      x = refl
augM-outer (g ∷ gK) gL (a ∷ f) x =
  trans (cong₂ _+_ (trans (cong (λ n → if g ==ℕ 0 then n else 0) (augm-⊙ gL x a)) (hd (g ==ℕ 0))) (augM-outer gK gL f x))
        (sym (*-distribʳ (if g ==ℕ 0 then a else 0) (augm gK f) (augm gL x)))
  where
  hd : ∀ b → (if b then a * augm gL x else 0) ≡ (if b then a else 0) * augm gL x
  hd true  = refl
  hd false = refl

-- Two families with the same augmentation wherever it matters.
augM-osum : ∀ {N P M} (gK : Vec Nat N) (gL : Vec Nat M) (F G : Vec (Vec Nat N) P) (X : Mat P M) →
            (∀ k → augm gL (at 0c X k) ≡ 0 ⊎ augm gK (at 0c F k) ≡ augm gK (at 0c G k)) →
            augM gK gL (osum F X) ≡ augM gK gL (osum G X)
augM-osum gK gL []      []      []      h = refl
augM-osum gK gL (f ∷ F) (g ∷ G) (x ∷ X) h =
  trans (augM-+ gK gL (outer f x) (osum F X))
    (trans (cong₂ _+_ (trans (augM-outer gK gL f x) (trans (hd (h 0)) (sym (augM-outer gK gL g x))))
                      (augM-osum gK gL F G X (λ k → h (suc k))))
           (sym (augM-+ gK gL (outer g x) (osum G X))))
  where
  hd : augm gL x ≡ 0 ⊎ augm gK f ≡ augm gK g → augm gK f * augm gL x ≡ augm gK g * augm gL x
  hd (inj₁ z) = trans (cong (augm gK f *_) z) (trans (*-zeroʳ (augm gK f)) (sym (trans (cong (augm gK g *_) z) (*-zeroʳ (augm gK g)))))
  hd (inj₂ e) = cong (_* augm gL x) e

module TensorAug {N M : Nat} (B : Basis N) (C : Basis M) (HB : Hyp B) (HC : Hyp C)
                 (dgpB : DegP B) (dgmB : DegM B) where
  open Tensor B C
  private
    module B = Basis B
    module C = Basis C

    lin-unit : ∀ {P m} i → i < m → (vs : Vec (Vec Nat P) m) → lin (unit {m} i) vs ≡ at 0c vs i
    lin-unit {P} {suc m} zero    _       (v ∷ vs) =
      trans (cong₂ _+c_ (trans (+c-comm v 0c) (+c-id v)) (lin-0 vs)) (trans (+c-comm v 0c) (+c-id v))
    lin-unit {P} {suc m} (suc i) (s≤s l) (v ∷ vs) = trans (+c-id (lin (unit {m} i) vs)) (lin-unit i l vs)

    prj-unit : ∀ {m} (gs : Vec Nat m) k → k < m → prj (at 0 gs k) gs (unit k) ≡ unit k
    prj-unit (g ∷ gs) zero    _       = cong₂ _∷_ (cong (λ b → if b then 1 else 0) (==-refl′ g)) (prj-0 g gs)
    prj-unit (g ∷ gs) (suc k) (s≤s l) = cong₂ _∷_ (if-0′ (g ==ℕ at 0 gs k)) (prj-unit gs k l)

    -- A generator of degree 1 is in range.
    in-range : ∀ {m} (gs : Vec Nat m) k → at 0 gs k ≡ 1 → k < m
    in-range []       k       ()
    in-range (g ∷ gs) zero    e = s≤s z≤n
    in-range (g ∷ gs) (suc k) e = s≤s (in-range gs k e)

    augB : ∀ k → at 0 B.gdeg k ≡ 1 → augm B.gdeg (at 0c B.bplus k) ≡ augm B.gdeg (at 0c B.bminus k)
    augB k e =
      trans (cong (augm B.gdeg) (sym (lin-unit k kN B.bplus)))
        (trans (Hyp.aug1 HB (unit k) (subst (λ j → prj j B.gdeg (unit k) ≡ unit k) e (prj-unit B.gdeg k kN)))
               (cong (augm B.gdeg) (lin-unit k kN B.bminus)))
      where
      kN = in-range B.gdeg k e

    supB : ∀ (bs : Vec (Vec Nat N) N) → zipV (degFix B) B.gdeg bs ≡ bs → ∀ k → Sup (λ g → suc g ≡ at 0 B.gdeg k) B.gdeg (at 0c bs k)
    supB = supFix B

    no-suc0 : ∀ g → suc g ≡ 0 → ⊥
    no-suc0 g ()

    no-2 : ∀ g h → suc (suc g) + h ≡ 1 → ⊥
    no-2 g h ()

  -- The columns: ∂^±_K agree on augmentation in degree 1, vanish in degree 0.
  col-aug : ∀ X → SupM B.gdeg C.gdeg 1 X → augM B.gdeg C.gdeg (osum B.bplus X) ≡ augM B.gdeg C.gdeg (osum B.bminus X)
  col-aug X sX = augM-osum B.gdeg C.gdeg B.bplus B.bminus X h
    where
    h : ∀ k → augm C.gdeg (at 0c X k) ≡ 0 ⊎ augm B.gdeg (at 0c B.bplus k) ≡ augm B.gdeg (at 0c B.bminus k)
    h k = go (at 0 B.gdeg k) refl
      where
      go : ∀ g → at 0 B.gdeg k ≡ g → augm C.gdeg (at 0c X k) ≡ 0 ⊎ augm B.gdeg (at 0c B.bplus k) ≡ augm B.gdeg (at 0c B.bminus k)
      go zero          e = inj₂ (trans (augm-none (λ g → suc g ≡ at 0 B.gdeg k) B.gdeg _ (supB B.bplus dgpB k) (λ g p → no-suc0 g (trans p e)))
                                       (sym (augm-none (λ g → suc g ≡ at 0 B.gdeg k) B.gdeg _ (supB B.bminus dgmB k) (λ g p → no-suc0 g (trans p e)))))
      go (suc zero)    e = inj₂ (augB k e)
      go (suc (suc g)) e = inj₁ (augm-none (λ h → at 0 B.gdeg k + h ≡ 1) C.gdeg _ (sX k) (λ h p → no-2 g h (trans (cong (_+ h) (sym e)) p)))

  -- The rows: only rows of degree 0 count, and there ∂^±_L agree on augmentation.
  row-aug : ∀ X → SupM B.gdeg C.gdeg 1 X → augM B.gdeg C.gdeg (rowD true X) ≡ augM B.gdeg C.gdeg (rowD false X)
  row-aug X sX = go B.gdeg X sX
    where
    go : ∀ {P} (gs : Vec Nat P) (Y : Mat P M) → SupM gs C.gdeg 1 Y → augM gs C.gdeg (rowW gs bL true Y) ≡ augM gs C.gdeg (rowW gs bL false Y)
    go []       []      s = refl
    go (zero  ∷ gs) (y ∷ Y) s = cong₂ _+_ (Hyp.aug1 HC y (sup-prj 1 C.gdeg y (s 0))) (go gs Y (λ k → s (suc k)))
    go (suc g ∷ gs) (y ∷ Y) s = cong (0 +_) (go gs Y (λ k → s (suc k)))

  aug⊗ : ∀ X → SupM B.gdeg C.gdeg 1 X → augM B.gdeg C.gdeg (D true X) ≡ augM B.gdeg C.gdeg (D false X)
  aug⊗ X sX =
    trans (augM-+ B.gdeg C.gdeg (osum B.bplus X) (rowD true X))
      (trans (cong₂ _+_ (col-aug X sX) (row-aug X sX)) (sym (augM-+ B.gdeg C.gdeg (osum B.bminus X) (rowD false X))))

------------------------------------------------------------------------
-- The layout: block k lists the row k⊗l, reversed when deg k is odd.

infixr 5 _++V_
_++V_ : ∀ {A : Set} {m n} → Vec A m → Vec A n → Vec A (m + n)
[]       ++V ys = ys
(x ∷ xs) ++V ys = x ∷ (xs ++V ys)

snocV : ∀ {A : Set} {m} → Vec A m → A → Vec A (suc m)
snocV []       y = y ∷ []
snocV (x ∷ xs) y = x ∷ snocV xs y

revV : ∀ {A : Set} {m} → Vec A m → Vec A m
revV []       = []
revV (x ∷ xs) = snocV (revV xs) x

rv : ∀ {A : Set} {m} → Bool → Vec A m → Vec A m
rv true  v = revV v
rv false v = v

odd : Nat → Bool
odd n = not (even n)

flatA : ∀ {A : Set} {N M} → Vec Nat N → Vec (Vec A M) N → Vec A (N * M)
flatA []       []      = []
flatA (g ∷ gs) (x ∷ X) = rv (odd g) x ++V flatA gs X

splitV : ∀ {A : Set} m {n} → Vec A (m + n) → Vec A m × Vec A n
splitV zero    v       = [] , v
splitV (suc m) (x ∷ v) = (x ∷ fst (splitV m v)) , snd (splitV m v)

unflat : ∀ {N M} → Vec Nat N → Vec Nat (N * M) → Mat N M
unflat {M = M} []       c = []
unflat {M = M} (g ∷ gs) c = rv (odd g) (fst (splitV M c)) ∷ unflat gs (snd (splitV M c))

private
  snoc-rev : ∀ {A : Set} {m} (xs : Vec A m) y → revV (snocV xs y) ≡ y ∷ revV xs
  snoc-rev []       y = refl
  snoc-rev (x ∷ xs) y = cong (λ v → snocV v x) (snoc-rev xs y)

  rev-rev : ∀ {A : Set} {m} (xs : Vec A m) → revV (revV xs) ≡ xs
  rev-rev []       = refl
  rev-rev (x ∷ xs) = trans (snoc-rev (revV xs) x) (cong (x ∷_) (rev-rev xs))

  rv-rv : ∀ {A : Set} {m} b (xs : Vec A m) → rv b (rv b xs) ≡ xs
  rv-rv true  xs = rev-rev xs
  rv-rv false xs = refl

  split-++ : ∀ {A : Set} {m n} (xs : Vec A m) (ys : Vec A n) → splitV m (xs ++V ys) ≡ (xs , ys)
  split-++ []       ys = refl
  split-++ (x ∷ xs) ys = cong (λ p → (x ∷ fst p) , snd p) (split-++ xs ys)

  ++-split : ∀ {A : Set} m {n} (v : Vec A (m + n)) → fst (splitV m v) ++V snd (splitV m v) ≡ v
  ++-split zero    v       = refl
  ++-split (suc m) (x ∷ v) = cong (x ∷_) (++-split m v)

unflat-flat : ∀ {N M} (gs : Vec Nat N) (X : Mat N M) → unflat gs (flatA gs X) ≡ X
unflat-flat []       []      = refl
unflat-flat {M = M} (g ∷ gs) (x ∷ X) =
  cong₂ (λ p q → rv (odd g) p ∷ unflat gs q) (cong fst (split-++ (rv (odd g) x) (flatA gs X))) (cong snd (split-++ (rv (odd g) x) (flatA gs X)))
  ▸ cong₂ _∷_ (rv-rv (odd g) x) (unflat-flat gs X)
  where
  _▸_ : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  _▸_ = trans

flat-unflat : ∀ {N M} (gs : Vec Nat N) (c : Vec Nat (N * M)) → flatA gs (unflat gs c) ≡ c
flat-unflat []       []  = refl
flat-unflat {M = M} (g ∷ gs) c =
  trans (cong₂ _++V_ (rv-rv (odd g) (fst (splitV M c))) (flat-unflat gs (snd (splitV M c)))) (++-split M c)

------------------------------------------------------------------------
-- Linear algebra through the layout.

private
  r0c : ∀ {m} (v : Vec Nat m) → v +c 0c ≡ v
  r0c v = trans (+c-comm v 0c) (+c-id v)

  midc : ∀ {m} (a b c d : Vec Nat m) → (a +c b) +c (c +c d) ≡ (a +c c) +c (b +c d)
  midc {m} a b c d = solve ((` 0 ⊞ ` 1) ⊞ (` 2 ⊞ ` 3)) ((` 0 ⊞ ` 2) ⊞ (` 1 ⊞ ` 3)) (lk (a ∷ b ∷ c ∷ d ∷ [])) tt
    where open Solver (chainMon m)

lin-++ : ∀ {P m n} (u : Vec Nat m) (u′ : Vec Nat n) (vs : Vec (Vec Nat P) m) (vs′ : Vec (Vec Nat P) n) →
         lin (u ++V u′) (vs ++V vs′) ≡ lin u vs +c lin u′ vs′
lin-++ []      u′ []       vs′ = sym (+c-id (lin u′ vs′))
lin-++ (a ∷ u) u′ (v ∷ vs) vs′ = trans (cong ((a ⊙ v) +c_) (lin-++ u u′ vs vs′)) (sym (+c-assoc (a ⊙ v) (lin u vs) (lin u′ vs′)))

lin-snoc : ∀ {P m} (u : Vec Nat m) a (vs : Vec (Vec Nat P) m) v → lin (snocV u a) (snocV vs v) ≡ lin u vs +c (a ⊙ v)
lin-snoc []      a []       v = trans (r0c (a ⊙ v)) (sym (+c-id (a ⊙ v)))
lin-snoc (b ∷ u) a (w ∷ vs) v = trans (cong ((b ⊙ w) +c_) (lin-snoc u a vs v)) (sym (+c-assoc (b ⊙ w) (lin u vs) (a ⊙ v)))

lin-rv : ∀ {P m} b (u : Vec Nat m) (vs : Vec (Vec Nat P) m) → lin (rv b u) (rv b vs) ≡ lin u vs
lin-rv false u       vs       = refl
lin-rv true  []      []       = refl
lin-rv true  (a ∷ u) (v ∷ vs) = trans (lin-snoc (revV u) a (revV vs) v) (trans (cong (_+c (a ⊙ v)) (lin-rv true u vs)) (+c-comm (lin u vs) (a ⊙ v)))

-- Blockwise lin.
linR : ∀ {P N M} → Mat N M → Vec (Vec (Vec Nat P) M) N → Vec Nat P
linR []      []      = 0c
linR (x ∷ X) (f ∷ F) = lin x f +c linR X F

lin-flat : ∀ {P N M} (gs : Vec Nat N) (X : Mat N M) (F : Vec (Vec (Vec Nat P) M) N) → lin (flatA gs X) (flatA gs F) ≡ linR X F
lin-flat []       []      []      = refl
lin-flat (g ∷ gs) (x ∷ X) (f ∷ F) =
  trans (lin-++ (rv (odd g) x) (flatA gs X) (rv (odd g) f) (flatA gs F)) (cong₂ _+c_ (lin-rv (odd g) x f) (lin-flat gs X F))

private
  ++-+ : ∀ {m n} (u v : Vec Nat m) (u′ v′ : Vec Nat n) → (u +c v) ++V (u′ +c v′) ≡ (u ++V u′) +c (v ++V v′)
  ++-+ []      []      u′ v′ = refl
  ++-+ (a ∷ u) (b ∷ v) u′ v′ = cong ((a + b) ∷_) (++-+ u v u′ v′)

  snoc-+ : ∀ {m} (u v : Vec Nat m) a b → snocV (u +c v) (a + b) ≡ snocV u a +c snocV v b
  snoc-+ []      []      a b = refl
  snoc-+ (c ∷ u) (d ∷ v) a b = cong ((c + d) ∷_) (snoc-+ u v a b)

  rev-+ : ∀ {m} (u v : Vec Nat m) → revV (u +c v) ≡ revV u +c revV v
  rev-+ []      []      = refl
  rev-+ (a ∷ u) (b ∷ v) = trans (cong (λ w → snocV w (a + b)) (rev-+ u v)) (snoc-+ (revV u) (revV v) a b)

  rv-+ : ∀ {m} b (u v : Vec Nat m) → rv b (u +c v) ≡ rv b u +c rv b v
  rv-+ true  u v = rev-+ u v
  rv-+ false u v = refl

  snoc-0 : ∀ m → snocV (0c {m}) 0 ≡ 0c
  snoc-0 zero    = refl
  snoc-0 (suc m) = cong (0 ∷_) (snoc-0 m)

  rev-0 : ∀ m → revV (0c {m}) ≡ 0c
  rev-0 zero    = refl
  rev-0 (suc m) = trans (cong (λ w → snocV w 0) (rev-0 m)) (snoc-0 m)

flat-+ : ∀ {N M} (gs : Vec Nat N) (X Y : Mat N M) → flatA gs (X +m Y) ≡ flatA gs X +c flatA gs Y
flat-+ []       []      []      = refl
flat-+ (g ∷ gs) (x ∷ X) (y ∷ Y) =
  trans (cong₂ _++V_ (rv-+ (odd g) x y) (flat-+ gs X Y)) (++-+ (rv (odd g) x) (rv (odd g) y) (flatA gs X) (flatA gs Y))

flat-0 : ∀ {N M} (gs : Vec Nat N) → flatA gs (0m {N} {M}) ≡ 0c
flat-0 []       = refl
flat-0 {M = M} (g ∷ gs) = trans (cong₂ _++V_ (rv0 (odd g)) (flat-0 gs)) (++0 M)
  where
  rv0 : ∀ b → rv b (0c {M}) ≡ 0c
  rv0 true  = rev-0 M
  rv0 false = refl
  ++0 : ∀ m {n} → (0c {m}) ++V (0c {n}) ≡ 0c
  ++0 zero    = refl
  ++0 (suc m) = cong (0 ∷_) (++0 m)

private
  osum-cons0 : ∀ {N P M} (F : Vec (Vec Nat N) P) (X : Mat P M) → osum (mapV (0 ∷_) F) X ≡ 0c ∷ osum F X
  osum-cons0 []      []      = refl
  osum-cons0 (f ∷ F) (x ∷ X) = trans (cong (outer (0 ∷ f) x +m_) (osum-cons0 F X)) (cong (_∷ (outer f x +m osum F X)) (+c-id 0c))

  ⊙1 : ∀ {m} (x : Vec Nat m) → 1 ⊙ x ≡ x
  ⊙1 x = r0c x

osum-units : ∀ {N M} (X : Mat N M) → osum (units N) X ≡ X
osum-units [] = refl
osum-units {suc N} (x ∷ X) =
  trans (cong ((outer (1 ∷ 0c) x) +m_) (trans (osum-cons0 (units N) X) (cong (0c ∷_) (osum-units X))))
        (cong₂ _∷_ (trans (cong (_+c 0c) (⊙1 x)) (r0c x)) (trans (cong (_+m X) (outer-0l {N} x)) (+m-id X)))

------------------------------------------------------------------------
-- Supports, structurally.

SupS : ∀ {m} → (Nat → Set) → Vec Nat m → Vec Nat m → Set
SupS P []       []      = ⊤
SupS P (g ∷ gs) (a ∷ v) = (a ≡ 0 ⊎ P g) × SupS P gs v

SupS→Sup : ∀ {m} P (gs v : Vec Nat m) → SupS P gs v → Sup P gs v
SupS→Sup P []       []      s       i       = inj₁ refl
SupS→Sup P (g ∷ gs) (a ∷ v) (h , s) zero    = h
SupS→Sup P (g ∷ gs) (a ∷ v) (h , s) (suc i) = SupS→Sup P gs v s i

Sup→SupS : ∀ {m} P (gs v : Vec Nat m) → Sup P gs v → SupS P gs v
Sup→SupS P []       []      s = tt
Sup→SupS P (g ∷ gs) (a ∷ v) s = s 0 , Sup→SupS P gs v (λ i → s (suc i))

SupS-++ : ∀ {m n} P (gs v : Vec Nat m) (gs′ v′ : Vec Nat n) → SupS P gs v → SupS P gs′ v′ → SupS P (gs ++V gs′) (v ++V v′)
SupS-++ P []       []      gs′ v′ s s′ = s′
SupS-++ P (g ∷ gs) (a ∷ v) gs′ v′ (h , s) s′ = h , SupS-++ P gs v gs′ v′ s s′

SupS-++⁻ : ∀ {m n} P (gs v : Vec Nat m) (gs′ v′ : Vec Nat n) → SupS P (gs ++V gs′) (v ++V v′) → SupS P gs v × SupS P gs′ v′
SupS-++⁻ P []       []      gs′ v′ s       = tt , s
SupS-++⁻ P (g ∷ gs) (a ∷ v) gs′ v′ (h , s) = let (s₁ , s₂) = SupS-++⁻ P gs v gs′ v′ s in (h , s₁) , s₂

private
  SupS-snoc : ∀ {m} P (gs v : Vec Nat m) g a → SupS P gs v → (a ≡ 0 ⊎ P g) → SupS P (snocV gs g) (snocV v a)
  SupS-snoc P []       []      g a s h = h , tt
  SupS-snoc P (g′ ∷ gs) (b ∷ v) g a (h′ , s) h = h′ , SupS-snoc P gs v g a s h

  SupS-snoc⁻ : ∀ {m} P (gs v : Vec Nat m) g a → SupS P (snocV gs g) (snocV v a) → SupS P gs v × (a ≡ 0 ⊎ P g)
  SupS-snoc⁻ P []       []      g a (h , _) = tt , h
  SupS-snoc⁻ P (g′ ∷ gs) (b ∷ v) g a (h′ , s) = let (s₁ , h) = SupS-snoc⁻ P gs v g a s in (h′ , s₁) , h

SupS-rv : ∀ {m} P b (gs v : Vec Nat m) → SupS P gs v → SupS P (rv b gs) (rv b v)
SupS-rv P false gs       v       s       = s
SupS-rv P true  []       []      s       = tt
SupS-rv P true  (g ∷ gs) (a ∷ v) (h , s) = SupS-snoc P (revV gs) (revV v) g a (SupS-rv P true gs v s) h

SupS-rv⁻ : ∀ {m} P b (gs v : Vec Nat m) → SupS P (rv b gs) (rv b v) → SupS P gs v
SupS-rv⁻ P false gs       v       s = s
SupS-rv⁻ P true  []       []      s = tt
SupS-rv⁻ P true  (g ∷ gs) (a ∷ v) s = let (s₁ , h) = SupS-snoc⁻ P (revV gs) (revV v) g a s in h , SupS-rv⁻ P true gs v s₁

-- prj j fixes exactly the chains supported in degree j.
prj→SupS : ∀ {m} j (gs v : Vec Nat m) → prj j gs v ≡ v → SupS (λ h → h ≡ j) gs v
prj→SupS j []       []      e = tt
prj→SupS j (g ∷ gs) (a ∷ v) e = hd (g ==ℕ j) refl (cong hd′ e) , prj→SupS j gs v (cong tl e)
  where
  hd′ : ∀ {n} → Vec Nat (suc n) → Nat
  hd′ (x ∷ _) = x
  tl : ∀ {n} → Vec Nat (suc n) → Vec Nat n
  tl (_ ∷ xs) = xs
  ==-sound : ∀ m n → (m ==ℕ n) ≡ true → m ≡ n
  ==-sound zero    zero    _ = refl
  ==-sound (suc m) (suc n) e = cong suc (==-sound m n e)
  ==-sound zero    (suc n) ()
  ==-sound (suc m) zero    ()
  hd : ∀ b → (g ==ℕ j) ≡ b → (if b then a else 0) ≡ a → a ≡ 0 ⊎ g ≡ j
  hd true  q _ = inj₂ (==-sound g j q)
  hd false q e = inj₁ (sym e)

SupS→prj : ∀ {m} j (gs v : Vec Nat m) → SupS (λ h → h ≡ j) gs v → prj j gs v ≡ v
SupS→prj j gs v s = sup-prj j gs v (SupS→Sup (λ h → h ≡ j) gs v s)

------------------------------------------------------------------------
-- K ⊗ L as a basis.

module TensorLay {N M : Nat} (B : Basis N) (C : Basis M) where
  open Tensor B C
  private
    module B = Basis B
    module C = Basis C
    gK = B.gdeg
    gL = C.gdeg

  degRow : Nat → Vec Nat M
  degRow g = mapV (g +_) gL

  gdeg⊗ : Vec Nat (N * M)
  gdeg⊗ = flatA gK (mapV degRow gK)

  fam : Bool → Vec (Vec (Vec Nat (N * M)) M) N
  fam α = mapV (λ u → mapV (λ v → flatA gK (D α (outer u v))) (units M)) (units N)

  B⊗ : Basis (N * M)
  B⊗ = record { gdeg = gdeg⊗ ; bplus = flatA gK (fam true) ; bminus = flatA gK (fam false) }

  private
    fD : Bool → Vec Nat N → Vec Nat M → Vec Nat (N * M)
    fD α u v = flatA gK (D α (outer u v))

    fD-+ : ∀ α u v w → fD α u (v +c w) ≡ fD α u v +c fD α u w
    fD-+ α u v w = trans (cong (λ Y → flatA gK (D α Y)) (outer-+r u v w))
                         (trans (cong (flatA gK) (D-+ α (outer u v) (outer u w))) (flat-+ gK (D α (outer u v)) (D α (outer u w))))

    fD-0 : ∀ α u → fD α u 0c ≡ 0c
    fD-0 α u = trans (cong (λ Y → flatA gK (D α Y)) (outer-0r u)) (trans (cong (flatA gK) (D-0 α)) (flat-0 gK))

    linR-fam : ∀ {P} α (us : Vec (Vec Nat N) P) (X : Mat P M) →
               linR X (mapV (λ u → mapV (fD α u) (units M)) us) ≡ flatA gK (D α (osum us X))
    linR-fam α []       []      = sym (trans (cong (flatA gK) (D-0 α)) (flat-0 gK))
    linR-fam α (u ∷ us) (x ∷ X) =
      trans (cong₂ _+c_ (trans (lin-hom (fD α u) (fD-+ α u) (fD-0 α u) x (units M)) (cong (fD α u) (lin-units x)))
                        (linR-fam α us X))
            (sym (trans (cong (flatA gK) (D-+ α (outer u x) (osum us X))) (flat-+ gK (D α (outer u x)) (D α (osum us X)))))

  -- ∂^α in the layout is D α.
  d⊗ : ∀ α c → lin c (flatA gK (fam α)) ≡ flatA gK (D α (unflat gK c))
  d⊗ α c =
    trans (cong (λ c′ → lin c′ (flatA gK (fam α))) (sym (flat-unflat gK c)))
      (trans (lin-flat gK (unflat gK c) (fam α))
        (trans (linR-fam α (units N) (unflat gK c)) (cong (λ Y → flatA gK (D α Y)) (osum-units (unflat gK c)))))

  dP⊗ : ∀ c → dP B⊗ c ≡ flatA gK (D true (unflat gK c))
  dP⊗ = d⊗ true

  dM⊗ : ∀ c → dM B⊗ c ≡ flatA gK (D false (unflat gK c))
  dM⊗ = d⊗ false

  -- Degrees in the layout are SupM.
  supS-flat : ∀ j (X : Mat N M) → SupM gK gL j X → SupS (λ h → h ≡ j) gdeg⊗ (flatA gK X)
  supS-flat j X s = go gK X s
    where
    row : ∀ g x → Sup (λ h → g + h ≡ j) gL x → SupS (λ h → h ≡ j) (degRow g) x
    row g x s = go′ gL x (Sup→SupS (λ h → g + h ≡ j) gL x s)
      where
      go′ : ∀ {m} (hs v : Vec Nat m) → SupS (λ h → g + h ≡ j) hs v → SupS (λ h → h ≡ j) (mapV (g +_) hs) v
      go′ []       []      _       = tt
      go′ (h ∷ hs) (a ∷ v) (p , s) = p , go′ hs v s
    go : ∀ {P} (hs : Vec Nat P) (Y : Mat P M) → SupM hs gL j Y → SupS (λ h → h ≡ j) (flatA hs (mapV degRow hs)) (flatA hs Y)
    go []       []      s = tt
    go (h ∷ hs) (y ∷ Y) s =
      SupS-++ (λ h′ → h′ ≡ j) (rv (odd h) (degRow h)) (rv (odd h) y) _ _
              (SupS-rv (λ h′ → h′ ≡ j) (odd h) (degRow h) y (row h y (s 0))) (go hs Y (λ k → s (suc k)))

  flat-supS : ∀ j (X : Mat N M) → SupS (λ h → h ≡ j) gdeg⊗ (flatA gK X) → SupM gK gL j X
  flat-supS j X s = go gK X s
    where
    row : ∀ g x → SupS (λ h → h ≡ j) (degRow g) x → Sup (λ h → g + h ≡ j) gL x
    row g x s = SupS→Sup (λ h → g + h ≡ j) gL x (go′ gL x s)
      where
      go′ : ∀ {m} (hs v : Vec Nat m) → SupS (λ h → h ≡ j) (mapV (g +_) hs) v → SupS (λ h → g + h ≡ j) hs v
      go′ []       []      _       = tt
      go′ (h ∷ hs) (a ∷ v) (p , s) = p , go′ hs v s
    go : ∀ {P} (hs : Vec Nat P) (Y : Mat P M) → SupS (λ h → h ≡ j) (flatA hs (mapV degRow hs)) (flatA hs Y) → SupM hs gL j Y
    go []       []      s k = subst (Sup (λ h′ → at 0 [] k + h′ ≡ j) gL) (sym (at0m k)) (sup-0 (λ h′ → at 0 [] k + h′ ≡ j) gL)
      where
      at0m : ∀ k → at 0c ([] {A = Vec Nat M}) k ≡ 0c
      at0m k = refl
    go (h ∷ hs) (y ∷ Y) s zero    =
      row h y (SupS-rv⁻ (λ h′ → h′ ≡ j) (odd h) (degRow h) y (fst (SupS-++⁻ (λ h′ → h′ ≡ j) (rv (odd h) (degRow h)) (rv (odd h) y) _ _ s)))
    go (h ∷ hs) (y ∷ Y) s (suc k) =
      go hs Y (snd (SupS-++⁻ (λ h′ → h′ ≡ j) (rv (odd h) (degRow h)) (rv (odd h) y) _ _ s)) k

  -- Augmentation in the layout is augM.
  augm-flat : ∀ (X : Mat N M) → augm gdeg⊗ (flatA gK X) ≡ augM gK gL X
  augm-flat X = go gK X
    where
    open import CaTTExp.Strict.Bag using (+-assoc; +-comm)
    a-++ : ∀ {m n} (gs v : Vec Nat m) (gs′ v′ : Vec Nat n) → augm (gs ++V gs′) (v ++V v′) ≡ augm gs v + augm gs′ v′
    a-++ []       []      gs′ v′ = refl
    a-++ (g ∷ gs) (a ∷ v) gs′ v′ = trans (cong ((if g ==ℕ 0 then a else 0) +_) (a-++ gs v gs′ v′))
                                         (sym (+-assoc (if g ==ℕ 0 then a else 0) (augm gs v) (augm gs′ v′)))
    a-snoc : ∀ {m} (gs v : Vec Nat m) g a → augm (snocV gs g) (snocV v a) ≡ augm gs v + (if g ==ℕ 0 then a else 0)
    a-snoc []       []      g a = +-comm (if g ==ℕ 0 then a else 0) 0
    a-snoc (h ∷ hs) (b ∷ v) g a = trans (cong ((if h ==ℕ 0 then b else 0) +_) (a-snoc hs v g a))
                                        (sym (+-assoc (if h ==ℕ 0 then b else 0) (augm hs v) (if g ==ℕ 0 then a else 0)))
    a-rv : ∀ {m} b (gs v : Vec Nat m) → augm (rv b gs) (rv b v) ≡ augm gs v
    a-rv false gs       v       = refl
    a-rv true  []       []      = refl
    a-rv true  (g ∷ gs) (a ∷ v) = trans (a-snoc (revV gs) (revV v) g a)
                                    (trans (cong (_+ (if g ==ℕ 0 then a else 0)) (a-rv true gs v))
                                           (+-comm (augm gs v) (if g ==ℕ 0 then a else 0)))
    a-row : ∀ {m} g (hs x : Vec Nat m) → augm (mapV (g +_) hs) x ≡ (if g ==ℕ 0 then augm hs x else 0)
    a-row zero    []       []      = refl
    a-row zero    (h ∷ hs) (a ∷ x) = cong ((if h ==ℕ 0 then a else 0) +_) (a-row zero hs x)
    a-row (suc g) []       []      = refl
    a-row (suc g) (h ∷ hs) (a ∷ x) = a-row (suc g) hs x
    go : ∀ {P} (hs : Vec Nat P) (Y : Mat P M) → augm (flatA hs (mapV degRow hs)) (flatA hs Y) ≡ augM hs gL Y
    go []       []      = refl
    go (h ∷ hs) (y ∷ Y) =
      trans (a-++ (rv (odd h) (degRow h)) (rv (odd h) y) (flatA hs (mapV degRow hs)) (flatA hs Y))
            (cong₂ _+_ (trans (a-rv (odd h) (degRow h) y) (a-row h gL y)) (go hs Y))

------------------------------------------------------------------------
-- ∂∂ = 0, degrees and augmentation for the layout of K ⊗ L.

module TensorHyp {N M : Nat} (B : Basis N) (C : Basis M) (HB : Hyp B) (HC : Hyp C)
                 (dgpB : DegP B) (dgmB : DegM B) (dgpC : DegP C) (dgmC : DegM C) where
  open Tensor B C
  open TensorLay B C public
  open TensorDD B C HB HC dgpB dgmB using (dd⊗)
  open TensorDeg B C dgpB dgmB dgpC dgmC using (deg⊗)
  open TensorAug B C HB HC dgpB dgmB using (aug⊗)
  private
    module B = Basis B
    module C = Basis C
    gK = B.gdeg
    gL = C.gdeg

    -- Both boundaries, with the layout undone.
    dd2 : ∀ α β c → lin (lin c (flatA gK (fam β))) (flatA gK (fam α)) ≡ flatA gK (D α (D β (unflat gK c)))
    dd2 α β c = trans (d⊗ α (lin c (flatA gK (fam β))))
                      (cong (λ c′ → flatA gK (D α (unflat gK c′))) (d⊗ β c) ▸ cong (λ Y → flatA gK (D α Y)) (unflat-flat gK (D β (unflat gK c))))
      where
      _▸_ : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
      _▸_ = trans

  dd′ : ∀ c → dP B⊗ (dP B⊗ c) +c dM B⊗ (dM B⊗ c) ≡ dP B⊗ (dM B⊗ c) +c dM B⊗ (dP B⊗ c)
  dd′ c =
    trans (cong₂ _+c_ (dd2 true true c) (dd2 false false c))
      (trans (sym (flat-+ gK (D true (D true X)) (D false (D false X))))
        (trans (cong (flatA gK) (dd⊗ X))
          (trans (flat-+ gK (D true (D false X)) (D false (D true X)))
                 (sym (cong₂ _+c_ (dd2 true false c) (dd2 false true c))))))
    where
    X = unflat gK c

  private
    deg-d : ∀ α j c → prj (suc j) gdeg⊗ c ≡ c → prj j gdeg⊗ (lin c (flatA gK (fam α))) ≡ lin c (flatA gK (fam α))
    deg-d α j c e =
      trans (cong (prj j gdeg⊗) (d⊗ α c))
        (trans (SupS→prj j gdeg⊗ (flatA gK (D α X)) (supS-flat j (D α X) (deg⊗ α j X sX))) (sym (d⊗ α c)))
      where
      X = unflat gK c
      sX : SupM gK gL (suc j) X
      sX = flat-supS (suc j) X (subst (SupS (λ h → h ≡ suc j) gdeg⊗) (sym (flat-unflat gK c)) (prj→SupS (suc j) gdeg⊗ c e))

  deg-dp′ : ∀ j c → prj (suc j) gdeg⊗ c ≡ c → prj j gdeg⊗ (dP B⊗ c) ≡ dP B⊗ c
  deg-dp′ = deg-d true

  deg-dm′ : ∀ j c → prj (suc j) gdeg⊗ c ≡ c → prj j gdeg⊗ (dM B⊗ c) ≡ dM B⊗ c
  deg-dm′ = deg-d false

  aug1′ : ∀ c → prj 1 gdeg⊗ c ≡ c → augm gdeg⊗ (dP B⊗ c) ≡ augm gdeg⊗ (dM B⊗ c)
  aug1′ c e =
    trans (cong (augm gdeg⊗) (dP⊗ c))
      (trans (augm-flat (D true X))
        (trans (aug⊗ X sX)
          (sym (trans (cong (augm gdeg⊗) (dM⊗ c)) (augm-flat (D false X))))))
    where
    X = unflat gK c
    sX : SupM gK gL 1 X
    sX = flat-supS 1 X (subst (SupS (λ h → h ≡ 1) gdeg⊗) (sym (flat-unflat gK c)) (prj→SupS 1 gdeg⊗ c e))

------------------------------------------------------------------------
-- Positions in the layout.

private
  at-++l : ∀ {A : Set} {m n} (d : A) (u : Vec A m) (w : Vec A n) i → i < m → at d (u ++V w) i ≡ at d u i
  at-++l d (x ∷ u) w zero    _       = refl
  at-++l d (x ∷ u) w (suc i) (s≤s l) = at-++l d u w i l

  at-++r : ∀ {A : Set} {m n} (d : A) (u : Vec A m) (w : Vec A n) i → at d (u ++V w) (m + i) ≡ at d w i
  at-++r d []      w i = refl
  at-++r d (x ∷ u) w i = at-++r d u w i

  at-snoc-l : ∀ {A : Set} {m} (d : A) (u : Vec A m) y i → i < m → at d (snocV u y) i ≡ at d u i
  at-snoc-l d (x ∷ u) y zero    _       = refl
  at-snoc-l d (x ∷ u) y (suc i) (s≤s l) = at-snoc-l d u y i l

  at-snoc-r : ∀ {A : Set} {m} (d : A) (u : Vec A m) y → at d (snocV u y) m ≡ y
  at-snoc-r d []      y = refl
  at-snoc-r d (x ∷ u) y = at-snoc-r d u y

  ∸-suc : ∀ m r → r < m → m ∸ r ≡ suc (m ∸ suc r)
  ∸-suc (suc m) zero    _       = cong suc (sym (∸0 m))
    where
    ∸0 : ∀ m → m ∸ 0 ≡ m
    ∸0 zero    = refl
    ∸0 (suc m) = refl
  ∸-suc (suc m) (suc r) (s≤s l) = ∸-suc m r l

  ∸-self : ∀ m → m ∸ m ≡ 0
  ∸-self zero    = refl
  ∸-self (suc m) = ∸-self m

  lt-or-eq : ∀ i m → i < suc m → (i < m) ⊎ (i ≡ m)
  lt-or-eq zero    zero    _       = inj₂ refl
  lt-or-eq zero    (suc m) _       = inj₁ (s≤s z≤n)
  lt-or-eq (suc i) zero    (s≤s ())
  lt-or-eq (suc i) (suc m) (s≤s l) with lt-or-eq i m l
  ... | inj₁ p = inj₁ (s≤s p)
  ... | inj₂ e = inj₂ (cong suc e)

at-rev : ∀ {A : Set} {m} (d : A) (v : Vec A m) r → r < m → at d (revV v) r ≡ at d v (m ∸ suc r)
at-rev {m = suc m} d (x ∷ v) r l with lt-or-eq r m l
... | inj₁ p    = trans (at-snoc-l d (revV v) x r p) (trans (at-rev d v r p) (cong (at d (x ∷ v)) (sym (∸-suc m r p))))
... | inj₂ refl = trans (at-snoc-r d (revV v) x) (cong (at d (x ∷ v)) (sym (∸-self r)))

at-out : ∀ {A : Set} {m} (d : A) (vs : Vec A m) i → m ≤ i → at d vs i ≡ d
at-out d []       i       _       = refl
at-out d (v ∷ vs) (suc i) (s≤s q) = at-out d vs i q

at-def : ∀ {A : Set} {m} (d d′ : A) (v : Vec A m) i → i < m → at d v i ≡ at d′ v i
at-def d d′ (x ∷ v) zero    _       = refl
at-def d d′ (x ∷ v) (suc i) (s≤s l) = at-def d d′ v i l

private
  ≤-+r : ∀ a b → a ≤ a + b
  ≤-+r zero    b = z≤n
  ≤-+r (suc a) b = s≤s (≤-+r a b)

  -- M + a ≤ d splits d.
  split≤ : ∀ M {a d} → M + a ≤ d → Σ Nat (λ d′ → (d ≡ M + d′) × (a ≤ d′))
  split≤ zero    {d = d}     p       = d , refl , p
  split≤ (suc M) {d = suc d} (s≤s p) = let (d′ , e , q) = split≤ M p in d′ , cong suc e , q

  -- d < M + a: either d < M, or d = M + d′ with d′ < a.
  split< : ∀ M {a} d → d < M + a → (d < M) ⊎ Σ Nat (λ d′ → (d ≡ M + d′) × (d′ < a))
  split< zero    d       p       = inj₂ (d , refl , p)
  split< (suc M) zero    p       = inj₁ (s≤s z≤n)
  split< (suc M) (suc d) (s≤s p) with split< M d p
  ... | inj₁ q              = inj₁ (s≤s q)
  ... | inj₂ (d′ , e , q)   = inj₂ (d′ , cong suc e , q)

  open import CaTTExp.Strict.Bag using (+-assoc; +-suc; +-comm; +-zero)

  rev0 : ∀ m → revV (0c {m}) ≡ 0c
  rev0 zero    = refl
  rev0 (suc m) = trans (cong (λ w → snocV w 0) (rev0 m)) (s0 m)
    where
    s0 : ∀ m → snocV (0c {m}) 0 ≡ 0c
    s0 zero    = refl
    s0 (suc m) = cong (0 ∷_) (s0 m)

  rv0′ : ∀ m b → rv b (0c {m}) ≡ 0c
  rv0′ m true  = rev0 m
  rv0′ m false = refl

module Blocks {M : Nat} where
  -- Rows t, t+1, … vanish: nothing at or after position t·M.
  LoRows : ∀ {P} (gs : Vec Nat P) t (Y : Mat P M) → (∀ k′ → t ≤ k′ → at 0c Y k′ ≡ 0c) → Lo (t * M) (flatA gs Y)
  LoRows []       t       []      h d _ = refl
  LoRows {suc P} (g ∷ gs) zero    (y ∷ Y) h d _ =
    trans (cong (λ Z → at0 (flatA (g ∷ gs) Z) d) (vextV 0c (y ∷ Y) 0m (λ i l → trans (h i z≤n) (sym (at0m {suc P} i)))))
          (trans (cong (λ v → at0 v d) (flat-0 (g ∷ gs))) (at-0c {suc P * M} d))
    where
    at0m : ∀ {P} i → at 0c (0m {P} {M}) i ≡ 0c
    at0m {zero}  i       = refl
    at0m {suc P} zero    = refl
    at0m {suc P} (suc i) = at0m {P} i
  LoRows (g ∷ gs) (suc t) (y ∷ Y) h d p =
    let (d′ , e , q) = split≤ M p in
    trans (cong (at0 (rv (odd g) y ++V flatA gs Y)) e)
          (trans (at-++r 0 (rv (odd g) y) (flatA gs Y) d′) (LoRows gs t Y (λ k′ q′ → h (suc k′) (s≤s q′)) d′ q))

  -- Rows before t vanish: nothing before position t·M.
  HiRows : ∀ {P} (gs : Vec Nat P) t (Y : Mat P M) → (∀ k′ → k′ < t → at 0c Y k′ ≡ 0c) → Hi (t * M) (flatA gs Y)
  HiRows gs       zero    Y       h d ()
  HiRows []       (suc t) []      h d p = refl
  HiRows (g ∷ gs) (suc t) (y ∷ Y) h d p with split< M d p
  ... | inj₁ q = trans (at-++l 0 (rv (odd g) y) (flatA gs Y) d q)
                       (trans (cong (λ w → at0 (rv (odd g) w) d) (h 0 (s≤s z≤n))) (trans (cong (λ w → at0 w d) (rv0′ M (odd g))) (at-0c {M} d)))
  ... | inj₂ (d′ , refl , q) =
    trans (at-++r 0 (rv (odd g) y) (flatA gs Y) d′) (HiRows gs t Y (λ k′ q′ → h (suc k′) (s≤s q′)) d′ q)

  -- Only rows up to k, and row k (as laid out) vanishes from r on.
  LoBlock : ∀ {P} (gs : Vec Nat P) k r (Y : Mat P M) → k < P → (∀ k′ → k < k′ → at 0c Y k′ ≡ 0c) →
            Lo r (rv (odd (at 0 gs k)) (at 0c Y k)) → Lo (k * M + r) (flatA gs Y)
  LoBlock (g ∷ gs) zero r (y ∷ Y) _ h hk d p with ≤-dec M d
  ... | inj₂ q = trans (at-++l 0 (rv (odd g) y) (flatA gs Y) d q) (hk d p)
  ... | inj₁ q =
    let (d′ , e , _) = split≤ M (subst (_≤ d) (sym (+-zero M)) q) in
    trans (cong (at0 (rv (odd g) y ++V flatA gs Y)) e)
          (trans (at-++r 0 (rv (odd g) y) (flatA gs Y) d′) (LoRows gs zero Y (λ k′ _ → h (suc k′) (s≤s z≤n)) d′ z≤n))
  LoBlock (g ∷ gs) (suc k) r (y ∷ Y) (s≤s kP) h hk d p =
    let (d′ , e , q) = split≤ M (subst (_≤ d) (+-assoc M (k * M) r) p) in
    trans (cong (at0 (rv (odd g) y ++V flatA gs Y)) e)
          (trans (at-++r 0 (rv (odd g) y) (flatA gs Y) d′) (LoBlock gs k r Y kP (λ k′ q′ → h (suc k′) (s≤s q′)) hk d′ q))

  -- Only rows from k on, and row k (as laid out) vanishes before r ≤ M.
  HiBlock : ∀ {P} (gs : Vec Nat P) k r (Y : Mat P M) → k < P → r ≤ M → (∀ k′ → k′ < k → at 0c Y k′ ≡ 0c) →
            Hi r (rv (odd (at 0 gs k)) (at 0c Y k)) → Hi (k * M + r) (flatA gs Y)
  HiBlock (g ∷ gs) zero r (y ∷ Y) _ rM h hk d p =
    trans (at-++l 0 (rv (odd g) y) (flatA gs Y) d (≤-trans p rM)) (hk d p)
  HiBlock (g ∷ gs) (suc k) r (y ∷ Y) (s≤s kP) rM h hk d p with split< M d (subst (d <_) (+-assoc M (k * M) r) p)
  ... | inj₁ q = trans (at-++l 0 (rv (odd g) y) (flatA gs Y) d q)
                       (trans (cong (λ w → at0 (rv (odd g) w) d) (h 0 (s≤s z≤n))) (trans (cong (λ w → at0 w d) (rv0′ M (odd g))) (at-0c {M} d)))
  ... | inj₂ (d′ , refl , q) =
    trans (at-++r 0 (rv (odd g) y) (flatA gs Y) d′) (HiBlock gs k r Y kP rM (λ k′ q′ → h (suc k′) (s≤s q′)) hk d′ q)

  -- The entry at position k·M + r.
  at-flat : ∀ {A : Set} {P} (d : A) (dr : Vec A M) (gs : Vec Nat P) (F : Vec (Vec A M) P) k r → k < P → r < M →
            at d (flatA gs F) (k * M + r) ≡ at d (rv (odd (at 0 gs k)) (at dr F k)) r
  at-flat d dr (g ∷ gs) (f ∷ F) zero    r _       rM = at-++l d (rv (odd g) f) (flatA gs F) r rM
  at-flat d dr (g ∷ gs) (f ∷ F) (suc k) r (s≤s l) rM =
    trans (cong (at d (rv (odd g) f ++V flatA gs F)) (+-assoc M (k * M) r))
          (trans (at-++r d (rv (odd g) f) (flatA gs F) (k * M + r)) (at-flat d dr gs F k r l rM))

------------------------------------------------------------------------
-- The order of K ⊗ L: negative faces before, positive faces after.

private
  ∸-≤ : ∀ M b → M ∸ b ≤ M
  ∸-≤ zero    zero    = z≤n
  ∸-≤ zero    (suc b) = z≤n
  ∸-≤ (suc M) zero    = ≤-refl (suc M)
  ∸-≤ (suc M) (suc b) = ≤-suc (∸-≤ M b)

  ∸-anti : ∀ M a b → a ≤ b → M ∸ b ≤ M ∸ a
  ∸-anti M       zero    b       _       = ∸-≤ M b
  ∸-anti zero    (suc a) (suc b) _       = z≤n
  ∸-anti (suc M) (suc a) (suc b) (s≤s p) = ∸-anti M a b p

  ∸suc< : ∀ M r → r < M → M ∸ suc r < M
  ∸suc< (suc M) r _ = s≤s (∸-≤ M r)

  Lo-+ : ∀ {m t} (u v : Vec Nat m) → Lo t u → Lo t v → Lo t (u +c v)
  Lo-+ u v hu hv d p = trans (at-+c u v d) (cong₂ _+_ (hu d p) (hv d p))

  Hi-+ : ∀ {m t} (u v : Vec Nat m) → Hi t u → Hi t v → Hi t (u +c v)
  Hi-+ u v hu hv d p = trans (at-+c u v d) (cong₂ _+_ (hu d p) (hv d p))

  divM : ∀ M′ i → Σ Nat (λ k → Σ Nat (λ r → (r < suc M′) × (i ≡ k * suc M′ + r)))
  divM M′ zero    = 0 , 0 , s≤s z≤n , refl
  divM M′ (suc i) with divM M′ i
  ... | (k , r , l , e) with lt-or-eq r M′ l
  ...   | inj₁ p    = k , suc r , s≤s p , trans (cong suc e) (sym (+-suc (k * suc M′) r))
    where open import CaTTExp.Strict.Bag using (+-suc)
  ...   | inj₂ refl = suc k , 0 , s≤s z≤n ,
                      trans (cong suc (trans e (+-comm (k * suc r) r))) (sym (+-zero (suc (r + k * suc r))))
    where open import CaTTExp.Strict.Bag using (+-comm; +-zero)

  *-mono : ∀ {a b} M → a ≤ b → a * M ≤ b * M
  *-mono M z≤n             = z≤n
  *-mono M (s≤s {m} {n} p) = +-mono M (*-mono M p)
    where
    +-mono : ∀ M {x y} → x ≤ y → M + x ≤ M + y
    +-mono zero    p = p
    +-mono (suc M) p = s≤s (+-mono M p)

module TensorOrd {N M : Nat} (B : Basis N) (C : Basis M) (HB : Hyp B) (HC : Hyp C) where
  open Tensor B C
  open TensorLay B C
  open Blocks {M}
  private
    module B = Basis B
    module C = Basis C
    gK = B.gdeg
    g = λ k → at 0 gK k

    lpos : Nat → Nat → Nat
    lpos k r = if odd (g k) then M ∸ suc r else r

    lpos< : ∀ k r → r < M → lpos k r < M
    lpos< k r l with odd (g k)
    ... | true  = ∸suc< M r l
    ... | false = l

    lin-unit : ∀ {P m} i → i < m → (vs : Vec (Vec Nat P) m) → lin (unit {m} i) vs ≡ at 0c vs i
    lin-unit {P} {suc m} zero    _       (v ∷ vs) =
      trans (cong₂ _+c_ (trans (+c-comm v 0c) (+c-id v)) (lin-0 vs)) (trans (+c-comm v 0c) (+c-id v))
    lin-unit {P} {suc m} (suc i) (s≤s l) (v ∷ vs) = trans (+c-id (lin (unit {m} i) vs)) (lin-unit i l vs)

    unit-at : ∀ {m} k k′ → at 0 (unit {m} k) k′ ≡ 0 ⊎ k′ ≡ k
    unit-at {zero}  k       k′       = inj₁ refl
    unit-at {suc m} zero    zero     = inj₂ refl
    unit-at {suc m} zero    (suc k′) = inj₁ (at-0c {m} k′)
    unit-at {suc m} (suc k) zero     = inj₁ refl
    unit-at {suc m} (suc k) (suc k′) with unit-at {m} k k′
    ... | inj₁ z = inj₁ z
    ... | inj₂ e = inj₂ (cong suc e)

    unit-self : ∀ {m} k → k < m → at 0 (unit {m} k) k ≡ 1
    unit-self {suc m} zero    _       = refl
    unit-self {suc m} (suc k) (s≤s l) = unit-self {m} k l

    row-outer : ∀ {P} (f : Vec Nat P) (x : Vec Nat M) k′ → at 0c (outer f x) k′ ≡ at 0 f k′ ⊙ x
    row-outer f x k′ = at-map (λ a → a ⊙ x) 0 0c refl f k′

    -- D α on the generator k⊗l.
    D-gen : ∀ α k l → k < N → l < M →
            D α (outer (unit {N} k) (unit {M} l)) ≡ outer (at 0c (bK α) k) (unit {M} l) +m outer (unit {N} k) (at 0c (bL (sg (even (g k)) α)) l)
    D-gen α k l kN lM =
      cong₂ _+m_ (trans (osum-outer (bK α) (unit {N} k) (unit {M} l)) (cong (λ f → outer f (unit {M} l)) (lin-unit k kN (bK α))))
                 (trans (outer-row gK bL α (unit {N} k) (unit {M} l) (not (even (g k))) supp)
                        (cong (outer (unit {N} k)) (trans (cong (λ s → lin (unit {M} l) (bL s)) σeq) (lin-unit l lM (bL (sg (even (g k)) α))))))
      where
      supp : ∀ k′ → at 0 (unit {N} k) k′ ≡ 0 ⊎ even (at 0 gK k′) ≡ not (not (even (g k)))
      supp k′ with unit-at {N} k k′
      ... | inj₁ z    = inj₁ z
      ... | inj₂ refl = inj₂ (sym (not-not (even (g k))))
      σeq : sg (not (even (g k))) (not α) ≡ sg (even (g k)) α
      σeq = trans (sg-flip (even (g k)) (not α)) (cong (sg (even (g k))) (not-not α))

    at-rv : ∀ {A : Set} (d : A) b (v : Vec A M) r → r < M → at d (rv b v) r ≡ at d v (if b then M ∸ suc r else r)
    at-rv d true  v r l = at-rev d v r l
    at-rv d false v r l = refl

    -- The basis element at position k·M + r.
    atB : ∀ α k r → k < N → r < M → at 0c (flatA gK (fam α)) (k * M + r) ≡ flatA gK (D α (outer (unit {N} k) (unit {M} (lpos k r))))
    atB α k r kN rM =
      trans (at-flat 0c (rowf 0c) gK (fam α) k r kN rM)
      (trans (cong (λ R → at 0c (rv (odd (g k)) R) r) (trans (at-map rowf 0c (rowf 0c) refl (units N) k) (cong rowf (at-units N k kN))))
      (trans (at-rv 0c (odd (g k)) (rowf (unit {N} k)) r rM)
      (trans (at-def 0c (fD′ (unit {N} k) 0c) (rowf (unit {N} k)) (lpos k r) (lpos< k r rM))
      (trans (at-map (fD′ (unit {N} k)) 0c (fD′ (unit {N} k) 0c) refl (units M) (lpos k r))
             (cong (fD′ (unit {N} k)) (at-units M (lpos k r) (lpos< k r rM)))))))
      where
      fD′ : Vec Nat N → Vec Nat M → Vec Nat (N * M)
      fD′ u v = flatA gK (D α (outer u v))
      rowf : Vec Nat N → Vec (Vec Nat (N * M)) M
      rowf u = mapV (fD′ u) (units M)

    lo-row : ∀ r b → r < M → Lo r (rv (not b) (at 0c (bL (sg b false)) (if not b then M ∸ suc r else r)))
    lo-row r true  rM = Hyp.ordm HC r
    lo-row r false rM d p with ≤-dec M d
    ... | inj₁ Md = at-out 0 (revV (at 0c C.bplus (M ∸ suc r))) d Md
    ... | inj₂ dM = trans (at-rev 0 (at 0c C.bplus (M ∸ suc r)) d dM) (Hyp.ordp HC (M ∸ suc r) (M ∸ suc d) (∸-anti M (suc r) (suc d) (s≤s p)))

    hi-row : ∀ r b → r < M → Hi (suc r) (rv (not b) (at 0c (bL (sg b true)) (if not b then M ∸ suc r else r)))
    hi-row r true  rM d p = Hyp.ordp HC r d (≤-pred p)
    hi-row r false rM d p =
      trans (at-rev 0 (at 0c C.bminus (M ∸ suc r)) d (≤-trans p rM)) (Hyp.ordm HC (M ∸ suc r) (M ∸ suc d) (∸-anti M (suc d) (suc r) p))

    lo-gen : ∀ k r → k < N → r < M → Lo (k * M + r) (flatA gK (D false (outer (unit {N} k) (unit {M} (lpos k r)))))
    lo-gen k r kN rM =
      subst (Lo (k * M + r)) (sym (trans (cong (flatA gK) (D-gen false k l kN (lpos< k r rM))) (flat-+ gK _ _)))
        (Lo-+ (flatA gK (outer (at 0c B.bminus k) (unit {M} l))) (flatA gK (outer (unit {N} k) y))
          (λ d q → LoRows gK k (outer (at 0c B.bminus k) (unit {M} l)) colz d (≤-trans (≤-+r (k * M) r) q))
          (LoBlock gK k r (outer (unit {N} k) y) kN rowz
                   (subst (λ w → Lo r (rv (odd (g k)) w)) (sym (trans (row-outer (unit {N} k) y k) (trans (cong (_⊙ y) (unit-self {N} k kN)) (⊙1 y))))
                          (lo-row r (even (g k)) rM))))
      where
      l = lpos k r
      y = at 0c (bL (sg (even (g k)) false)) l
      colz : ∀ k′ → k ≤ k′ → at 0c (outer (at 0c B.bminus k) (unit {M} l)) k′ ≡ 0c
      colz k′ q = trans (row-outer (at 0c B.bminus k) (unit {M} l) k′) (cong (_⊙ unit l) (Hyp.ordm HB k k′ q))
      rowz : ∀ k′ → k < k′ → at 0c (outer (unit {N} k) y) k′ ≡ 0c
      rowz k′ q with unit-at {N} k k′
      ... | inj₁ z    = trans (row-outer (unit {N} k) y k′) (cong (_⊙ y) z)
      ... | inj₂ refl = ⊥-elim (≤-<-⊥ (≤-refl k) q)

    hi-gen : ∀ k r → k < N → r < M → Hi (suc (k * M + r)) (flatA gK (D true (outer (unit {N} k) (unit {M} (lpos k r)))))
    hi-gen k r kN rM =
      subst (Hi (suc (k * M + r))) (sym (trans (cong (flatA gK) (D-gen true k l kN (lpos< k r rM))) (flat-+ gK _ _)))
        (Hi-+ (flatA gK (outer (at 0c B.bplus k) (unit {M} l))) (flatA gK (outer (unit {N} k) y))
          (λ d q → HiRows gK (suc k) (outer (at 0c B.bplus k) (unit {M} l)) colz d (≤-trans q bound))
          (λ d q → HiBlock gK k (suc r) (outer (unit {N} k) y) kN rM rowz
                     (subst (λ w → Hi (suc r) (rv (odd (g k)) w)) (sym (trans (row-outer (unit {N} k) y k) (trans (cong (_⊙ y) (unit-self {N} k kN)) (⊙1 y))))
                            (hi-row r (even (g k)) rM))
                     d (subst (d <_) (sym (+-suc (k * M) r)) q)))
      where
      open import CaTTExp.Strict.Bag using (+-suc; +-comm)
      l = lpos k r
      y = at 0c (bL (sg (even (g k)) true)) l
      colz : ∀ k′ → k′ < suc k → at 0c (outer (at 0c B.bplus k) (unit {M} l)) k′ ≡ 0c
      colz k′ q = trans (row-outer (at 0c B.bplus k) (unit {M} l) k′) (cong (_⊙ unit l) (Hyp.ordp HB k k′ (≤-pred q)))
      rowz : ∀ k′ → k′ < k → at 0c (outer (unit {N} k) y) k′ ≡ 0c
      rowz k′ q with unit-at {N} k k′
      ... | inj₁ z    = trans (row-outer (unit {N} k) y k′) (cong (_⊙ y) z)
      ... | inj₂ refl = ⊥-elim (≤-<-⊥ (≤-refl k′) q)
      bound : suc (k * M + r) ≤ suc k * M
      bound = subst (suc (k * M + r) ≤_) (+-comm (k * M) M) (subst (_≤ k * M + M) (+-suc (k * M) r) (+mono (k * M) rM))
        where
        +mono : ∀ a {x y} → x ≤ y → a + x ≤ a + y
        +mono zero    p = p
        +mono (suc a) p = s≤s (+mono a p)

  ordm′ : ∀ i d → i ≤ d → at0 (at 0c (flatA gK (fam false)) i) d ≡ 0
  ordm′ i d p = go M refl
    where
    go : ∀ M′ → M ≡ M′ → at0 (at 0c (flatA gK (fam false)) i) d ≡ 0
    go zero    e = trans (cong (λ v → at0 v d) (at-out 0c (flatA gK (fam false)) i (subst (_≤ i) (sym (trans (cong (N *_) e) (*0 N))) z≤n)))
                         (at-0c {N * M} d)
      where
      *0 : ∀ n → n * 0 ≡ 0
      *0 zero    = refl
      *0 (suc n) = *0 n
    go (suc M′) refl with divM M′ i
    ... | (k , r , rM , refl) with ≤-dec N k
    ...   | inj₁ Nk = trans (cong (λ v → at0 v d) (at-out 0c (flatA gK (fam false)) (k * M + r) (≤-trans (*-mono M Nk) (≤-+r (k * M) r))))
                            (at-0c {N * M} d)
    ...   | inj₂ kN = trans (cong (λ v → at0 v d) (atB false k r kN rM)) (lo-gen k r kN rM d p)

  ordp′ : ∀ i d → d ≤ i → at0 (at 0c (flatA gK (fam true)) i) d ≡ 0
  ordp′ i d p = go M refl
    where
    go : ∀ M′ → M ≡ M′ → at0 (at 0c (flatA gK (fam true)) i) d ≡ 0
    go zero    e = trans (cong (λ v → at0 v d) (at-out 0c (flatA gK (fam true)) i (subst (_≤ i) (sym (trans (cong (N *_) e) (*0 N))) z≤n)))
                         (at-0c {N * M} d)
      where
      *0 : ∀ n → n * 0 ≡ 0
      *0 zero    = refl
      *0 (suc n) = *0 n
    go (suc M′) refl with divM M′ i
    ... | (k , r , rM , refl) with ≤-dec N k
    ...   | inj₁ Nk = trans (cong (λ v → at0 v d) (at-out 0c (flatA gK (fam true)) (k * M + r) (≤-trans (*-mono M Nk) (≤-+r (k * M) r))))
                            (at-0c {N * M} d)
    ...   | inj₂ kN = trans (cong (λ v → at0 v d) (atB true k r kN rM)) (hi-gen k r kN rM d (s≤s p))

------------------------------------------------------------------------
-- Everything but unitality: K ⊗ L satisfies `Hyp` as soon as its atoms
-- are unital.

module TensorAll {N M : Nat} (B : Basis N) (C : Basis M) (HB : Hyp B) (HC : Hyp C)
                 (dgpB : DegP B) (dgmB : DegM B) (dgpC : DegP C) (dgmC : DegM C) where
  open TensorHyp B C HB HC dgpB dgmB dgpC dgmC public
  open TensorOrd B C HB HC public using (ordm′; ordp′)
  open import CaTTExp.Strict.Atoms using (module Atom)

  hyp⊗ : (∀ i → i < N * M → Atom.Cells.Deg.Unital B⊗ dd′ deg-dp′ deg-dm′ i) → Hyp B⊗
  hyp⊗ un = record
    { dd = dd′ ; deg-dp = deg-dp′ ; deg-dm = deg-dm′
    ; ordm = ordm′ ; ordp = ordp′ ; aug1 = aug1′ ; unital = un }

------------------------------------------------------------------------
-- Checks: with L = λD¹ the layout is the Gray cylinder of `Cylinder`.

module _ where
  open import CaTTExp.Strict.BasisCheck using (BD¹; BD²)
  open import CaTTExp.Strict.Cylinder using (module Cyl)

  square-is-cyl : TensorLay.B⊗ BD¹ BD¹ ≡ Cyl.B′ BD¹
  square-is-cyl = refl

  D²⊗D¹-is-cyl : TensorLay.B⊗ BD² BD¹ ≡ Cyl.B′ BD²
  D²⊗D¹-is-cyl = refl

  -- λD¹ ⊗ λD² (the other way round) and λD² ⊗ λD², checked by the decision
  -- procedures of BasisCheck, unitality included.
  open import CaTTExp.Strict.BasisCheck using (mkHyp)

  D¹⊗D²-check : Hyp (TensorLay.B⊗ BD¹ BD²)
  D¹⊗D²-check = mkHyp (TensorLay.B⊗ BD¹ BD²) refl refl refl tt tt refl tt

  D²⊗D²-check : Hyp (TensorLay.B⊗ BD² BD²)
  D²⊗D²-check = mkHyp (TensorLay.B⊗ BD² BD²) refl refl refl tt tt refl tt
