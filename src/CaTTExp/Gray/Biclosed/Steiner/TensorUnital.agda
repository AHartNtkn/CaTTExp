------------------------------------------------------------------------
-- Strong Steiner under the tensor (ledger C5f): unitality, and the full
-- strong Steiner property for every code.
--
-- For basis elements i of a and x of K with cell data (`CellData`), the
-- element (i, x) of a ∷ K has cell data given by the tensor of chains
--   ch α k (j, y) = [deg j + deg y = k] · chA α (deg j) j
--                                        · chK (flip (deg j) α) (deg y) y,
-- i.e. ⟨(i, x)⟩^α_k = Σ_{p+q=k} ⟨i⟩^α_p ⊗ ⟨x⟩^{±α}_q, the sign of the
-- K-factor flipping with the degree of the a-factor (`tensorCD`).
-- Globularity is the telescoping of ∂(⟨i⟩_p ⊗ ⟨x⟩_q) (`t-glob`, using
-- `dP-split`); disjointness holds because at each degree one of the
-- two factors has disjoint parts (`t-disj`); ε of the degree-0 chain
-- is ε⟨i⟩^α_0 · ε⟨x⟩^α_0 = 1 (`t-unit`).
--
-- So every element of every code has cell data when the atoms satisfy
-- the degree condition, ∂∂ = 0 and unitality (`code-CD`), and every
-- code is unital (`code-unital`).  With parts 1–3 of `TensorSteiner`
-- this gives the full strong Steiner property for every code whose
-- atoms are strong Steiner (`code-SS`), and every code when every
-- named basis is (`all-codes-SS`).
-- No postulates.
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.TensorUnital (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum
open import CaTTExp.Gray.Biclosed.Steiner.Codes
open import CaTTExp.Gray.Biclosed.Steiner.StrongSteiner
open import CaTTExp.Gray.Biclosed.Steiner.CellData
open import CaTTExp.Gray.Biclosed.Steiner.TensorSteiner nmFB
  using (codeFB; t-degs; t-disj; t-aug; t-chain; AllH; []ʰ; _∷ʰ_; code-height)
open import CaTTExp.Gray.Biclosed.Steiner.GlobeSteiner using (globes-all)
open Codes nmFB

------------------------------------------------------------------------
-- Order on Nat, through witnesses

private
  lt-dec : ∀ a b → ((a <ℕ b) ≡ true) ⊎ ((a <ℕ b) ≡ false)
  lt-dec a b with a <ℕ b
  ... | true  = inj₁ refl
  ... | false = inj₂ refl

  eq-dec : ∀ a b → ((a ==ℕ b) ≡ true) ⊎ ((a ==ℕ b) ≡ false)
  eq-dec a b with a ==ℕ b
  ... | true  = inj₁ refl
  ... | false = inj₂ refl

  ≡T : ∀ {b} → b ≡ true → T b
  ≡T refl = tt

  ≡F : ∀ {b} → b ≡ false → T (not b)
  ≡F refl = tt

  le-of : ∀ a P → T (not (a <ℕ P)) → Σ Nat (λ n → a ≡ P + n)
  le-of zero    zero    _ = 0 , refl
  le-of zero    (suc P) ()
  le-of (suc a) zero    _ = suc a , refl
  le-of (suc a) (suc P) q with le-of a P q
  ... | n , e = n , cong suc e

  lt-of : ∀ a P → T (a <ℕ P) → Σ Nat (λ n → P ≡ suc (a + n))
  lt-of a       zero    ()
  lt-of zero    (suc P) _ = P , refl
  lt-of (suc a) (suc P) q with lt-of a P q
  ... | n , e = n , cong suc e

  lt-from : ∀ a n → T (a <ℕ suc (a + n))
  lt-from zero    n = tt
  lt-from (suc a) n = lt-from a n

  nlt-from : ∀ P n → T ((P + n) <ℕ P) → ⊥
  nlt-from zero    n ()
  nlt-from (suc P) n q = nlt-from P n q

  n≢suc : ∀ n k → n ≡ suc (n + k) → ⊥
  n≢suc zero    k ()
  n≢suc (suc n) k e = n≢suc n k (suc-inj e)
    where suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
          suc-inj refl = refl

  -- a ≥ P, b ≥ Q gives a + b ≮ P + Q
  N1 : ∀ a P b Q → T (not (a <ℕ P)) → T (not (b <ℕ Q)) → T ((a + b) <ℕ (P + Q)) → ⊥
  N1 a P b Q p q r with le-of a P p | le-of b Q q
  ... | n , refl | m , refl = nlt-from (P + Q) (n + m) (T-subst (cong (_<ℕ (P + Q)) (+-inter P n Q m)) r)

  -- a < P and a + b = P + Q give Q < b
  N2 : ∀ a P b Q → T (a <ℕ P) → a + b ≡ P + Q → T (Q <ℕ b)
  N2 a P b Q p e with lt-dec Q b
  ... | inj₁ h = ≡T h
  ... | inj₂ h with lt-of a P p | le-of Q b (≡F h)
  ...   | n , refl | m , refl =
    ⊥-elim (n≢suc (a + b) (n + m) (trans e (cong suc (+-inter a n b m))))

  -- a ≠ P and a ≮ P give P < a
  N3 : ∀ a P → (a ≡ P → ⊥) → (a <ℕ P) ≡ false → T (P <ℕ a)
  N3 a P ne h with le-of a P (≡F h)
  ... | zero  , e = ⊥-elim (ne (trans e (+-zero P)))
  ... | suc n , e = T-subst (cong (P <ℕ_) (sym (trans e (+-suc P n)))) (lt-from P n)

  -- P + Q < a + b and a ≤ P give Q < b
  N4 : ∀ a P b Q → T ((P + Q) <ℕ (a + b)) → (P <ℕ a) ≡ false → T (Q <ℕ b)
  N4 a P b Q r h with lt-dec Q b
  ... | inj₁ h′ = ≡T h′
  ... | inj₂ h′ with le-of P a (≡F h) | le-of Q b (≡F h′)
  ...   | n , refl | m , refl = ⊥-elim (nlt-from (a + b) (n + m) (T-subst (cong (_<ℕ (a + b)) (+-inter a n b m)) r))

  ==-+l : ∀ P a b → (P + a ==ℕ P + b) ≡ (a ==ℕ b)
  ==-+l zero    a b = refl
  ==-+l (suc P) a b = ==-+l P a b

------------------------------------------------------------------------
-- Small lemmas

private
  sel0 : ∀ b → sel b 0 ≡ 0
  sel0 true  = refl
  sel0 false = refl

  sel-nz : ∀ b n → T (not (sel b n ==ℕ 0)) → T b
  sel-nz true  n _ = tt
  sel-nz false n ()

  -- a number that is nonzero only when an impossible equation holds is 0
  z-of : ∀ {A : Set} {u v : A} (c : Nat) → (T (not (c ==ℕ 0)) → u ≡ v) → (u ≡ v → ⊥) → c ≡ 0
  z-of zero    _ _  = refl
  z-of (suc c) h ne = ⊥-elim (ne (h tt))

  nz-of : ∀ {c n} → c ≡ suc n → T (not (c ==ℕ 0))
  nz-of refl = tt

  sel-rearr : ∀ b X Y A → sel b (X * Y) * A ≡ sel b Y * (X * A)
  sel-rearr true  X Y A = trans (cong (_* A) (*-comm X Y)) (*-assoc Y X A)
  sel-rearr false X Y A = refl

  sel-rearr₂ : ∀ b X Y A → sel b (X * Y) * A ≡ sel b X * (Y * A)
  sel-rearr₂ true  X Y A = *-assoc X Y A
  sel-rearr₂ false X Y A = refl

  rearr : ∀ a b c d → (a * b) * (c * d) ≡ (a * c) * (b * d)
  rearr a b c d =
    trans (*-assoc a b (c * d))
    (trans (cong (a *_) (trans (sym (*-assoc b c d)) (trans (cong (_* d) (*-comm b c)) (*-assoc c b d))))
           (sym (*-assoc a c (b * d))))

  not-not : ∀ b → not (not b) ≡ b
  not-not true  = refl
  not-not false = refl

  even-suc : ∀ n → even (suc n) ≡ not (even n)
  even-suc zero          = refl
  even-suc (suc zero)    = refl
  even-suc (suc (suc n)) = even-suc n

  flip-suc : ∀ n β → flip (suc n) β ≡ not (flip n β)
  flip-suc n β rewrite even-suc n with even n
  ... | true  = refl
  ... | false = sym (not-not β)

  flip-false : ∀ n → flip n false ≡ not (flip n true)
  flip-false n with even n
  ... | true  = refl
  ... | false = refl

  flip-α : ∀ n α → flip n α ≡ (if α then flip n true else flip n false)
  flip-α n true  = refl
  flip-α n false = refl

  flip-cases : ∀ d → ((flip d true ≡ true) × (flip d false ≡ false)) ⊎ ((flip d true ≡ false) × (flip d false ≡ true))
  flip-cases d with even d
  ... | true  = inj₁ (refl , refl)
  ... | false = inj₂ (refl , refl)

  -- the two telescoping identities
  ar1 : ∀ X Y u₊ u₋ a₊ a₋ v₁ v₂ → u₊ + a₋ ≡ u₋ + a₊ → v₁ + X ≡ v₂ + Y →
        (X * u₊ + a₊ * v₁) + a₋ * X ≡ (X * u₋ + a₊ * v₂) + a₊ * Y
  ar1 X Y u₊ u₋ a₊ a₋ v₁ v₂ eu ev =
    trans (+-assoc (X * u₊) (a₊ * v₁) (a₋ * X))
    (trans (cong ((X * u₊) +_) (+-comm (a₊ * v₁) (a₋ * X)))
    (trans (sym (+-assoc (X * u₊) (a₋ * X) (a₊ * v₁)))
    (trans (cong (_+ a₊ * v₁) (trans (cong (X * u₊ +_) (*-comm a₋ X)) (sym (distribˡ X u₊ a₋))))
    (trans (cong (λ t → X * t + a₊ * v₁) eu)
    (trans (cong (_+ a₊ * v₁) (distribˡ X u₋ a₊))
    (trans (+-assoc (X * u₋) (X * a₊) (a₊ * v₁))
    (trans (cong (X * u₋ +_) (trans (cong (_+ a₊ * v₁) (*-comm X a₊))
                             (trans (sym (distribˡ a₊ X v₁))
                             (trans (cong (a₊ *_) (trans (+-comm X v₁) ev)) (distribˡ a₊ v₂ Y)))))
           (sym (+-assoc (X * u₋) (a₊ * v₂) (a₊ * Y))))))))))

  ar2 : ∀ X Y u₊ u₋ a₊ a₋ v₁ v₂ → u₊ + a₋ ≡ u₋ + a₊ → v₁ + X ≡ v₂ + Y →
        (Y * u₊ + a₋ * v₁) + a₋ * X ≡ (Y * u₋ + a₋ * v₂) + a₊ * Y
  ar2 X Y u₊ u₋ a₊ a₋ v₁ v₂ eu ev =
    trans (+-assoc (Y * u₊) (a₋ * v₁) (a₋ * X))
    (trans (cong (Y * u₊ +_) (trans (sym (distribˡ a₋ v₁ X)) (trans (cong (a₋ *_) ev) (distribˡ a₋ v₂ Y))))
    (trans (cong (Y * u₊ +_) (+-comm (a₋ * v₂) (a₋ * Y)))
    (trans (sym (+-assoc (Y * u₊) (a₋ * Y) (a₋ * v₂)))
    (trans (cong (_+ a₋ * v₂) (trans (cong (Y * u₊ +_) (*-comm a₋ Y)) (sym (distribˡ Y u₊ a₋))))
    (trans (cong (λ t → Y * t + a₋ * v₂) eu)
    (trans (cong (_+ a₋ * v₂) (distribˡ Y u₋ a₊))
    (trans (+-assoc (Y * u₋) (Y * a₊) (a₋ * v₂))
    (trans (cong (Y * u₋ +_) (+-comm (Y * a₊) (a₋ * v₂)))
    (trans (sym (+-assoc (Y * u₋) (a₋ * v₂) (Y * a₊)))
           (cong ((Y * u₋ + a₋ * v₂) +_) (*-comm Y a₊)))))))))))

  -- the globularity identity at one cell, with the signs abstracted
  glob-gen : ∀ α (t₁ t₂ s : Bool) (Yv : Nat) (aA uA bK : Bool → Nat) (vK : Bool → Bool → Nat) →
    t₂ ≡ not t₁ → s ≡ (if α then t₁ else t₂) → Yv ≡ bK (not s) →
    uA true + aA false ≡ uA false + aA true →
    (∀ s → vK s true + bK false ≡ vK s false + bK true) →
    (Yv * uA true + aA α * vK s t₁) + aA false * bK t₂ ≡ (Yv * uA false + aA α * vK s t₂) + aA true * bK t₁
  glob-gen true  true  ._ ._ ._ aA uA bK vK refl refl refl gA gK =
    ar1 (bK false) (bK true) (uA true) (uA false) (aA true) (aA false) (vK true true) (vK true false) gA (gK true)
  glob-gen true  false ._ ._ ._ aA uA bK vK refl refl refl gA gK =
    ar1 (bK true) (bK false) (uA true) (uA false) (aA true) (aA false) (vK false false) (vK false true) gA (sym (gK false))
  glob-gen false true  ._ ._ ._ aA uA bK vK refl refl refl gA gK =
    ar2 (bK false) (bK true) (uA true) (uA false) (aA true) (aA false) (vK false true) (vK false false) gA (gK false)
  glob-gen false false ._ ._ ._ aA uA bK vK refl refl refl gA gK =
    ar2 (bK true) (bK false) (uA true) (uA false) (aA true) (aA false) (vK true false) (vK true true) gA (sym (gK true))

------------------------------------------------------------------------
-- The tensor of cell data

module _ (a : AC) (K : Code)
         (dA : ∀ i j → T (SS.degAt (fbA a) i j)) (dK : ∀ x y → T (SS.degAt (codeFB K) x y)) where
  private
    module CA = CD (fbA a)
    module CK = CD (codeFB K)
    module CT = CD (codeFB (a ∷ K))
    EA = enumA a
    EK = enumEl K
    elsA = els EA
    elsK = els EK

  -- ∂ in a ∷ K at (m, z): the a-part and the K-part
  dP-split : ∀ (C : El (a ∷ K) → Nat) β m z →
    CT.dP β C (m , z) ≡ Σl elsA (λ j → C (j , z) * bdA a β j m) + Σl elsK (λ y → C (m , y) * bd K (flip (degA a m) β) y z)
  dP-split C β m z =
    trans (Σ-pairs elsA elsK (λ v → C v * bd (a ∷ K) β v (m , z)))
    (trans (Σ-cong elsA (λ j →
             trans (Σ-cong elsK (λ y → distribˡ (C (j , y)) (bdA a β j m * δE K y z) (δ EA j m * bd K (flip (degA a j) β) y z)))
                   (Σ-+ elsK (λ y → C (j , y) * (bdA a β j m * δE K y z)) (λ y → C (j , y) * (δ EA j m * bd K (flip (degA a j) β) y z)))))
    (trans (Σ-+ elsA (λ j → Σl elsK (λ y → C (j , y) * (bdA a β j m * δE K y z)))
                     (λ j → Σl elsK (λ y → C (j , y) * (δ EA j m * bd K (flip (degA a j) β) y z))))
           (cong₂ _+_ (Σ-cong elsA L) R)))
    where
      L : ∀ j → Σl elsK (λ y → C (j , y) * (bdA a β j m * δE K y z)) ≡ C (j , z) * bdA a β j m
      L j = trans (Σ-cong elsK (λ y → sym (*-assoc (C (j , y)) (bdA a β j m) (δE K y z))))
                  (Σ-δʳ EK z (λ y → C (j , y) * bdA a β j m))
      sw : ∀ p q r → p * (q * r) ≡ (p * r) * q
      sw p q r = trans (cong (p *_) (*-comm q r)) (sym (*-assoc p r q))
      R : Σl elsA (λ j → Σl elsK (λ y → C (j , y) * (δ EA j m * bd K (flip (degA a j) β) y z))) ≡
          Σl elsK (λ y → C (m , y) * bd K (flip (degA a m) β) y z)
      R = trans (Σ-cong elsA (λ j →
                  trans (Σ-cong elsK (λ y → sw (C (j , y)) (δ EA j m) (bd K (flip (degA a j) β) y z)))
                        (sym (Σ-*ʳ elsK (δ EA j m) (λ y → C (j , y) * bd K (flip (degA a j) β) y z)))))
                (Σ-δʳ EA m (λ j → Σl elsK (λ y → C (j , y) * bd K (flip (degA a j) β) y z)))

  module _ {i : Ix a} {x : El K} (CAi : CA.CellData i) (CKx : CK.CellData x) where
    open CA.CellData CAi renaming (ch to chA; conc to concA; top to topA; above to aboveA;
                                   glob to globA; disj to disjA; unit to unitA)
    open CK.CellData CKx renaming (ch to chK; conc to concK; top to topK; above to aboveK;
                                   glob to globK; disj to disjK; unit to unitK)
    private
      P = degA a i
      Q = deg K x

    tch : Bool → Nat → El (a ∷ K) → Nat
    tch α k (j , y) = sel ((degA a j + deg K y) ==ℕ k) (chA α (degA a j) j * chK (flip (degA a j) α) (deg K y) y)

    t-conc : ∀ α k u → T (SS.nz (codeFB (a ∷ K)) (tch α k u)) → deg (a ∷ K) u ≡ k
    t-conc α k (j , y) n = ==ℕ-sound _ _ (sel-nz _ _ n)

    t-top : ∀ α u → tch α (P + Q) u ≡ δ (enumEl (a ∷ K)) (i , x) u
    t-top α (j , y) =
      trans TT (trans (cong₂ _*_ (topA α j) (topK (flip P α) y)) (sym (δ× EA EK i x j y)))
      where
        dj = degA a j
        dy = deg K y
        TT : tch α (P + Q) (j , y) ≡ chA α P j * chK (flip P α) Q y
        TT with eq-dec dj P
        ... | inj₁ h =
          trans (cong (λ n → sel (n + dy ==ℕ P + Q) (chA α n j * chK (flip n α) dy y)) e)
                (inner (eq-dec dy Q))
          where
            e : dj ≡ P
            e = ==ℕ-sound _ _ (≡T h)
            inner : ((dy ==ℕ Q) ≡ true) ⊎ ((dy ==ℕ Q) ≡ false) →
                    sel (P + dy ==ℕ P + Q) (chA α P j * chK (flip P α) dy y) ≡ chA α P j * chK (flip P α) Q y
            inner (inj₁ h′) =
              trans (cong (λ n → sel (P + n ==ℕ P + Q) (chA α P j * chK (flip P α) n y)) (==ℕ-sound _ _ (≡T h′)))
                    (sel-T _ (==ℕ-refl (P + Q)))
            inner (inj₂ h′) =
              trans (sel-F _ (trans (==-+l P dy Q) h′))
                    (sym (trans (cong (chA α P j *_) (z-of (chK (flip P α) Q y) (concK (flip P α) Q y) (==-false dy Q h′)))
                                (*-zero (chA α P j))))
        ... | inj₂ h =
          trans lhs0 (sym (cong (_* chK (flip P α) Q y) (z-of (chA α P j) (concA α P j) (==-false dj P h))))
          where
            lhs0 : tch α (P + Q) (j , y) ≡ 0
            lhs0 with eq-dec (dj + dy) (P + Q)
            ... | inj₂ s = sel-F _ s
            ... | inj₁ s with lt-dec dj P
            ...   | inj₁ l = trans (cong (sel _) (trans (cong (chA α dj j *_)
                                     (aboveK (flip dj α) dy y (N2 dj P dy Q (≡T l) (==ℕ-sound _ _ (≡T s)))))
                                     (*-zero (chA α dj j))))
                                   (sel0 _)
            ...   | inj₂ l = trans (cong (λ t → sel _ (t * chK (flip dj α) dy y))
                                     (aboveA α dj j (N3 dj P (==-false dj P h) l)))
                                   (sel0 _)

    t-above : ∀ α k u → T ((P + Q) <ℕ k) → tch α k u ≡ 0
    t-above α k (j , y) q with eq-dec (degA a j + deg K y) k
    ... | inj₂ s = sel-F _ s
    ... | inj₁ s with lt-dec P (degA a j)
    ...   | inj₁ l = trans (cong (λ t → sel _ (t * chK (flip (degA a j) α) (deg K y) y)) (aboveA α (degA a j) j (≡T l)))
                           (sel0 _)
    ...   | inj₂ l = trans (cong (sel _) (trans (cong (chA α (degA a j) j *_)
                             (aboveK (flip (degA a j) α) (deg K y) y
                               (N4 (degA a j) P (deg K y) Q (T-subst (cong ((P + Q) <ℕ_) (sym (==ℕ-sound (degA a j + deg K y) k (≡T s)))) q) l)))
                             (*-zero (chA α (degA a j) j))))
                           (sel0 _)

    c-disj : ∀ k u → T (k <ℕ (P + Q)) → tch true k u * tch false k u ≡ 0
    c-disj k (j , y) q with eq-dec (degA a j + deg K y) k
    ... | inj₂ s = cong₂ (λ b c → sel b (chA true dj j * chK (flip dj true) dy y) * sel c (chA false dj j * chK (flip dj false) dy y)) s s
      where dj = degA a j
            dy = deg K y
    ... | inj₁ s =
      trans (cong₂ (λ b c → sel b (chA true dj j * chK (flip dj true) dy y) * sel c (chA false dj j * chK (flip dj false) dy y)) s s)
      (trans (rearr (chA true dj j) (chK (flip dj true) dy y) (chA false dj j) (chK (flip dj false) dy y)) prod0)
      where
        dj = degA a j
        dy = deg K y
        prod0 : (chA true dj j * chA false dj j) * (chK (flip dj true) dy y * chK (flip dj false) dy y) ≡ 0
        prod0 with lt-dec dj P
        ... | inj₁ l = cong (_* (chK (flip dj true) dy y * chK (flip dj false) dy y)) (disjA dj j (≡T l))
        ... | inj₂ l with lt-dec dy Q
        ...   | inj₂ l′ = ⊥-elim (N1 dj P dy Q (≡F l) (≡F l′) (T-subst (cong (_<ℕ (P + Q)) (sym (==ℕ-sound _ _ (≡T s)))) q))
        ...   | inj₁ l′ = trans (cong ((chA true dj j * chA false dj j) *_) kz) (*-zero (chA true dj j * chA false dj j))
          where
            kz : chK (flip dj true) dy y * chK (flip dj false) dy y ≡ 0
            kz with flip-cases dj
            ... | inj₁ (p , p′) = trans (cong₂ (λ b c → chK b dy y * chK c dy y) p p′) (disjK dy y (≡T l′))
            ... | inj₂ (p , p′) = trans (cong₂ (λ b c → chK b dy y * chK c dy y) p p′)
                                        (trans (*-comm (chK false dy y) (chK true dy y)) (disjK dy y (≡T l′)))

    t-unit : ∀ α → Σl (els (enumEl (a ∷ K))) (tch α 0) ≡ 1
    t-unit α =
      trans (Σ-pairs elsA elsK (tch α 0))
      (trans (Σ-cong elsA (λ j → trans (Σ-cong elsK (U j)) (sym (Σ-*ˡ elsK (chA α 0 j) (chK α 0)))))
      (trans (Σ-cong elsA (λ j → trans (cong (chA α 0 j *_) (unitK α)) (*-one (chA α 0 j)))) (unitA α)))
      where
        U : ∀ j y → tch α 0 (j , y) ≡ chA α 0 j * chK α 0 y
        U j y = go (degA a j) refl (deg K y) refl
          where
            go : ∀ n → degA a j ≡ n → ∀ m → deg K y ≡ m → tch α 0 (j , y) ≡ chA α 0 j * chK α 0 y
            go zero    e zero    e′ =
              cong₂ (λ n m → sel (n + m ==ℕ 0) (chA α n j * chK (flip n α) m y)) e e′
            go (suc n) e m       e′ =
              trans (cong (λ n → sel (n + deg K y ==ℕ 0) (chA α n j * chK (flip n α) (deg K y) y)) e)
                    (sym (cong (_* chK α 0 y) (z-of (chA α 0 j) (concA α 0 j) (λ q → sz (trans (sym e) q)))))
              where sz : ∀ {k} → suc k ≡ 0 → ⊥
                    sz ()
            go zero    e (suc m) e′ =
              trans (cong₂ (λ n m → sel (n + m ==ℕ 0) (chA α n j * chK (flip n α) m y)) e e′)
                    (sym (trans (cong (chA α 0 j *_) (z-of (chK α 0 y) (concK α 0 y) (λ q → sz (trans (sym e′) q))))
                                (*-zero (chA α 0 j))))
              where sz : ∀ {k} → suc k ≡ 0 → ⊥
                    sz ()

    t-glob : ∀ α p w → CT.dP true (tch α (suc p)) w + tch false p w ≡ CT.dP false (tch α (suc p)) w + tch true p w
    t-glob α p (m , z) =
      trans (cong (_+ tch false p (m , z)) (split true))
      (trans (core b)
             (sym (cong (_+ tch true p (m , z)) (split false))))
      where
        dm = degA a m
        dz = deg K z
        b = (dm + dz) ==ℕ p
        Y = chK (flip (suc dm) α) dz z
        u : Bool → Nat
        u β = CA.dP β (chA α (suc dm)) m
        v : Bool → Nat
        v β = CK.dP (flip dm β) (chK (flip dm α) (suc dz)) z

        F1 : ∀ β j → tch α (suc p) (j , z) * bdA a β j m ≡ sel b Y * (chA α (suc dm) j * bdA a β j m)
        F1 β j = go (bdA a β j m) refl
          where
            go : ∀ n → bdA a β j m ≡ n → tch α (suc p) (j , z) * bdA a β j m ≡ sel b Y * (chA α (suc dm) j * bdA a β j m)
            go zero e =
              trans (cong (tch α (suc p) (j , z) *_) e)
              (trans (*-zero (tch α (suc p) (j , z)))
                     (sym (trans (cong (λ q → sel b Y * (chA α (suc dm) j * q)) e)
                                 (trans (cong (sel b Y *_) (*-zero (chA α (suc dm) j))) (*-zero (sel b Y))))))
            go (suc n) e =
              trans (cong (_* bdA a β j m)
                      (cong (λ n → sel (n + dz ==ℕ suc p) (chA α n j * chK (flip n α) dz z))
                            (sym (CA.deg-ofB j m β (dA j m) (nz-of e)))))
                    (sel-rearr b (chA α (suc dm) j) Y (bdA a β j m))

        F2 : ∀ β y → tch α (suc p) (m , y) * bd K (flip dm β) y z ≡
                     sel b (chA α dm m) * (chK (flip dm α) (suc dz) y * bd K (flip dm β) y z)
        F2 β y = go (bd K (flip dm β) y z) refl
          where
            go : ∀ n → bd K (flip dm β) y z ≡ n → tch α (suc p) (m , y) * bd K (flip dm β) y z ≡
                                                  sel b (chA α dm m) * (chK (flip dm α) (suc dz) y * bd K (flip dm β) y z)
            go zero e =
              trans (cong (tch α (suc p) (m , y) *_) e)
              (trans (*-zero (tch α (suc p) (m , y)))
                     (sym (trans (cong (λ q → sel b (chA α dm m) * (chK (flip dm α) (suc dz) y * q)) e)
                                 (trans (cong (sel b (chA α dm m) *_) (*-zero (chK (flip dm α) (suc dz) y)))
                                        (*-zero (sel b (chA α dm m)))))))
            go (suc n) e =
              trans (cong (_* bd K (flip dm β) y z)
                      (trans (cong (λ n → sel (dm + n ==ℕ suc p) (chA α dm m * chK (flip dm α) n y))
                                   (sym (CK.deg-ofB y z (flip dm β) (dK y z) (nz-of e))))
                             (cong (λ c → sel c (chA α dm m * chK (flip dm α) (suc dz) y))
                                   (cong (_==ℕ suc p) (+-suc dm dz)))))
                    (sel-rearr₂ b (chA α dm m) (chK (flip dm α) (suc dz) y) (bd K (flip dm β) y z))

        split : ∀ β → CT.dP β (tch α (suc p)) (m , z) ≡ sel b Y * u β + sel b (chA α dm m) * v β
        split β =
          trans (dP-split (tch α (suc p)) β m z)
          (cong₂ _+_ (trans (Σ-cong elsA (F1 β)) (sym (Σ-*ˡ elsA (sel b Y) (λ j → chA α (suc dm) j * bdA a β j m))))
                     (trans (Σ-cong elsK (F2 β))
                            (sym (Σ-*ˡ elsK (sel b (chA α dm m)) (λ y → chK (flip dm α) (suc dz) y * bd K (flip dm β) y z)))))

        core : ∀ c → (sel c Y * u true + sel c (chA α dm m) * v true) + sel c (chA false dm m * chK (flip dm false) dz z) ≡
                     (sel c Y * u false + sel c (chA α dm m) * v false) + sel c (chA true dm m * chK (flip dm true) dz z)
        core false = refl
        core true  =
          glob-gen α (flip dm true) (flip dm false) (flip dm α) Y
                   (λ γ → chA γ dm m) u (λ γ → chK γ dz z) (λ s β′ → CK.dP β′ (chK s (suc dz)) z)
                   (flip-false dm) (flip-α dm α) (cong (λ t → chK t dz z) (flip-suc dm α))
                   (globA α dm m) (λ s → globK s dz z)

    tensorCD : CT.CellData (i , x)
    tensorCD = record { ch = tch ; conc = t-conc ; top = t-top ; above = t-above
                      ; glob = t-glob ; disj = c-disj ; unit = t-unit }

------------------------------------------------------------------------
-- Every code

-- the empty code: one cell of degree 0
nilCD : CD.CellData (codeFB []) tt
nilCD = record
  { ch    = λ α p _ → sel (p ==ℕ 0) 1
  ; conc  = λ { α zero tt _ → refl ; α (suc p) tt () }
  ; top   = λ α _ → refl
  ; above = λ { α zero tt () ; α (suc p) tt _ → refl }
  ; glob  = λ α p _ → refl
  ; disj  = λ p _ ()
  ; unit  = λ α → refl
  }

-- the Steiner conditions used for unitality, on each atom of a code
record AtomOK (a : AC) : Set where
  field
    degs   : ∀ x y → T (SS.degAt (fbA a) x y)
    chain  : ∀ x z → T (SS.chainAt (fbA a) x z)
    unital : ∀ α x → T (SS.unitAt (fbA a) α x)

data AllOK : Code → Set where
  []ᵒ  : AllOK []
  _∷ᵒ_ : ∀ {a K} → AtomOK a → AllOK K → AllOK (a ∷ K)

code-degs : ∀ K → AllOK K → ∀ u v → T (SS.degAt (codeFB K) u v)
code-degs []      []ᵒ       tt tt = tt
code-degs (a ∷ K) (o ∷ᵒ os) = t-degs a K (AtomOK.degs o) (code-degs K os)

code-CD : ∀ K → AllOK K → ∀ u → CD.CellData (codeFB K) u
code-CD []      []ᵒ       tt      = nilCD
code-CD (a ∷ K) (o ∷ᵒ os) (i , x) =
  tensorCD a K (AtomOK.degs o) (code-degs K os)
           (CD.Atom.atomCD (fbA a) (AtomOK.degs o) (AtomOK.chain o) (AtomOK.unital o) i)
           (code-CD K os x)

code-unital : ∀ K → AllOK K → ∀ α u → T (SS.unitAt (codeFB K) α u)
code-unital K os α u = CD.cd-unital (codeFB K) (code-CD K os u) α

------------------------------------------------------------------------
-- The strong Steiner property for every code

data AllSS : Code → Set where
  []ˢ  : AllSS []
  _∷ˢ_ : ∀ {a K} → SS.StrongSteiner (fbA a) → AllSS K → AllSS (a ∷ K)

private
  okOf : ∀ {K} → AllSS K → AllOK K
  okOf []ˢ       = []ᵒ
  okOf (s ∷ˢ ss) = record { degs = SS.StrongSteiner.degs s ; chain = SS.StrongSteiner.chain s
                          ; unital = SS.StrongSteiner.unital s } ∷ᵒ okOf ss

  hOf : ∀ {K} → AllSS K → AllH K
  hOf []ˢ       = []ʰ
  hOf (s ∷ˢ ss) = SS.StrongSteiner.height s ∷ʰ hOf ss

code-disj : ∀ K → AllSS K → ∀ u v → T (SS.disjAt (codeFB K) u v)
code-disj []      []ˢ       tt tt = tt
code-disj (a ∷ K) (s ∷ˢ ss) =
  t-disj a K (SS.StrongSteiner.degs s) (code-degs K (okOf ss)) (SS.StrongSteiner.disj s) (code-disj K ss)

code-chain : ∀ K → AllSS K → ∀ u v → T (SS.chainAt (codeFB K) u v)
code-chain []      []ˢ       tt tt = tt
code-chain (a ∷ K) (s ∷ˢ ss) =
  t-chain a K (SS.StrongSteiner.degs s) (SS.StrongSteiner.chain s) (code-chain K ss)

code-aug : ∀ K → AllSS K → ∀ u → T (SS.augAt (codeFB K) u)
code-aug []      []ˢ       tt = tt
code-aug (a ∷ K) (s ∷ˢ ss) =
  t-aug a K (SS.StrongSteiner.degs s) (code-degs K (okOf ss)) (SS.StrongSteiner.aug s) (code-aug K ss)

-- every code whose atoms are strong Steiner is strong Steiner (C5f)
code-SS : ∀ K → AllSS K → SS.StrongSteiner (codeFB K)
code-SS K ss = record
  { degs   = code-degs K (okOf ss)
  ; disj   = code-disj K ss
  ; chain  = code-chain K ss
  ; aug    = code-aug K ss
  ; unital = code-unital K (okOf ss)
  ; height = code-height K (hOf ss)
  }

-- so, when every named basis is strong Steiner, every code is
-- (globes are strong Steiner in every dimension, `globes-all`)
all-codes-SS : (∀ n → SS.StrongSteiner (nmFB n)) → ∀ K → SS.StrongSteiner (codeFB K)
all-codes-SS nm K = code-SS K (atoms K)
  where
    atoms : ∀ K → AllSS K
    atoms []              = []ˢ
    atoms (globe n ∷ K)   = globes-all n ∷ˢ atoms K
    atoms (named n ∷ K)   = nm n ∷ˢ atoms K
