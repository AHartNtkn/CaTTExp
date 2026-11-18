------------------------------------------------------------------------
-- The lower cut behind the swap lemma (ledger A5, step L5; outside
-- response §4.1, Steiner Prop. 5.9).
--
-- Let y #ᵣ y′ be defined, y with the rows of ⟨b⟩ above r and y′ with
-- the rows of ⟨c⟩ above r, where c < b in the basis order. Then
--   * r > 0 (`no-cut-0`: at r = 0 the augmentation would be 2), and
--   * y #ᵣ y′ = v #ᵣ₋₁ u with v having the rows of ⟨c⟩ above r and u
--     those of ⟨b⟩ (`lower-cut`).
-- Row r of y #ᵣ y′ is (⟨b⟩ᵣ⁻ + ⟨c⟩ᵣ⁻ + w, ⟨b⟩ᵣ⁺ + ⟨c⟩ᵣ⁺ + w) with
-- w ≥ 0; w is split at index b, its part below b going to v.
------------------------------------------------------------------------
module CaTTExp.Strict.LowerCut where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; ≤-refl; ≤-trans; ≤-suc; <→≤; ≤-<-⊥)
open import CaTTExp.Strict.Tables
open import CaTTExp.Strict.Nu
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms
open import CaTTExp.Strict.Generation
open import CaTTExp.Strict.CMonSolver
open import CaTTExp.Strict.Bag using (+-comm; +-assoc; +-zero; +-suc)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Splitting a vector at an index.

lowV : ∀ {m} → Nat → Vec Nat m → Vec Nat m
lowV t       []      = []
lowV zero    (a ∷ w) = 0 ∷ lowV zero w
lowV (suc t) (a ∷ w) = a ∷ lowV t w

lowV-lt : ∀ {m} t (w : Vec Nat m) d → d < t → at0 (lowV t w) d ≡ at0 w d
lowV-lt (suc t) []      d       _       = refl
lowV-lt (suc t) (a ∷ w) zero    _       = refl
lowV-lt (suc t) (a ∷ w) (suc d) (s≤s l) = lowV-lt t w d l

lowV-ge : ∀ {m} t (w : Vec Nat m) d → t ≤ d → at0 (lowV t w) d ≡ 0
lowV-ge t       []      d       _       = refl
lowV-ge zero    (a ∷ w) zero    _       = refl
lowV-ge zero    (a ∷ w) (suc d) _       = lowV-ge zero w d z≤n
lowV-ge (suc t) (a ∷ w) (suc d) (s≤s l) = lowV-ge t w d l

module Cut {N : Nat} (B : Basis N) (H : Hyp B) (L : Nat) where
  open Basis B
  open Hyp H
  open Atom B
  open Gen B H L
  open Cells dd using (module Deg)
  open Deg deg-dp deg-dm using (∸c-deg; ent-ok)

  private
    𝕄′ = ADC.𝕄 K
    dp = dP B
    dm = dM B

  ----------------------------------------------------------------------
  -- Vectors.

  private
    Lo-+ : ∀ {t} (u v : Vec Nat N) → Lo t u → Lo t v → Lo t (u +c v)
    Lo-+ u v hu hv d p = trans (at-+c u v d) (cong₂ _+_ (hu d p) (hv d p))

    Hi-+ : ∀ {t} (u v : Vec Nat N) → Hi t u → Hi t v → Hi t (u +c v)
    Hi-+ u v hu hv d p = trans (at-+c u v d) (cong₂ _+_ (hu d p) (hv d p))

    Lo-mono : ∀ {t t′} (u : Vec Nat N) → t ≤ t′ → Lo t u → Lo t′ u
    Lo-mono u l h d p = h d (≤-trans l p)

  -- w = w₁ + w₂ with w₁ below t and w₂ from t on, both of w's degree.
  module Parts (t : Nat) (w : Vec Nat N) where
    w₂ w₁ : Vec Nat N
    w₂ = w ∸c lowV t w
    w₁ = w ∸c w₂

    at-w₂ : ∀ d → at0 w₂ d ≡ (at0 w d ∸ at0 (lowV t w) d)
    at-w₂ d = at-∸c w (lowV t w) d

    w₁-Lo : Lo t w₁
    w₁-Lo d p = trans (at-∸c w w₂ d)
      (trans (cong (at0 w d ∸_) (trans (at-w₂ d) (cong (at0 w d ∸_) (lowV-ge t w d p)))) (n∸n (at0 w d)))
      where
      n∸n : ∀ n → n ∸ (n ∸ 0) ≡ 0
      n∸n zero    = refl
      n∸n (suc n) = n∸n n

    w₂-Hi : Hi t w₂
    w₂-Hi d p = trans (at-w₂ d) (trans (cong (at0 w d ∸_) (lowV-lt t w d p)) (n∸n (at0 w d)))
      where
      n∸n : ∀ n → n ∸ n ≡ 0
      n∸n zero    = refl
      n∸n (suc n) = n∸n n

    sum : w₁ +c w₂ ≡ w
    sum = vext _ _ pt
      where
      pt : ∀ d → at0 (w₁ +c w₂) d ≡ at0 w d
      pt d with ≤-dec t d
      ... | inj₁ p = trans (at-+c w₁ w₂ d) (trans (cong₂ _+_ (w₁-Lo d p) (trans (at-w₂ d) (cong (at0 w d ∸_) (lowV-ge t w d p)))) (∸0 (at0 w d)))
        where
        ∸0 : ∀ n → 0 + (n ∸ 0) ≡ n
        ∸0 n = refl
      ... | inj₂ p = trans (at-+c w₁ w₂ d)
                       (trans (cong (at0 w₁ d +_) (w₂-Hi d p))
                         (trans (+-zero (at0 w₁ d))
                           (trans (at-∸c w w₂ d) (trans (cong (at0 w d ∸_) (w₂-Hi d p)) (n∸0 (at0 w d))))))
        where
        n∸0 : ∀ n → n ∸ 0 ≡ n
        n∸0 zero    = refl
        n∸0 (suc n) = refl

    deg₂ : ∀ j → InD j w → InD j w₂
    deg₂ j h = ∸c-deg j gdeg w (lowV t w) h

    deg₁ : ∀ j → InD j w → InD j w₁
    deg₁ j h = ∸c-deg j gdeg w w₂ h

  ----------------------------------------------------------------------
  -- Tables at the boundary row.

  private
    at-src-top : ∀ {m} n (x : Tab 𝕄′ m) → n < m → at 0R (srcT 𝕄′ n x) n ≡ (fst (at 0R x n) , fst (at 0R x n))
    at-src-top zero    ((a , b) ∷ r) _       = refl
    at-src-top (suc n) (e ∷ r)       (s≤s l) = at-src-top n r l

    at-tgt-top : ∀ {m} n (x : Tab 𝕄′ m) → n < m → at 0R (tgtT 𝕄′ n x) n ≡ (snd (at 0R x n) , snd (at 0R x n))
    at-tgt-top zero    ((a , b) ∷ r) _       = refl
    at-tgt-top (suc n) (e ∷ r)       (s≤s l) = at-tgt-top n r l

    at-comp-top : ∀ {m} n (x y : Tab 𝕄′ m) → n < m → at 0R (compT 𝕄′ n x y) n ≡ (fst (at 0R x n) , snd (at 0R y n))
    at-comp-top zero    ((a , b) ∷ r) ((c , d) ∷ s) _       = refl
    at-comp-top (suc n) (e ∷ r)       (e′ ∷ s)      (s≤s l) = at-comp-top n r s l

    at-comp-hi : ∀ {m} n (x y : Tab 𝕄′ m) j → n < j → at 0R (compT 𝕄′ n x y) j ≡ at 0R x j +R at 0R y j
    at-comp-hi n       []            []            j       l       = sym (+R-idr 0R)
    at-comp-hi zero    ((a , b) ∷ r) ((c , d) ∷ s) (suc j) l       = at-add r s j
      where
      at-add : ∀ {m} (x y : Tab 𝕄′ m) j → at 0R (add 𝕄′ x y) j ≡ at 0R x j +R at 0R y j
      at-add []      []       j       = sym (+R-idr 0R)
      at-add (e ∷ r) (e′ ∷ r′) zero    = refl
      at-add (e ∷ r) (e′ ∷ r′) (suc j) = at-add r r′ j
    at-comp-hi (suc n) (e ∷ r)       (e′ ∷ s)      (suc j) (s≤s l) = at-comp-hi n r s j l

    hd≡′ : ∀ {m} {e e′ : Row} {r r′ : Vec Row m} → _≡_ {A = Vec Row (suc m)} (e ∷ r) (e′ ∷ r′) → e ≡ e′
    hd≡′ refl = refl

    -- Rows of a cell, as Ent conditions.
    entC : ∀ (x : Tb) → IsCell K L x → ∀ j → j < L → Ent K L (suc j) (at 0R x j) (at 0R x (suc j))
    entC x cx = fst (snd (IsCell→CellF x cx))

  ----------------------------------------------------------------------
  -- Row r of a cell agreeing with ⟨a⟩ above r: ⟨a⟩ᵣ + (w, w).

  row-excess : ∀ r a → r < deg a → deg a ≤ L → (x : Tb) → IsCell K L x → Agree r (at 0R x) (ent a) →
               let u = fst (at 0R x r) ; v = snd (at 0R x r) ; u0 = fst (ent a r) ; v0 = snd (ent a r) in
               (u ≡ u0 +c (u ∸c u0)) × (v ≡ v0 +c (u ∸c u0))
  row-excess r a ra aL x cx ag =
    excess u v u0 v0 (same-bd u v u0 v0 e E1 E2) (disj-LH a u0 v0 (fst (ent-sides a r ra)) (snd (ent-sides a r ra)))
    where
    u = fst (at 0R x r)
    v = snd (at 0R x r)
    u0 = fst (ent a r)
    v0 = snd (ent a r)
    e = fst (ent a (suc r))
    rL : r < L
    rL = ≤-trans ra aL
    E1 : dp e +c u ≡ dm e +c v
    E1 = let (_ , _ , b , _) = subst (λ q → Ent K L (suc r) (at 0R x r) q) (ag (suc r) (≤-refl _) rL) (entC x cx r rL) in b
    E2 : dp e +c u0 ≡ dm e +c v0
    E2 = let (_ , _ , b , _) = ent-ok a r in b

  ----------------------------------------------------------------------
  -- Row r of y #ᵣ y′.

  record CompRow (r : Nat) (b c : Nat) (y y′ : Tb) : Set where
    field
      w     : Vec Nat N
      w-deg : InD r w
      row⁻  : fst (at 0R (compT 𝕄′ r y y′) r) ≡ fst (ent b r) +c (fst (ent c r) +c w)
      row⁺  : snd (at 0R (compT 𝕄′ r y y′) r) ≡ snd (ent c r) +c (snd (ent b r) +c w)

  comp-row : ∀ r b c → c < b → r < deg b → r < deg c → deg b ≤ L → deg c ≤ L →
             ∀ (y y′ : Tb) → IsCell K L y → IsCell K L y′ → tgtT 𝕄′ r y ≡ srcT 𝕄′ r y′ →
             Agree r (at 0R y) (ent b) → Agree r (at 0R y′) (ent c) → CompRow r b c y y′
  comp-row r b c cb rb rc bL cL y y′ cy cy′ m agy agy′ = record
    { w = w ; w-deg = dw
    ; row⁻ = trans (cong fst (at-comp-top r y y′ rL1))
               (trans (fst ey) (cong (A⁻ +c_) (snd ex)))
    ; row⁺ = trans (cong snd (at-comp-top r y y′ rL1))
               (trans (snd ez) (cong (B⁺ +c_) (fst ex)))
    }
    where
    rL1 : r < suc L
    rL1 = ≤-suc (≤-trans rb bL)
    A⁻ = fst (ent b r)
    A⁺ = snd (ent b r)
    B⁻ = fst (ent c r)
    B⁺ = snd (ent c r)
    Y⁻ = fst (at 0R y r)
    Y⁺ = snd (at 0R y r)
    Z⁻ = fst (at 0R y′ r)
    Z⁺ = snd (at 0R y′ r)
    ey = row-excess r b rb bL y cy agy
    ez = row-excess r c rc cL y′ cy′ agy′
    wy = Y⁻ ∸c A⁻
    wz = Z⁻ ∸c B⁻
    mt : Y⁺ ≡ Z⁻
    mt = cong fst (trans (sym (at-tgt-top r y rL1)) (trans (cong (λ t → at 0R t r) m) (at-src-top r y′ rL1)))
    eqn : wz +c B⁻ ≡ wy +c A⁺
    eqn = trans (+c-comm wz B⁻) (trans (sym (fst ez)) (trans (sym mt) (trans (snd ey) (+c-comm A⁺ wy))))
    dj : ∀ d → (at0 A⁺ d ≡ 0) ⊎ (at0 B⁻ d ≡ 0)
    dj d with ≤-dec c d
    ... | inj₁ p = inj₂ (fst (ent-sides c r rc) d p)
    ... | inj₂ p = inj₁ (snd (ent-sides b r rb) d (≤-trans p (≤-suc (<→≤ cb))))
    ex = excess wz wy A⁺ B⁻ eqn dj
    w = wz ∸c A⁺
    dZ : InD r Z⁻
    dZ = deg-row r y′ cy′ (<→≤ (≤-trans rc cL))
      where
      deg-row : ∀ r (x : Tb) → IsCell K L x → r ≤ L → InD r (fst (at 0R x r))
      deg-row zero    (e ∷ x) (e0 , _) _ = fst e0
      deg-row (suc r) x       cx       l = let (d , _ , _ , _) = entC x cx r l in d
    dw : InD r w
    dw = ∸c-deg r gdeg wz A⁺ (∸c-deg r gdeg Z⁻ B⁻ dZ)

  ----------------------------------------------------------------------
  -- At r = 0 no such composite exists: its 0-source would have
  -- augmentation at least 2.

  no-cut-0 : ∀ b c → c < b → b < N → c < N → 0 < deg b → 0 < deg c → deg b ≤ L → deg c ≤ L →
             ∀ (y y′ : Tb) → IsCell K L y → IsCell K L y′ → tgtT 𝕄′ 0 y ≡ srcT 𝕄′ 0 y′ →
             Agree 0 (at 0R y) (ent b) → Agree 0 (at 0R y′) (ent c) → ⊥
  no-cut-0 b c cb bN cN rb rc bL cL y y′ cy cy′ m agy agy′ = two≠one
    where
    x2 = compT 𝕄′ 0 y y′
    CR = comp-row 0 b c cb rb rc bL cL y y′ cy cy′ m agy agy′
    w = CompRow.w CR
    aug-x : augm gdeg (fst (at 0R x2 0)) ≡ 1
    aug-x = aug0 x2 (cell-comp K L 0 y y′ m cy cy′)
      where
      aug0 : ∀ (x : Tb) → IsCell K L x → augm gdeg (fst (at 0R x 0)) ≡ 1
      aug0 (e ∷ x) ((_ , _ , a , _) , _) = a
    two≠one : ⊥
    two≠one = absurd (trans (sym aug-x) (trans (cong (augm gdeg) (CompRow.row⁻ CR))
                (trans (augm-+ gdeg (fst (ent b 0)) (fst (ent c 0) +c w))
                  (cong₂ _+_ (fst (unital b bN)) (augm-+ gdeg (fst (ent c 0)) w)))))
      where
      absurd : ∀ {k} → 1 ≡ 1 + (augm gdeg (fst (ent c 0)) + k) → ⊥
      absurd {k} e rewrite fst (unital c cN) = s≢0 (suc-inj′ e)
        where
        suc-inj′ : ∀ {m n} → suc m ≡ suc n → m ≡ n
        suc-inj′ refl = refl
        s≢0 : ∀ {n} → 0 ≡ suc n → ⊥
        s≢0 ()

  ----------------------------------------------------------------------
  -- The lower cut, r = s + 1.

  record LC (s : Nat) (b c : Nat) (x2 : Tb) : Set where
    field
      v u   : RF
      cv    : CellF v
      cu    : CellF u
      v-ag  : Agree (suc s) v (ent c)
      u-ag  : Agree (suc s) u (ent b)
      match : tgtT 𝕄′ s (tabG {m = suc L} v 0) ≡ srcT 𝕄′ s (tabG u 0)
      comp  : compT 𝕄′ s (tabG {m = suc L} v 0) (tabG u 0) ≡ x2

  open Solver 𝕄′ using (solve; lk; `_; _⊞_)

  lower-cut : ∀ s b c → c < b → suc s < deg b → suc s < deg c → deg b ≤ L → deg c ≤ L →
              ∀ (y y′ : Tb) → IsCell K L y → IsCell K L y′ → tgtT 𝕄′ (suc s) y ≡ srcT 𝕄′ (suc s) y′ →
              Agree (suc s) (at 0R y) (ent b) → Agree (suc s) (at 0R y′) (ent c) →
              LC s b c (compT 𝕄′ (suc s) y y′)
  lower-cut s b c cb rb rc bL cL y y′ cy cy′ m agy agy′ = record
    { v = Split.y S ; u = Split.z S ; cv = Split.cy S ; cu = Split.cz S
    ; v-ag = λ j h jL → trans (Split.yp S j (≤-trans (≤-suc (≤-refl _)) h))
                          (trans (cong (ent c j +R_) (W-above s w₁ j h)) (+R-idr (ent c j)))
    ; u-ag = λ j h jL → trans (Split.zq S j (≤-trans (≤-suc (≤-refl _)) h))
                          (trans (cong (ent b j +R_) (W-above s w₂ j h)) (+R-idr (ent b j)))
    ; match = Split.match S
    ; comp = trans (Split.comp S) (sym (tab-at 0R x2))
    }
    where
    r = suc s
    x2 = compT 𝕄′ r y y′
    f = at 0R x2
    CR = comp-row r b c cb rb rc bL cL y y′ cy cy′ m agy agy′
    w = CompRow.w CR
    open Parts b w
    dw₁ = deg₁ r (CompRow.w-deg CR)
    dw₂ = deg₂ r (CompRow.w-deg CR)
    p q : RF
    p j = ent c j +R W s w₁ j
    q j = ent b j +R W s w₂ j
    sL : s < L
    sL = ≤-trans (<→≤ rb) bL
    cf : CellF f
    cf = IsCell→CellF x2 (cell-comp K L r y y′ m cy cy′)
    A⁻ = fst (ent b r)
    A⁺ = snd (ent b r)
    B⁻ = fst (ent c r)
    B⁺ = snd (ent c r)
    pr : p r ≡ (B⁻ +c w₁ , B⁺ +c w₁)
    pr = cong (ent c r +R_) (W-top s w₁)
    qr : q r ≡ (A⁻ +c w₂ , A⁺ +c w₂)
    qr = cong (ent b r +R_) (W-top s w₂)
    sp : ∀ j → s < j → j ≤ L → f j ≡ p j +R q j
    sp j h jL with view3 j r
    ... | vlt h′ = ⊥-elim (≤-<-⊥ h h′)
    ... | veq refl =
      trans (cong₂ _,_ (CompRow.row⁻ CR) (CompRow.row⁺ CR))
        (trans (cong₂ _,_ (trans (cong (λ t → A⁻ +c (B⁻ +c t)) (sym sum))
                                  (solve (` 0 ⊞ (` 1 ⊞ (` 2 ⊞ ` 3))) ((` 1 ⊞ ` 2) ⊞ (` 0 ⊞ ` 3)) (lk (A⁻ ∷ B⁻ ∷ w₁ ∷ w₂ ∷ [])) tt))
                           (trans (cong (λ t → B⁺ +c (A⁺ +c t)) (sym sum))
                                  (solve (` 0 ⊞ (` 1 ⊞ (` 2 ⊞ ` 3))) ((` 0 ⊞ ` 2) ⊞ (` 1 ⊞ ` 3)) (lk (B⁺ ∷ A⁺ ∷ w₁ ∷ w₂ ∷ [])) tt)))
               (sym (cong₂ _+R_ pr qr)))
    ... | vgt h′ =
      trans (at-comp-hi r y y′ j h′)
        (trans (cong₂ _+R_ (agy j h′ jL) (agy′ j h′ jL))
          (trans (+R-comm′ (ent b j) (ent c j))
            (sym (cong₂ _+R_ (trans (cong (ent c j +R_) (W-above s w₁ j h′)) (+R-idr (ent c j)))
                             (trans (cong (ent b j +R_) (W-above s w₂ j h′)) (+R-idr (ent b j)))))))
      where
      +R-comm′ : ∀ (a b : Row) → a +R b ≡ b +R a
      +R-comm′ (a , a′) (b , b′) = cong₂ _,_ (+c-comm a b) (+c-comm a′ b′)
    gp : Good s p
    gp = Good-add s (ent c) (W s w₁) (Good-ent c s (<→≤ rc) cL) (Good-W s w₁ dw₁)
    gq : Good s q
    gq = Good-add s (ent b) (W s w₂) (Good-ent b s (<→≤ rb) bL) (Good-W s w₂ dw₂)
    loP : Lo b (B⁻ +c w₁)
    loP = Lo-+ B⁻ w₁ (Lo-mono B⁻ (<→≤ cb) (fst (ent-sides c r rc))) w₁-Lo
    hiQ : Hi b (A⁺ +c w₂)
    hiQ = Hi-+ A⁺ w₂ (Hi-weak {N} {b} {A⁺} (snd (ent-sides b r rb))) w₂-Hi
    Lo-dm : ∀ t → c < t → (u : Vec Nat N) → Lo t u → Lo t (dm u ∸c dp u)
    Lo-dm (suc t) _ u h = ∸c-Lo (dm u) (dp u) (Lo-weak {N} {t} {dm u} (dm-Lo t u h))
    lo : Lo b (dm (fst (p r)) ∸c dp (fst (p r)))
    lo = subst (λ t → Lo b (dm t ∸c dp t)) (sym (cong fst pr)) (Lo-dm b cb (B⁻ +c w₁) loP)
    hi : Hi (suc b) (dp (snd (q r)) ∸c dm (snd (q r)))
    hi = subst (λ t → Hi (suc b) (dp t ∸c dm t)) (sym (cong snd qr))
           (∸c-Hi (dp (A⁺ +c w₂)) (dm (A⁺ +c w₂)) (dp-Hi b (A⁺ +c w₂) hiQ))
    dj : Disj s p q
    dj d with ≤-dec b d
    ... | inj₁ h = inj₁ (lo d h)
    ... | inj₂ h = inj₂ (hi d (≤-suc h))
    S : Split s f p q
    S = peel s sL f p q cf gp gq sp dj
