------------------------------------------------------------------------
-- Unique lifting for ν(K) (ledger A5, steps L5 and L6; outside
-- response §4 and §5).
--
-- Fix a target ω-category 𝒟 with values κ g for the atoms, and
-- attaching words W^± g that compute the boundaries of each atom in
-- both ν(K) and 𝒟 (hypothesis (19)). Two composition-only
-- expressions with the same value in ν(K) have the same value in 𝒟.
--
-- The proof is an induction on r: Lf r says this for every cell that
-- agrees above r with an atom or with zero. In the step, both
-- expressions are standardised. Either one of them shows that the
-- cell already agrees above r with a single atom (so Lf r applies), or
-- both are chains of at least two factors at cut r, each factor
-- agreeing above r with one atom. Chains are compared by moving the
-- factor with the least label to the front (the swap lemma, through
-- the lower cut) and splitting off that factor (`Lifting.factors`).
------------------------------------------------------------------------
module CaTTExp.Strict.Lift where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Tables
open import CaTTExp.Strict.Nu
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms
open import CaTTExp.Strict.Generation
open import CaTTExp.Strict.Expr
open import CaTTExp.Strict.BdElim
open import CaTTExp.Strict.NuWords
open import CaTTExp.Strict.NuRows
open import CaTTExp.Strict.Lifting
open import CaTTExp.Strict.LowerCut
open import CaTTExp.Strict.AtomSum
import CaTTExp.Strict.Std as S
open import CaTTExp.Strict.StdSem using (module StdSem)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)
open import CaTTExp.Strict.Bag using (+-zero)

------------------------------------------------------------------------
-- Re-bracketing around a replaced pair: a #ᵣ (b #ᵣ c) becomes
-- a′ #ᵣ (b′ #ᵣ c) when a #ᵣ b = a′ #ᵣ b′.

module Rot (𝒞 : ωCat) where
  open ωCat 𝒞
  open Basics 𝒞 using (comp-cong)

  pab : ∀ r a b c (p₁ : tgt r b ≡ src r c) → tgt r a ≡ src r (comp r b c p₁) → tgt r a ≡ src r b
  pab r a b c p₁ p = trans p (src-comp r b c p₁)

  rot : ∀ r a b c (p₁ : tgt r b ≡ src r c) (p : tgt r a ≡ src r (comp r b c p₁)) a′ b′ (pab′ : tgt r a′ ≡ src r b′) →
        comp r a b (pab r a b c p₁ p) ≡ comp r a′ b′ pab′ →
        Σ (tgt r b′ ≡ src r c) λ p₃ → Σ (tgt r a′ ≡ src r (comp r b′ c p₃)) λ p₄ →
        comp r a (comp r b c p₁) p ≡ comp r a′ (comp r b′ c p₃) p₄
  rot r a b c p₁ p a′ b′ pab′ E = p₃ , p₄ ,
    trans (sym (assoc r a b c q pabc p₁ p)) (trans (comp-cong r pabc pabc′ E refl) (assoc r a′ b′ c pab′ pabc′ p₃ p₄))
    where
    q = pab r a b c p₁ p
    pabc : tgt r (comp r a b q) ≡ src r c
    pabc = trans (tgt-comp r a b q) p₁
    pabc′ : tgt r (comp r a′ b′ pab′) ≡ src r c
    pabc′ = trans (cong (tgt r) (sym E)) pabc
    p₃ : tgt r b′ ≡ src r c
    p₃ = trans (sym (tgt-comp r a′ b′ pab′)) pabc′
    p₄ : tgt r a′ ≡ src r (comp r b′ c p₃)
    p₄ = trans pab′ (sym (src-comp r b′ c p₃))

module Lift {N : Nat} (B : Basis N) (H : Hyp B) (L : Nat)
            (𝒟 : ωCat) (κ : AtomG B H L → ωCat.C 𝒟)
            (W : Sd → AtomG B H L → Expr (AtomG B H L)) where
  open Basis B
  open Hyp H
  open Atom B
  open Gen B H L hiding (W)
  open Rows B H L
  open TabAt (ADC.𝕄 K)
  open Sum B H L
  open Det K L using (Above; factors)
  open Cut B H L using (LC; lower-cut; no-cut-0)

  G : Set
  G = AtomG B H L

  degG : G → Nat
  degG (i , _ , _) = deg i

  open Syn degG W

  private
    module ν = ωCat (nu K L)
    module 𝔇 = ωCat 𝒟
    module Eν = Eval (nu K L) (ιν B H L)
    module ED = Eval 𝒟 κ
    module Sν = Sem (nu K L) (ιν B H L)
    module SD = Sem 𝒟 κ

  ----------------------------------------------------------------------
  -- Values in both categories.

  Rel : ν.C → 𝔇.C → Set
  Rel x y = Σ (Expr G) (λ e → CO e × Eν.Ev e x × ED.Ev e y)

  UnFor : ν.C → Set
  UnFor x = ∀ {y y′} → Rel x y → Rel x y′ → y ≡ y′

  -- Lf r: unique lifting for cells agreeing above r with an atom or zero.
  Lf : Nat → Set
  Lf r = ∀ x A → AOKL A → Agree r (rows x) (Arow A) → UnFor x

  rel-comp : ∀ n {x x′ y y′} → Rel x y → Rel x′ y′ → (p : ν.tgt n x ≡ ν.src n x′) (q : 𝔇.tgt n y ≡ 𝔇.src n y′) →
             Rel (ν.comp n x x′ p) (𝔇.comp n y y′ q)
  rel-comp n (e , c , u , v) (e′ , c′ , u′ , v′) p q = cmp n e e′ , co-cmp n c c′ , Eν.ev-cmp n u u′ p , ED.ev-cmp n v v′ q

  rel-sub : ∀ {x x′ y y′} → x ≡ x′ → y ≡ y′ → Rel x y → Rel x′ y′
  rel-sub refl refl r = r

  ----------------------------------------------------------------------
  -- Every composition-only expression has degrees ≤ L.

  co-deg : ∀ {e} → CO e → DegLe L e
  co-deg (co-gen (i , _ , iL)) = dl-gen iL
  co-deg (co-cmp n a b)        = dl-cmp (co-deg a) (co-deg b)

  dimν : ∀ g → ν.src (degG g) (ιν B H L g) ≡ ιν B H L g
  dimν (i , iN , iL) = dim-atom i iN iL

  rows-tgt : ∀ n x j → n < j → rows (ν.tgt n x) j ≡ 0R
  rows-tgt n (x , _) j l = at-tgt n x j l

  ----------------------------------------------------------------------
  -- Hypothesis (19), and boundaries of related values.

  module Hyps (W-co : ∀ s g → CO (W s g))
              (W-deg : ∀ s g → DegLe (degG g ∸ 1) (W s g))
              (W-evν : ∀ s g → 1 ≤ degG g → Eν.Ev (W s g) (Sν.bdC s (degG g ∸ 1) (ιν B H L g)))
              (dimκ : ∀ g → 𝔇.src (degG g) (κ g) ≡ κ g)
              (W-evD : ∀ s g → 1 ≤ degG g → ED.Ev (W s g) (SD.bdC s (degG g ∸ 1) (κ g))) where

    open Props W-co W-deg

    rel-bd : ∀ s n {x y} → Rel x y → Rel (Sν.bdC s n x) (SD.bdC s n y)
    rel-bd s n (e , c , u , v) =
      bd s L n e , bd-co s L n e c ,
      Sν.sound W-deg dimν W-evν s L n e (co-deg c) u ,
      SD.sound W-deg dimκ W-evD s L n e (co-deg c) v

    -- Cells of dimension ≤ r agree above r with zero.
    low : ∀ r → Lf r → ∀ n x → n ≤ r → ∀ s → UnFor (Sν.bdC s n x)
    low r Pr n x nr σ⁻ = Pr (ν.src n x) nothing tt (λ j rj _ → rows-src n x j (≤-trans (s≤s nr) rj))
    low r Pr n x nr σ⁺ = Pr (ν.tgt n x) nothing tt (λ j rj _ → rows-tgt n x j (≤-trans (s≤s nr) rj))

    -- Composability in 𝒟 follows from composability in ν(K).
    match𝔇 : ∀ r → Lf r → ∀ n → n ≤ r → ∀ {x x′ y y′} → Rel x y → Rel x′ y′ → ν.tgt n x ≡ ν.src n x′ → 𝔇.tgt n y ≡ 𝔇.src n y′
    match𝔇 r Pr n nr {x} R R′ p = low r Pr n x nr σ⁺ (rel-bd σ⁺ n R) (rel-sub (sym p) refl (rel-bd σ⁻ n R′))

    -- Existence for generation trees with levels ≤ r.
    exL : ∀ r → Lf r → ∀ {x} → GenL (suc r) x → (cx : IsCell K L x) → Σ 𝔇.C (Rel (x , cx))
    exL r Pr (gl-atom i iN iL) cx =
      κ (i , iN , iL) , rel-sub (≡-cell K L refl) refl (gen (i , iN , iL) , co-gen _ , Eν.ev-gen _ , ED.ev-gen _)
    exL r Pr (gl-comp n (s≤s nr) gy gz m) cx =
      let (y₁ , R₁) = exL r Pr gy (gen-cell (forget gy))
          (y₂ , R₂) = exL r Pr gz (gen-cell (forget gz))
          p = ≡-cell K L m
      in 𝔇.comp n y₁ y₂ (match𝔇 r Pr n nr R₁ R₂ p) ,
         rel-sub (≡-cell K L refl) refl (rel-comp n R₁ R₂ p (match𝔇 r Pr n nr R₁ R₂ p))

    ------------------------------------------------------------------
    -- Chains at cut r: r-composites of related pairs, each agreeing
    -- above r with one atom (its label). The count vector records the
    -- labels with multiplicity.

    Lab : Nat → ν.C → Nat → Set
    Lab r x g = (r < deg g) × (deg g ≤ L) × (g < N) × Agree r (rows x) (ent g)

    data Ch (r : Nat) : ν.C → 𝔇.C → Vec Nat N → Set where
      ch1 : ∀ {x y g} → Rel x y → Lab r x g → Ch r x y (unit g)
      ch∷ : ∀ {x y x′ y′ g c} → Rel x y → Lab r x g → Ch r x′ y′ c →
            (p : ν.tgt r x ≡ ν.src r x′) (q : 𝔇.tgt r y ≡ 𝔇.src r y′) →
            Ch r (ν.comp r x x′ p) (𝔇.comp r y y′ q) (unit g +c c)

    ch-rel : ∀ {r x y c} → Ch r x y c → Rel x y
    ch-rel (ch1 R _)          = R
    ch-rel (ch∷ R _ ch p q)   = rel-comp _ R (ch-rel ch) p q

    -- Rows above r of a chain: Σ cᵢ⟨i⟩.
    RS : Vec Nat N → RF
    RS c j = esum fst c 0 j , esum snd c 0 j

    RS-unit : ∀ g j → g < N → RS (unit g) j ≡ ent g j
    RS-unit g j gN = cong₂ _,_ (trans (esum-unit fst g 0 j gN) (cong (λ t → fst (ent t j)) (+-zero g)))
                               (trans (esum-unit snd g 0 j gN) (cong (λ t → snd (ent t j)) (+-zero g)))

    RS-+ : ∀ c c′ j → RS (c +c c′) j ≡ RS c j +R RS c′ j
    RS-+ c c′ j = cong₂ _,_ (esum-+ fst c c′ 0 j) (esum-+ snd c c′ 0 j)

    rowsCh : ∀ {r x y c} → Ch r x y c → Agree r (rows x) (RS c)
    rowsCh (ch1 {g = g} _ (_ , _ , gN , ag)) j rj jL = trans (ag j rj jL) (sym (RS-unit g j gN))
    rowsCh {r} (ch∷ {x = x} {x′ = x′} {g = g} {c = c} _ (_ , _ , gN , ag) ch p q) j rj jL =
      trans (rows-comp r x x′ p j rj)
        (trans (cong₂ _+R_ (trans (ag j rj jL) (sym (RS-unit g j gN))) (rowsCh ch j rj jL))
          (sym (RS-+ (unit g) c j)))

    ------------------------------------------------------------------
    -- Tables.

    private
      at-tabG′ : ∀ {m} (f : RF) k j → j < m → at 0R (tabG {m = m} f k) j ≡ f (j + k)
      at-tabG′ {suc m} f k zero    _       = refl
      at-tabG′ {suc m} f k (suc j) (s≤s l) = trans (at-tabG′ {m} f (suc k) j l) (cong f (+-suc′ j k))
        where
        +-suc′ : ∀ j k → j + suc k ≡ suc (j + k)
        +-suc′ zero    k = refl
        +-suc′ (suc j) k = cong suc (+-suc′ j k)

      tab-ext : ∀ {m} (x y : Tab (ADC.𝕄 K) m) → (∀ j → j < m → at 0R x j ≡ at 0R y j) → x ≡ y
      tab-ext []      []      h = refl
      tab-ext (e ∷ x) (e′ ∷ y) h = cong₂ _∷_ (h 0 (s≤s z≤n)) (tab-ext x y (λ j l → h (suc j) (s≤s l)))

      above-of : ∀ {m} n (x y : Tab (ADC.𝕄 K) m) → (∀ j → n < j → j < m → at 0R x j ≡ at 0R y j) → Above n x y
      above-of n       []      []       h = tt
      above-of zero    (e ∷ x) (e′ ∷ y) h = tab-ext x y (λ j l → h (suc j) (s≤s z≤n) (s≤s l))
      above-of (suc n) (e ∷ x) (e′ ∷ y) h = above-of n x y (λ j l l′ → h (suc j) (s≤s l) (s≤s l′))

    rows-tabG : ∀ f cf j → j ≤ L → rows (tabG {m = suc L} f 0 , cf) j ≡ f j
    rows-tabG f cf j jL = trans (at-tabG′ {suc L} f 0 j (s≤s jL)) (cong f (+-zero j))

    above : ∀ r (x y : ν.C) → Agree r (rows x) (rows y) → Above r (fst x) (fst y)
    above r x y h = above-of r (fst x) (fst y) (λ j l jL → h j l (≤-pred′ jL))
      where
      ≤-pred′ : ∀ {a b} → suc a ≤ suc b → a ≤ b
      ≤-pred′ (s≤s q) = q

    ------------------------------------------------------------------
    -- The swap lemma (§4): an adjacent pair with labels b > c can be
    -- exchanged, in both categories at once.

    record Sw (r : Nat) (X : ν.C) (Y : 𝔇.C) (b c : Nat) : Set where
      field
        x₁ x₂ : ν.C
        y₁ y₂ : 𝔇.C
        R₁ : Rel x₁ y₁
        R₂ : Rel x₂ y₂
        l₁ : Lab r x₁ c
        l₂ : Lab r x₂ b
        p  : ν.tgt r x₁ ≡ ν.src r x₂
        q  : 𝔇.tgt r y₁ ≡ 𝔇.src r y₂
        eν : X ≡ ν.comp r x₁ x₂ p
        eD : Y ≡ 𝔇.comp r y₁ y₂ q

    private
      module SSν = StdSem (nu K L) (ιν B H L)
      module SSD = StdSem 𝒟 κ
      module BD = Basics 𝒟

    swap : ∀ r → Lf r → ∀ {x₁ x₂ y₁ y₂ b c} → Rel x₁ y₁ → Lab r x₁ b → Rel x₂ y₂ → Lab r x₂ c → c < b →
           (p : ν.tgt r x₁ ≡ ν.src r x₂) (q : 𝔇.tgt r y₁ ≡ 𝔇.src r y₂) →
           Sw r (ν.comp r x₁ x₂ p) (𝔇.comp r y₁ y₂ q) b c
    swap zero Pr {x₁} {x₂} {b = b} {c} R₁ (rb , bL , bN , ag₁) R₂ (rc , cL , cN , ag₂) cb p q =
      ⊥-elim (no-cut-0 b c cb bN cN rb rc bL cL (fst x₁) (fst x₂) (snd x₁) (snd x₂) (cong fst p) ag₁ ag₂)
    swap (suc s) Pr {x₁} {x₂} {y₁} {y₂} {b} {c} R₁ (rb , bL , bN , ag₁) R₂ (rc , cL , cN , ag₂) cb p q = record
      { x₁ = ν.comp s Vc (ν.src r Uc) p₁ν ; x₂ = ν.comp s (ν.tgt r Vc) Uc p₂ν
      ; y₁ = 𝔇.comp s yv (𝔇.src r yu) p₁D ; y₂ = 𝔇.comp s (𝔇.tgt r yv) yu p₂D
      ; R₁ = rel-comp s RV (rel-bd σ⁻ r RU) p₁ν p₁D
      ; R₂ = rel-comp s (rel-bd σ⁺ r RV) RU p₂ν p₂D
      ; l₁ = rc , cL , cN , λ j rj jL →
               trans (rows-comp s Vc (ν.src r Uc) p₁ν j (<→≤ rj))
                 (trans (cong₂ _+R_ (trans (rows-tabG v (snd Vc) j jL) (v-ag j rj jL)) (rows-src r Uc j rj)) (+R-idr (ent c j)))
      ; l₂ = rb , bL , bN , λ j rj jL →
               trans (rows-comp s (ν.tgt r Vc) Uc p₂ν j (<→≤ rj))
                 (trans (cong₂ _+R_ (rows-tgt r Vc j rj) (trans (rows-tabG u (snd Uc) j jL) (u-ag j rj jL))) (+R-idl (ent b j)))
      ; p = qν ; q = qD′
      ; eν = trans (sym eX) eqν
      ; eD = trans (BD.comp-cong r q q′D (Pr x₁ (just b) (bN , bL) ag₁ R₁ (rel-sub (sym e₁) refl RA₁))
                                         (Pr x₂ (just c) (cN , cL) ag₂ R₂ (rel-sub (sym e₂) refl RA₂)))
                   (trans (sym eq′D) eqD)
      }
      where
      r = suc s
      open LC (lower-cut s b c cb rb rc bL cL (fst x₁) (fst x₂) (snd x₁) (snd x₂) (cong fst p) ag₁ ag₂)
        renaming (comp to vu-eq; match to vu-m)
      sL : suc s ≤ L
      sL = <→≤ (≤-trans rb bL)
      up : ∀ {x} → GenL (suc s) x → GenL (suc (suc s)) x
      up = GenL-up (≤-suc (≤-refl _))
      gv : GenL (suc s) (tabG v 0)
      gv = gen-at (suc s) sL v cv (just c) (cN , cL) v-ag
      gu : GenL (suc s) (tabG u 0)
      gu = gen-at (suc s) sL u cu (just b) (bN , bL) u-ag
      Vc Uc : ν.C
      Vc = tabG v 0 , gen-cell (forget gv)
      Uc = tabG u 0 , gen-cell (forget gu)
      EV = exL (suc s) Pr (up gv) (snd Vc)
      EU = exL (suc s) Pr (up gu) (snd Uc)
      yv yu : 𝔇.C
      yv = fst EV
      yu = fst EU
      RV : Rel Vc yv
      RV = snd EV
      RU : Rel Uc yu
      RU = snd EU
      pν : ν.tgt s Vc ≡ ν.src s Uc
      pν = ≡-cell K L vu-m
      qD : 𝔇.tgt s yv ≡ 𝔇.src s yu
      qD = match𝔇 (suc s) Pr s (≤-suc (≤-refl s)) RV RU pν
      eX : ν.comp s Vc Uc pν ≡ ν.comp r x₁ x₂ p
      eX = ≡-cell K L vu-eq
      sr : s < r
      sr = ≤-refl _
      -- The original order (b, c).
      sp′ν = SSν.split′ sr Vc Uc pν
      sp′D = SSD.split′ sr yv yu qD
      p′₁ν = fst sp′ν
      p′₂ν = fst (snd sp′ν)
      q′ν  = fst (snd (snd sp′ν))
      eq′ν = snd (snd (snd sp′ν))
      p′₁D = fst sp′D
      p′₂D = fst (snd sp′D)
      q′D  = fst (snd (snd sp′D))
      eq′D = snd (snd (snd sp′D))
      A₁ A₂ : ν.C
      A₁ = ν.comp s (ν.src r Vc) Uc p′₁ν
      A₂ = ν.comp s Vc (ν.tgt r Uc) p′₂ν
      RA₁ = rel-comp s (rel-bd σ⁻ r RV) RU p′₁ν p′₁D
      RA₂ = rel-comp s RV (rel-bd σ⁺ r RU) p′₂ν p′₂D
      h₁ : Agree r (rows x₁) (rows A₁)
      h₁ j rj jL = trans (ag₁ j rj jL) (sym
        (trans (rows-comp s (ν.src r Vc) Uc p′₁ν j (<→≤ rj))
          (trans (cong₂ _+R_ (rows-src r Vc j rj) (trans (rows-tabG u (snd Uc) j jL) (u-ag j rj jL))) (+R-idl (ent b j)))))
      h₂ : Agree r (rows x₂) (rows A₂)
      h₂ j rj jL = trans (ag₂ j rj jL) (sym
        (trans (rows-comp s Vc (ν.tgt r Uc) p′₂ν j (<→≤ rj))
          (trans (cong₂ _+R_ (trans (rows-tabG v (snd Vc) j jL) (v-ag j rj jL)) (rows-tgt r Uc j rj)) (+R-idr (ent c j)))))
      fs = factors r (fst x₁) (fst x₂) (fst A₁) (fst A₂) (snd x₁) (snd x₂) (snd A₁) (snd A₂)
                   (cong fst p) (cong fst q′ν) (cong fst (trans (sym eX) eq′ν)) (above r x₁ A₁ h₁) (above r x₂ A₂ h₂)
      e₁ : x₁ ≡ A₁
      e₁ = ≡-cell K L (fst fs)
      e₂ : x₂ ≡ A₂
      e₂ = ≡-cell K L (snd fs)
      -- The swapped order (c, b).
      spν = SSν.split sr Vc Uc pν
      spD = SSD.split sr yv yu qD
      p₁ν = fst spν
      p₂ν = fst (snd spν)
      qν  = fst (snd (snd spν))
      eqν = snd (snd (snd spν))
      p₁D = fst spD
      p₂D = fst (snd spD)
      qD′ = fst (snd (snd spD))
      eqD = snd (snd (snd spD))

    ------------------------------------------------------------------
    -- Moving the least label to the front.

    data Fr (r : Nat) (x : ν.C) (y : 𝔇.C) (c : Vec Nat N) (m : Nat) : Set where
      fr1 : Rel x y → Lab r x m → c ≡ unit m → Fr r x y c m
      fr∷ : ∀ {x₁ y₁ x₂ y₂ c′} → Rel x₁ y₁ → Lab r x₁ m → Ch r x₂ y₂ c′ →
            (p : ν.tgt r x₁ ≡ ν.src r x₂) (q : 𝔇.tgt r y₁ ≡ 𝔇.src r y₂) →
            x ≡ ν.comp r x₁ x₂ p → y ≡ 𝔇.comp r y₁ y₂ q → c ≡ unit m +c c′ → Fr r x y c m

    Least : Vec Nat N → Nat → Set
    Least c m = (1 ≤ at0 c m) × (∀ g → 1 ≤ at0 c g → m ≤ g)

    private
      module Rν = Rot (nu K L)
      module RD = Rot 𝒟

      at-ug : ∀ g c k → at0 (unit {N} g +c c) k ≡ at0 (unit {N} g) k + at0 c k
      at-ug g c k = at-+c (unit {N} g) c k

      1≤+l : ∀ a b → 1 ≤ b → 1 ≤ a + b
      1≤+l zero    b h = h
      1≤+l (suc a) b h = s≤s z≤n

      1≤+r : ∀ a b → 1 ≤ a → 1 ≤ a + b
      1≤+r (suc a) b h = s≤s z≤n

      at-self : ∀ g → g < N → 1 ≤ at0 (unit {N} g) g
      at-self g gN = subst (1 ≤_) (sym (at-unit-self′ g gN)) (≤-refl 1)
        where
        at-unit-self′ : ∀ g → g < N → at0 (unit {N} g) g ≡ 1
        at-unit-self′ g gN = go g gN
          where
          go : ∀ {m} g → g < m → at0 (unit {m} g) g ≡ 1
          go {suc m} zero    _       = refl
          go {suc m} (suc g) (s≤s l) = go {m} g l

      at-other : ∀ k g → (k ≡ g → ⊥) → at0 (unit {N} k) g ≡ 0
      at-other k g ne with tri k g
      ... | tri< l = unit-Lo {N} k g l
      ... | tri≡ e = ⊥-elim (ne e)
      ... | tri> l = unit-Hi {N} k g l

      ¬1≤0 : 1 ≤ 0 → ⊥
      ¬1≤0 ()

      swap4 : (a b c : Vec Nat N) → a +c (b +c c) ≡ b +c (a +c c)
      swap4 a b c = trans (sym (+c-assoc a b c)) (trans (cong (_+c c) (+c-comm a b)) (+c-assoc b a c))

    front : ∀ r → Lf r → ∀ {x y c} → Ch r x y c → ∀ m → Least c m → Fr r x y c m
    front r Pr (ch1 {g = g} R l) m (cm , _) with tri g m
    ... | tri≡ refl = fr1 R l refl
    ... | tri< gm = ⊥-elim (¬1≤0 (subst (1 ≤_) (at-other g m (λ e → ≤-<-⊥ (≤-of e) gm)) cm))
      where
      ≤-of : ∀ {a b} → a ≡ b → b ≤ a
      ≤-of refl = ≤-refl _
    ... | tri> mg = ⊥-elim (¬1≤0 (subst (1 ≤_) (at-other g m (λ e → ≤-<-⊥ (≤-of e) mg)) cm))
      where
      ≤-of : ∀ {a b} → a ≡ b → a ≤ b
      ≤-of refl = ≤-refl _
    front r Pr (ch∷ {x = x} {y = y} {g = g} {c = c′} R l ch p q) m (cm , mn) with tri g m
    ... | tri≡ refl = fr∷ R l ch p q refl refl refl
    ... | tri< gm = ⊥-elim (≤-<-⊥ (mn g (subst (1 ≤_) (sym (at-ug g c′ g)) (1≤+r _ _ (at-self g (fst (snd (snd l))))))) gm)
    ... | tri> mg with front r Pr ch m (cm′ , λ g′ h → mn g′ (subst (1 ≤_) (sym (at-ug g c′ g′)) (1≤+l _ _ h)))
      where
      cm′ : 1 ≤ at0 c′ m
      cm′ = subst (1 ≤_) (trans (at-ug g c′ m) (cong (_+ at0 c′ m) (at-other g m (λ e → ≤-<-⊥ (≤-of e) mg)))) cm
        where
        ≤-of : ∀ {a b} → a ≡ b → a ≤ b
        ≤-of refl = ≤-refl _
    ... | fr1 R′ l′ refl =
      let S = swap r Pr R l R′ l′ mg p q in
      fr∷ (Sw.R₁ S) (Sw.l₁ S) (ch1 (Sw.R₂ S) (Sw.l₂ S)) (Sw.p S) (Sw.q S) (Sw.eν S) (Sw.eD S) (+c-comm (unit {N} g) (unit {N} m))
    ... | fr∷ {x₁ = x₁} {y₁ = y₁} {x₂ = x₂} {y₂ = y₂} {c′ = c₂} R₁ l₁ ch₂ p₁ q₁ refl refl refl =
      let S = swap r Pr R l R₁ l₁ mg (Rν.pab r x x₁ x₂ p₁ p) (RD.pab r y y₁ y₂ q₁ q)
          (p₃ , p₄ , eν) = Rν.rot r x x₁ x₂ p₁ p (Sw.x₁ S) (Sw.x₂ S) (Sw.p S) (Sw.eν S)
          (q₃ , q₄ , eD) = RD.rot r y y₁ y₂ q₁ q (Sw.y₁ S) (Sw.y₂ S) (Sw.q S) (Sw.eD S)
      in fr∷ (Sw.R₁ S) (Sw.l₁ S) (ch∷ (Sw.R₂ S) (Sw.l₂ S) ch₂ p₃ q₃) p₄ q₄ eν eD (swap4 (unit {N} g) (unit {N} m) c₂)
