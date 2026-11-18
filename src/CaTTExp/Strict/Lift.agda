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
open import CaTTExp.Strict.StdSem using (module StdSem; cmpR)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)
open import CaTTExp.Strict.Bag using (+-zero; +-assoc; +-comm)

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

    ------------------------------------------------------------------
    -- Two chains with the same ν-value have the same 𝒟-value.

    private
      sumv-0 : ∀ {m} → sumv (0c {m}) ≡ 0
      sumv-0 {zero}  = refl
      sumv-0 {suc m} = sumv-0 {m}

      sumv-+ : ∀ {m} (u v : Vec Nat m) → sumv (u +c v) ≡ sumv u + sumv v
      sumv-+ []      []      = refl
      sumv-+ (a ∷ u) (b ∷ v) =
        trans (cong ((a + b) +_) (sumv-+ u v))
          (trans (+-assoc a b (sumv u + sumv v))
            (trans (cong (a +_) (trans (sym (+-assoc b (sumv u) (sumv v)))
                                   (trans (cong (_+ sumv v) (+-comm b (sumv u))) (+-assoc (sumv u) b (sumv v)))))
              (sym (+-assoc a (sumv u) (b + sumv v)))))

      sumv-unit : ∀ {m} g → g < m → sumv (unit {m} g) ≡ 1
      sumv-unit {suc m} zero    _       = cong suc (sumv-0 {m})
      sumv-unit {suc m} (suc g) (s≤s l) = sumv-unit {m} g l

      unit-supp : ∀ r g → r < deg g → deg g ≤ L → Supp r (unit g)
      unit-supp r g rg gL k h with tri k g
      ... | tri≡ refl = ⊥-elim (out h)
        where
        out : (deg k ≤ r) ⊎ (L < deg k) → ⊥
        out (inj₁ a) = ≤-<-⊥ a rg
        out (inj₂ b) = ≤-<-⊥ gL b
      ... | tri< l = at-other g k (λ e → ≤-<-⊥ (≤-of (sym e)) l)
        where
        ≤-of : ∀ {a b} → a ≡ b → b ≤ a
        ≤-of refl = ≤-refl _
      ... | tri> l = at-other g k (λ e → ≤-<-⊥ (≤-of e) l)
        where
        ≤-of : ∀ {a b} → a ≡ b → b ≤ a
        ≤-of refl = ≤-refl _

    ch-supp : ∀ {r x y c} → Ch r x y c → Supp r c
    ch-supp {r} (ch1 {g = g} _ (rg , gL , _ , _)) = unit-supp r g rg gL
    ch-supp {r} (ch∷ {g = g} {c = c} _ (rg , gL , _ , _) ch _ _) k h =
      trans (at-+c (unit {N} g) c k) (cong₂ _+_ (unit-supp r g rg gL k h) (ch-supp ch k h))

    ch-nz : ∀ {r x y c} → Ch r x y c → Σ Nat (λ g → 1 ≤ at0 c g)
    ch-nz (ch1 {g = g} _ (_ , _ , gN , _))                 = g , at-self g gN
    ch-nz (ch∷ {g = g} {c = c} _ (_ , _ , gN , _) _ _ _) = g , subst (1 ≤_) (sym (at-ug g c g)) (1≤+r _ _ (at-self g gN))

    ch-sum : ∀ {r x y c} → Ch r x y c → 1 ≤ sumv c
    ch-sum (ch1 {g = g} _ (_ , _ , gN , _))                 = subst (1 ≤_) (sym (sumv-unit g gN)) (≤-refl 1)
    ch-sum (ch∷ {g = g} {c = c} _ (_ , _ , gN , _) _ _ _) =
      subst (1 ≤_) (sym (trans (sumv-+ (unit {N} g) c) (cong (_+ sumv c) (sumv-unit g gN)))) (s≤s z≤n)

    least-of : ∀ c → Σ Nat (λ g → 1 ≤ at0 c g) → Σ Nat (Least c)
    least-of c (g , h) with least c
    ... | inj₁ refl = ⊥-elim (¬1≤0 (subst (1 ≤_) (at-0c {N} g) h))
    ... | inj₂ (m , hi , k , e) = m , subst (1 ≤_) (sym e) (s≤s z≤n) , mn
      where
      mn : ∀ g′ → 1 ≤ at0 c g′ → m ≤ g′
      mn g′ h′ with tri m g′
      ... | tri< l    = <→≤ l
      ... | tri≡ refl = ≤-refl _
      ... | tri> l    = ⊥-elim (¬1≤0 (subst (1 ≤_) (hi g′ l) h′))

    ch-sub : ∀ {r x x′ y c} → x ≡ x′ → Ch r x y c → Ch r x′ y c
    ch-sub refl ch = ch

    private
      cancel-u : ∀ m (a b : Vec Nat N) → unit {N} m +c a ≡ unit m +c b → a ≡ b
      cancel-u m a b e = +c-cancel a b (unit m) (trans (+c-comm a (unit m)) (trans e (+c-comm (unit m) b)))

      not-single : ∀ {r x y} m c → Ch r x y c → unit {N} m ≡ unit m +c c → ⊥
      not-single m c ch e = ¬1≤0 (subst (1 ≤_) (at-0c {N} g) (subst (λ v → 1 ≤ at0 v g) c0 h))
        where
        g = fst (ch-nz ch)
        h = snd (ch-nz ch)
        c0 : c ≡ 0c
        c0 = sym (cancel-u m 0c c (trans (trans (+c-comm (unit m) 0c) (+c-id (unit m))) e))

    chUn : ∀ r → Lf r → ∀ n {x y y′ c c′} → sumv c < n → Ch r x y c → Ch r x y′ c′ → y ≡ y′
    chUn r Pr (suc n) {x} {c = c} {c′} sn ch ch′
      with least-of c (ch-nz ch)
    ... | m , lst with front r Pr ch m lst
                     | front r Pr ch′ m (subst (λ v → Least v m) cc lst)
      where
      cc : c ≡ c′
      cc = esum-inj r c c′ (ch-supp ch) (ch-supp ch′)
             (λ j rj jL → cong fst (trans (sym (rowsCh ch j rj jL)) (rowsCh ch′ j rj jL)))
    ... | fr1 R (_ , mL , mN , ag) _ | fr1 R′ _ _ = Pr x (just m) (mN , mL) ag R R′
    ... | fr1 _ _ e | fr∷ _ _ ch₂′ _ _ _ _ e′ = ⊥-elim (not-single m _ ch₂′ (trans (sym e) (trans cc e′)))
      where
      cc : c ≡ c′
      cc = esum-inj r c c′ (ch-supp ch) (ch-supp ch′)
             (λ j rj jL → cong fst (trans (sym (rowsCh ch j rj jL)) (rowsCh ch′ j rj jL)))
    ... | fr∷ _ _ ch₂ _ _ _ _ e | fr1 _ _ e′ = ⊥-elim (not-single m _ ch₂ (trans (sym e′) (trans (sym cc) e)))
      where
      cc : c ≡ c′
      cc = esum-inj r c c′ (ch-supp ch) (ch-supp ch′)
             (λ j rj jL → cong fst (trans (sym (rowsCh ch j rj jL)) (rowsCh ch′ j rj jL)))
    ... | fr∷ {x₁ = x₁} {x₂ = x₂} {c′ = c₂} R₁ (_ , mL , mN , ag₁) ch₂ p q ex ey ec
        | fr∷ {x₁ = x₁′} {x₂ = x₂′} {c′ = c₂′} R₁′ (_ , _ , _ , ag₁′) ch₂′ p′ q′ ex′ ey′ ec′ =
      trans ey (trans (BD.comp-cong r q q′ y1 y2) (sym ey′))
      where
      cc : c ≡ c′
      cc = esum-inj r c c′ (ch-supp ch) (ch-supp ch′)
             (λ j rj jL → cong fst (trans (sym (rowsCh ch j rj jL)) (rowsCh ch′ j rj jL)))
      c22 : c₂ ≡ c₂′
      c22 = cancel-u m c₂ c₂′ (trans (sym ec) (trans cc ec′))
      fs = factors r (fst x₁) (fst x₂) (fst x₁′) (fst x₂′) (snd x₁) (snd x₂) (snd x₁′) (snd x₂′)
                   (cong fst p) (cong fst p′) (cong fst (trans (sym ex) ex′))
                   (above r x₁ x₁′ (λ j rj jL → trans (ag₁ j rj jL) (sym (ag₁′ j rj jL))))
                   (above r x₂ x₂′ (λ j rj jL → trans (rowsCh ch₂ j rj jL)
                                                 (trans (cong (λ v → RS v j) c22) (sym (rowsCh ch₂′ j rj jL)))))
      e₁ : x₁ ≡ x₁′
      e₁ = ≡-cell K L (fst fs)
      e₂ : x₂ ≡ x₂′
      e₂ = ≡-cell K L (snd fs)
      y1 = Pr x₁ (just m) (mN , mL) ag₁ R₁ (rel-sub (sym e₁) refl R₁′)
      lt : sumv c₂ < n
      lt = ≤-pred″ (subst (_< suc n) (trans (cong sumv ec) (trans (sumv-+ (unit {N} m) c₂) (cong (_+ sumv c₂) (sumv-unit m mN)))) sn)
        where
        ≤-pred″ : ∀ {a b} → suc a ≤ suc b → a ≤ b
        ≤-pred″ (s≤s l) = l
      y2 = chUn r Pr n lt ch₂ (ch-sub (sym e₂) ch₂′)

    ------------------------------------------------------------------
    -- Standard forms as chains.

    private
      module St = S.Std degG W
      module Sg = Single W
      module WFP = St.WFProof W-co W-deg
      module SPν = St.SemProof (nu K L) (ιν B H L) W-co W-deg dimν W-evν
      module SPD = St.SemProof 𝒟 κ W-co W-deg dimκ W-evD
      module DPν = St.DimProof (nu K L) (ιν B H L) dimν

    open St using (_∷ᶠ_)

    toCh : ∀ r f fs {x y} → St.AllF r (f ∷ fs) → Eν.Ev (cmpR r f fs) x → ED.Ev (cmpR r f fs) y →
           Σ (Vec Nat N) (λ c → Ch r x y c × (sumv c ≡ St.len (f ∷ fs)))
    toCh r f [] ((cf , hf) ∷ᶠ _) u v with Sg.single-rows r f cf hf u
    ... | (i , iN , iL) , ri , ag = unit i , ch1 (f , cf , u , v) (ri , iL , iN , ag) , sumv-unit i iN
    toCh r f (g ∷ gs) ((cf , hf) ∷ᶠ a) (Eν.ev-cmp .r u u′ p) (ED.ev-cmp .r v v′ q) with Sg.single-rows r f cf hf u
    ... | (i , iN , iL) , ri , ag =
      let (c , ch , sc) = toCh r g gs a u′ v′ in
      unit i +c c , ch∷ (f , cf , u , v) (ri , iL , iN , ag) ch p q ,
      trans (sumv-+ (unit {N} i) c) (trans (cong (_+ sumv c) (sumv-unit i iN)) (cong suc sc))

    private
      case01 : ∀ n → n ≤ 1 → (n ≡ 0) ⊎ (n ≡ 1)
      case01 zero          _         = inj₁ refl
      case01 (suc zero)    _         = inj₂ refl
      case01 (suc (suc n)) (s≤s ())

      agree-up : ∀ {t r f g} → t ≤ r → Agree t f g → Agree r f g
      agree-up tr ag j rj jL = ag j (≤-trans (s≤s tr) rj) jL

    -- At most one generator above t: the value agrees above t with an
    -- atom or zero.
    low-shape : ∀ t e {x} → CO e → St.hi t e ≤ 1 → Eν.Ev e x → Σ (Maybe Nat) (λ A → AOKL A × Agree t (rows x) (Arow A))
    low-shape t e {x} co h u with case01 (St.hi t e) h
    ... | inj₁ h0 = nothing , tt , λ j tj _ →
            trans (cong (λ z → rows z j) (sym (DPν.dimLe (St.hi→DegLe co h0) u))) (rows-src t x j tj)
    ... | inj₂ h1 with Sg.single-rows t e co h1 u
    ...   | (i , iN , iL) , _ , ag = just i , (iN , iL) , ag

    data Shape (r : Nat) (x : ν.C) (y : 𝔇.C) : Set where
      sh-low : ∀ A → AOKL A → Agree r (rows x) (Arow A) → Shape r x y
      sh-ch  : ∀ {c} → Ch r x y c → 2 ≤ sumv c → Shape r x y
      sh-hi  : ∀ r′ {c} → r < r′ → Ch r′ x y c → 2 ≤ sumv c → Shape r x y

    shape : ∀ r e {x y} → CO e → Eν.Ev e x → ED.Ev e y → Shape r x y
    shape r e co u v = go (St.std e) (WFP.std-wf e co) (SPν.std-sem e co u) (SPD.std-sem e co v)
      where
      go : ∀ R {x y} → St.WF R → Eν.Ev (St.toE R) x → ED.Ev (St.toE R) y → Shape r x y
      go (St.one (i , iN , iL)) _ (Eν.ev-gen _) _ = sh-low (just i) (iN , iL) (λ j _ jL → rows-atom i iN iL j jL)
      go (St.many r′ f fs) {x} (a , l , t) u′ v′ with toCh r′ f fs a u′ v′
      ... | c , ch , sc with tri r′ r
      ...   | tri≡ refl = sh-ch ch two
        where
        two : 2 ≤ sumv c
        two = subst (2 ≤_) (sym sc) (s≤s l)
      ...   | tri> rr = sh-hi r′ rr ch (subst (2 ≤_) (sym sc) (s≤s l))
      ...   | tri< rr =
        let (A , ok , ag) = low-shape (suc r′) (cmpR r′ f fs) (St.co-cmpR r′ f fs a)
                              (subst (_≤ 1) (sym (St.hi-cmpR (suc r′) r′ f fs)) t) u′
        in sh-low A ok (agree-up rr ag)

    -- A chain of at least two factors at r′ does not agree above r′
    -- with an atom or zero.
    many-absurd : ∀ t r′ {x y c A} → t ≤ r′ → Ch r′ x y c → 2 ≤ sumv c → AOKL A → Agree t (rows x) (Arow A) → ⊥
    many-absurd t r′ {x} {c = c} {A} tr ch two ok ag = go A ok (agree-up tr ag)
      where
      tooMany : ∀ c′ → c ≡ c′ → sumv c′ ≤ 1 → ⊥
      tooMany c′ e h = ≤-<-⊥ h (subst (1 <_) (cong sumv e) two)
      go : ∀ A → AOKL A → Agree r′ (rows x) (Arow A) → ⊥
      go nothing _ ag′ =
        tooMany 0c (esum-inj r′ c 0c (ch-supp ch) (λ k _ → at-0c {N} k)
                      (λ j rj jL → cong fst (trans (sym (rowsCh ch j rj jL)) (trans (ag′ j rj jL) (sym (RS0 j))))))
                (subst (_≤ 1) (sym (sumv-0 {N})) z≤n)
        where
        RS0 : ∀ j → RS 0c j ≡ 0R
        RS0 j = cong₂ _,_ (esum-0 {N} fst 0 j) (esum-0 {N} snd 0 j)
      go (just a) (aN , aL) ag′ with tri r′ (deg a)
      ... | tri< ra =
        tooMany (unit a) (esum-inj r′ c (unit a) (ch-supp ch) (unit-supp r′ a ra aL)
                            (λ j rj jL → cong fst (trans (sym (rowsCh ch j rj jL)) (trans (ag′ j rj jL) (sym (RS-unit a j aN))))))
                (subst (_≤ 1) (sym (sumv-unit a aN)) (≤-refl 1))
      ... | tri≡ e = go nothing tt (λ j rj jL → trans (ag′ j rj jL) (ent-zero a j (subst (_< j) e rj)))
      ... | tri> ar = go nothing tt (λ j rj jL → trans (ag′ j rj jL) (ent-zero a j (≤-trans (s≤s (<→≤ ar)) rj)))

    ------------------------------------------------------------------
    -- Atoms are distinct.

    private
      ≤-prop : ∀ {a b} (p q : a ≤ b) → p ≡ q
      ≤-prop z≤n     z≤n     = refl
      ≤-prop (s≤s p) (s≤s q) = cong s≤s (≤-prop p q)

      1≢0 : 1 ≡ 0 → ⊥
      1≢0 ()

      top1 : ∀ k → k < N → at0 (fst (ent k (deg k))) k ≡ 1
      top1 k kN = trans (cong (λ z → at0 (fst z) k) (Cells.Deg.ent-in dd deg-dp deg-dm k (deg k) 0 (sym (+-zero (deg k)))))
                        (go k kN)
        where
        go : ∀ {m} g → g < m → at0 (unit {m} g) g ≡ 1
        go {suc m} zero    _       = refl
        go {suc m} (suc g) (s≤s l) = go {m} g l

      top0 : ∀ k i → (k ≡ i → ⊥) → at0 (fst (ent k (deg k))) i ≡ 0
      top0 k i ne = trans (cong (λ z → at0 (fst z) i) (Cells.Deg.ent-in dd deg-dp deg-dm k (deg k) 0 (sym (+-zero (deg k)))))
                          (at-other k i ne)

      above0 : ∀ k j i → deg k < j → at0 (fst (ent k j)) i ≡ 0
      above0 k j i l = trans (cong (λ z → at0 (fst z) i) (ent-zero k j l)) (at-0c {N} i)

    ιν-inj : ∀ g g′ → ιν B H L g ≡ ιν B H L g′ → g ≡ g′
    ιν-inj (i , iN , iL) (i′ , iN′ , iL′) e with ii
      where
      co : ∀ j → j ≤ L → ∀ k → at0 (fst (ent i j)) k ≡ at0 (fst (ent i′ j)) k
      co j jL k = cong (λ z → at0 (fst z) k)
                    (trans (sym (rows-atom i iN iL j jL)) (trans (cong (λ z → rows z j) e) (rows-atom i′ iN′ iL′ j jL)))
      ii : i ≡ i′
      ii with tri (deg i) (deg i′)
      ... | tri< l = ⊥-elim (1≢0 (trans (sym (top1 i′ iN′)) (trans (sym (co (deg i′) iL′ i′)) (above0 i (deg i′) i′ l))))
      ... | tri> l = ⊥-elim (1≢0 (trans (sym (top1 i iN)) (trans (co (deg i) iL i) (above0 i′ (deg i) i l))))
      ... | tri≡ d with tri i i′
      ...   | tri≡ q = q
      ...   | tri< q = ⊥-elim (1≢0 (trans (sym (top1 i iN))
                         (trans (co (deg i) iL i) (trans (cong (λ t → at0 (fst (ent i′ t)) i) d)
                           (top0 i′ i (λ z → ≤-<-⊥ (≤-of z) q))))))
        where
        ≤-of : ∀ {a b} → a ≡ b → a ≤ b
        ≤-of refl = ≤-refl _
      ...   | tri> q = ⊥-elim (1≢0 (trans (sym (top1 i iN))
                         (trans (co (deg i) iL i) (trans (cong (λ t → at0 (fst (ent i′ t)) i) d)
                           (top0 i′ i (λ z → ≤-<-⊥ (≤-of z) q))))))
        where
        ≤-of : ∀ {a b} → a ≡ b → b ≤ a
        ≤-of refl = ≤-refl _
    ... | refl = cong₂ (λ a b → i , a , b) (≤-prop iN iN′) (≤-prop iL iL′)

    ------------------------------------------------------------------
    -- The induction.

    base-at : ∀ e {x y A} → CO e → Eν.Ev e x → ED.Ev e y → AOKL A → Agree 0 (rows x) (Arow A) →
              Σ G (λ g → (x ≡ ιν B H L g) × (y ≡ κ g))
    base-at e {A = A} co u v ok ag = go (St.std e) (WFP.std-wf e co) (SPν.std-sem e co u) (SPD.std-sem e co v) ag
      where
      go : ∀ R {x y} → St.WF R → Eν.Ev (St.toE R) x → ED.Ev (St.toE R) y → Agree 0 (rows x) (Arow A) →
           Σ G (λ g → (x ≡ ιν B H L g) × (y ≡ κ g))
      go (St.one g) _ (Eν.ev-gen _) (ED.ev-gen _) _ = g , refl , refl
      go (St.many r′ f fs) (a , l , t) u′ v′ ag′ with toCh r′ f fs a u′ v′
      ... | c , ch , sc = ⊥-elim (many-absurd 0 r′ z≤n ch (subst (2 ≤_) (sym sc) (s≤s l)) ok ag′)

    Lf0 : Lf 0
    Lf0 x A ok ag (e , co , u , v) (e′ , co′ , u′ , v′) with base-at e co u v ok ag | base-at e′ co′ u′ v′ ok ag
    ... | g , ex , ey | g′ , ex′ , ey′ = trans ey (trans (cong κ (ιν-inj g g′ (trans (sym ex) ex′))) (sym ey′))

    LfS : ∀ r → Lf r → Lf (suc r)
    LfS r Pr x A ok ag (e , co , u , v) (e′ , co′ , u′ , v′) with shape r e co u v | shape r e′ co′ u′ v′
    ... | sh-low A′ ok′ ag′ | _                  = Pr x A′ ok′ ag′ (e , co , u , v) (e′ , co′ , u′ , v′)
    ... | sh-ch _ _         | sh-low A′ ok′ ag′  = Pr x A′ ok′ ag′ (e , co , u , v) (e′ , co′ , u′ , v′)
    ... | sh-hi r′ rr ch two | _                 = ⊥-elim (many-absurd (suc r) r′ rr ch two ok ag)
    ... | sh-ch _ _         | sh-hi r′ rr ch two = ⊥-elim (many-absurd (suc r) r′ rr ch two ok ag)
    ... | sh-ch ch _        | sh-ch ch′ _        = chUn r Pr _ (≤-refl _) ch ch′

    Lf-all : ∀ r → Lf r
    Lf-all zero    = Lf0
    Lf-all (suc r) = LfS r (Lf-all r)

    -- Unique lifting: composition-only expressions with the same value
    -- in ν(K) have the same value in 𝒟.
    unique : ∀ x → UnFor x
    unique x = Lf-all L x nothing tt (λ j Lj jL → ⊥-elim (≤-<-⊥ jL Lj))
