------------------------------------------------------------------------
-- For an ordered globular basis, ν of it is free on its generators
-- (ledger A5, (N3), first part: ν(λΓ) ≅ Free(Γ) when λΓ is presented
-- by such a basis).
--
-- A globular basis: every basis element i of degree ≥ 1 has
-- ∂⁻i = s i and ∂⁺i = t i, single basis elements of degree deg i − 1.
-- `Glob` takes the basis, s, t and `Hyp` as parameters; it does not
-- build λΓ from a globular set Γ. `Hyp` includes the order
-- s i < i < t i (strong loop-freeness), which excludes some globular
-- sets, for example α : f ⇒ g together with β : g ⇒ f. Under these
-- hypotheses, the boundaries of
-- the atom ⟨g⟩ are the atoms of its source and target (`atom-src`,
-- `atom-tgt`). So the attaching words of `Strict.Lift` are single
-- generators, and a strict functor ν(λΓ) → 𝒟 is the same as a map of
-- globular sets Γ → 𝒟 (`functor`, `functor-gen`, `unique`).
------------------------------------------------------------------------
module CaTTExp.Strict.FreeGlob where

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
import CaTTExp.Strict.Lift as LF
open import CaTTExp.Strict.Bag using (+-zero; +-suc)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

module Glob {N : Nat} (B : Basis N) (H : Hyp B) (L : Nat) (s t : Nat → Nat)
            (bm : ∀ i → i < N → 1 ≤ Atom.deg B i → at 0c (Basis.bminus B) i ≡ unit (s i))
            (bp : ∀ i → i < N → 1 ≤ Atom.deg B i → at 0c (Basis.bplus B) i ≡ unit (t i))
            (sN : ∀ i → i < N → 1 ≤ Atom.deg B i → s i < N)
            (tN : ∀ i → i < N → 1 ≤ Atom.deg B i → t i < N)
            (ds : ∀ i → i < N → 1 ≤ Atom.deg B i → Atom.deg B (s i) ≡ Atom.deg B i ∸ 1)
            (dt : ∀ i → i < N → 1 ≤ Atom.deg B i → Atom.deg B (t i) ≡ Atom.deg B i ∸ 1) where
  open Basis B
  open Hyp H
  open Atom B
  open Gen B H L hiding (Functor; W)

  private
    module ν = ωCat (nu K L)
    dp = dP B
    dm = dM B

    1≢0 : 1 ≡ 0 → ⊥
    1≢0 ()

    ≤-of : ∀ {a b} → a ≡ b → a ≤ b
    ≤-of refl = ≤-refl _

    ≥-of : ∀ {a b} → a ≡ b → b ≤ a
    ≥-of refl = ≤-refl _

    at-self : ∀ {m} g → g < m → at0 (unit {m} g) g ≡ 1
    at-self {suc m} zero    _       = refl
    at-self {suc m} (suc g) (s≤s l) = at-self {m} g l

    at-other : ∀ {m} k g → (k ≡ g → ⊥) → at0 (unit {m} k) g ≡ 0
    at-other {m} k g ne with tri k g
    ... | tri< l = unit-Lo {m} k g l
    ... | tri≡ e = ⊥-elim (ne e)
    ... | tri> l = unit-Hi {m} k g l

    lin-unit : ∀ {M m} i → i < m → (vs : Vec (Vec Nat M) m) → lin (unit {m} i) vs ≡ at 0c vs i
    lin-unit {M} {suc m} zero    _       (v ∷ vs) =
      trans (cong₂ _+c_ (trans (+c-comm v 0c) (+c-id v)) (lin-0 vs)) (trans (+c-comm v 0c) (+c-id v))
    lin-unit {M} {suc m} (suc i) (s≤s l) (v ∷ vs) = trans (+c-id (lin (unit {m} i) vs)) (lin-unit i l vs)

    0∸′ : ∀ n → 0 ∸ n ≡ 0
    0∸′ zero    = refl
    0∸′ (suc n) = refl

    unit∸ : ∀ a b → (a ≡ b → ⊥) → unit {N} a ∸c unit b ≡ unit a
    unit∸ a b ne = vext _ _ λ d → trans (at-∸c (unit {N} a) (unit {N} b) d) (go d)
      where
      go : ∀ d → at0 (unit {N} a) d ∸ at0 (unit {N} b) d ≡ at0 (unit {N} a) d
      go d with tri b d
      ... | tri≡ refl = trans (cong (_∸ at0 (unit {N} b) b) (at-other {N} a b ne))
                          (trans (0∸′ (at0 (unit {N} b) b)) (sym (at-other {N} a b ne)))
      ... | tri< l = cong (at0 (unit {N} a) d ∸_) (unit-Lo {N} b d l)
      ... | tri> l = cong (at0 (unit {N} a) d ∸_) (unit-Hi {N} b d l)

  open Cells dd using (module Deg)
  open Deg deg-dp deg-dm using (ent-in)

  ----------------------------------------------------------------------
  -- The order and the boundaries of single elements.

  s-lt : ∀ i → i < N → 1 ≤ deg i → s i < i
  s-lt i iN di with tri (s i) i
  ... | tri< l = l
  ... | tri≡ e = ⊥-elim (1≢0 (trans (sym (at-self (s i) (sN i iN di)))
                   (trans (cong (λ v → at0 v (s i)) (sym (bm i iN di))) (ordm i (s i) (≥-of e)))))
  ... | tri> l = ⊥-elim (1≢0 (trans (sym (at-self (s i) (sN i iN di)))
                   (trans (cong (λ v → at0 v (s i)) (sym (bm i iN di))) (ordm i (s i) (<→≤ l)))))

  t-gt : ∀ i → i < N → 1 ≤ deg i → i < t i
  t-gt i iN di with tri i (t i)
  ... | tri< l = l
  ... | tri≡ e = ⊥-elim (1≢0 (trans (sym (at-self (t i) (tN i iN di)))
                   (trans (cong (λ v → at0 v (t i)) (sym (bp i iN di))) (ordp i (t i) (≥-of e)))))
  ... | tri> l = ⊥-elim (1≢0 (trans (sym (at-self (t i) (tN i iN di)))
                   (trans (cong (λ v → at0 v (t i)) (sym (bp i iN di))) (ordp i (t i) (<→≤ l)))))

  st-ne : ∀ i → i < N → 1 ≤ deg i → s i ≡ t i → ⊥
  st-ne i iN di e = ≤-<-⊥ (≤-trans (≤-of (sym e)) (<→≤ (s-lt i iN di))) (t-gt i iN di)

  dm-unit : ∀ i → i < N → 1 ≤ deg i → dm (unit i) ≡ unit (s i)
  dm-unit i iN di = trans (lin-unit i iN bminus) (bm i iN di)

  dp-unit : ∀ i → i < N → 1 ≤ deg i → dp (unit i) ≡ unit (t i)
  dp-unit i iN di = trans (lin-unit i iN bplus) (bp i iN di)

  step-unit : ∀ g → g < N → 1 ≤ deg g → step (unit g , unit g) ≡ (unit (s g) , unit (t g))
  step-unit g gN dg =
    cong₂ _,_ (trans (cong₂ _∸c_ (dm-unit g gN dg) (dp-unit g gN dg)) (unit∸ (s g) (t g) (st-ne g gN dg)))
              (trans (cong₂ _∸c_ (dp-unit g gN dg) (dm-unit g gN dg)) (unit∸ (t g) (s g) (λ e → st-ne g gN dg (sym e))))

  claim : ∀ g → g < N → 1 ≤ deg g → ∀ k → entK g (suc k) ≡ (fst (entK (s g) k) , snd (entK (t g) k))
  claim g gN dg zero    = step-unit g gN dg
  claim g gN dg (suc k) = cong step (claim g gN dg k)

  ----------------------------------------------------------------------
  -- Globular identities, from ∂∂ = 0 and the order.

  private
    pick : ∀ p q r u → p < N → unit {N} p +c unit q ≡ unit r +c unit u → (u ≡ p → ⊥) → r ≡ p
    pick p q r u pN E nu with tri r p
    ... | tri≡ e = e
    ... | tri< l = ⊥-elim (bad (at-other {N} r p (λ e → ≤-<-⊥ (≥-of e) l)))
      where
      bad : at0 (unit {N} r) p ≡ 0 → ⊥
      bad z = 1≢0′ (trans (sym (trans (at-+c (unit {N} p) (unit {N} q) p) (cong (_+ at0 (unit {N} q) p) (at-self {N} p pN))))
                     (trans (cong (λ v → at0 v p) E) (trans (at-+c (unit {N} r) (unit {N} u) p) (cong₂ _+_ z (at-other {N} u p nu)))))
        where
        1≢0′ : ∀ {x} → suc x ≡ 0 → ⊥
        1≢0′ ()
    ... | tri> l = ⊥-elim (bad (at-other {N} r p (λ e → ≤-<-⊥ (≤-of e) l)))
      where
      bad : at0 (unit {N} r) p ≡ 0 → ⊥
      bad z = 1≢0′ (trans (sym (trans (at-+c (unit {N} p) (unit {N} q) p) (cong (_+ at0 (unit {N} q) p) (at-self {N} p pN))))
                     (trans (cong (λ v → at0 v p) E) (trans (at-+c (unit {N} r) (unit {N} u) p) (cong₂ _+_ z (at-other {N} u p nu)))))
        where
        1≢0′ : ∀ {x} → suc x ≡ 0 → ⊥
        1≢0′ ()

  module G2 (g : Nat) (gN : g < N) (dg : 2 ≤ deg g) where
    private
      dg1 : 1 ≤ deg g
      dg1 = ≤-trans (≤-suc (≤-refl 1)) dg
      a = s g
      b = t g
      aN = sN g gN dg1
      bN = tN g gN dg1
      pred≤ : ∀ {d} → 2 ≤ d → 1 ≤ d ∸ 1
      pred≤ {suc (suc d)} _ = s≤s z≤n
      pred≤ {suc zero} (s≤s ())
      da : 1 ≤ deg a
      da = subst (1 ≤_) (sym (ds g gN dg1)) (pred≤ dg)
      db : 1 ≤ deg b
      db = subst (1 ≤_) (sym (dt g gN dg1)) (pred≤ dg)
      E : unit {N} (t b) +c unit (s a) ≡ unit (t a) +c unit (s b)
      E = trans (sym (cong₂ _+c_ (trans (cong dp (dp-unit g gN dg1)) (dp-unit b bN db))
                                 (trans (cong dm (dm-unit g gN dg1)) (dm-unit a aN da))))
            (trans (dd (unit g))
              (cong₂ _+c_ (trans (cong dp (dm-unit g gN dg1)) (dp-unit a aN da))
                          (trans (cong dm (dp-unit g gN dg1)) (dm-unit b bN db))))

    tt-ts : t (s g) ≡ t (t g)
    tt-ts = pick (t b) (s a) (t a) (s b) (tN b bN db) E (st-ne b bN db)

    ss-st : s (t g) ≡ s (s g)
    ss-st = pick (s a) (t b) (s b) (t a) (sN a aN da)
              (trans (+c-comm (unit (s a)) (unit (t b))) (trans E (+c-comm (unit (t a)) (unit (s b)))))
              (λ e → st-ne a aN da (sym e))

  ----------------------------------------------------------------------
  -- The boundaries of an atom, row by row.

  private
    pos : ∀ {d} → 1 ≤ d → suc (d ∸ 1) ≡ d
    pos {suc d} _ = refl

    deg-eq : ∀ g j m → 1 ≤ deg g → deg g ∸ 1 ≡ j + suc m → deg g ≡ j + suc (suc m)
    deg-eq g j m dg e = trans (sym (pos dg)) (trans (cong suc e) (sym (+-suc j (suc m))))

    two : ∀ {d j} → 1 ≤ d → j < d ∸ 1 → 2 ≤ d
    two {suc (suc d)} _ _ = s≤s (s≤s z≤n)
    two {suc zero} _ ()

  src-row : ∀ g → g < N → (dg : 1 ≤ deg g) → ∀ j → srcF (deg g ∸ 1) (ent g) j ≡ ent (s g) j
  src-row g gN dg j with view3 j (deg g ∸ 1)
  ... | vlt l rewrite cmp3-lt l =
    let (m , e) = <-split l
        sg = s g ; tg = t g
        d2 = two dg l
        dsg : 1 ≤ deg sg
        dsg = subst (1 ≤_) (sym (ds g gN dg)) (subst (λ k → 1 ≤ k) (sym e) (s≤s′ j m))
        dtg : 1 ≤ deg tg
        dtg = subst (1 ≤_) (sym (dt g gN dg)) (subst (λ k → 1 ≤ k) (sym e) (s≤s′ j m))
    in trans (ent-in g j (suc (suc m)) (deg-eq g j m dg e))
         (trans (claim g gN dg (suc m))
           (trans (cong₂ _,_ refl
                    (trans (cong snd (claim tg (tN g gN dg) dtg m))
                      (trans (cong (λ z → snd (entK z m)) (sym (G2.tt-ts g gN d2)))
                        (sym (cong snd (claim sg (sN g gN dg) dsg m))))))
             (sym (ent-in sg j (suc m) (trans (ds g gN dg) e)))))
    where
    s≤s′ : ∀ j m → 1 ≤ j + suc m
    s≤s′ zero    m = s≤s z≤n
    s≤s′ (suc j) m = s≤s z≤n
  ... | veq refl rewrite cmp3-eq (deg g ∸ 1) =
    let e1 : ent g (deg g ∸ 1) ≡ (unit (s g) , unit (t g))
        e1 = trans (ent-in g (deg g ∸ 1) 1 (trans (sym (pos dg)) (sym (+-suc (deg g ∸ 1) 0 ∙′ cong suc (+-zero _)))))
                   (step-unit g gN dg)
    in trans (cong (λ z → fst z , fst z) e1)
         (sym (ent-in (s g) (deg g ∸ 1) 0 (trans (ds g gN dg) (sym (+-zero _)))))
    where
    _∙′_ = trans
  ... | vgt l rewrite cmp3-gt l = sym (ent-zero (s g) j (subst (_< j) (sym (ds g gN dg)) l))

  tgt-row : ∀ g → g < N → (dg : 1 ≤ deg g) → ∀ j → tgtF (deg g ∸ 1) (ent g) j ≡ ent (t g) j
  tgt-row g gN dg j with view3 j (deg g ∸ 1)
  ... | vlt l rewrite cmp3-lt l =
    let (m , e) = <-split l
        sg = s g ; tg = t g
        d2 = two dg l
        dsg : 1 ≤ deg sg
        dsg = subst (1 ≤_) (sym (ds g gN dg)) (subst (λ k → 1 ≤ k) (sym e) (s≤s′ j m))
        dtg : 1 ≤ deg tg
        dtg = subst (1 ≤_) (sym (dt g gN dg)) (subst (λ k → 1 ≤ k) (sym e) (s≤s′ j m))
    in trans (ent-in g j (suc (suc m)) (deg-eq g j m dg e))
         (trans (claim g gN dg (suc m))
           (trans (cong₂ _,_
                    (trans (cong fst (claim sg (sN g gN dg) dsg m))
                      (trans (cong (λ z → fst (entK z m)) (sym (G2.ss-st g gN d2)))
                        (sym (cong fst (claim tg (tN g gN dg) dtg m)))))
                    refl)
             (sym (ent-in tg j (suc m) (trans (dt g gN dg) e)))))
    where
    s≤s′ : ∀ j m → 1 ≤ j + suc m
    s≤s′ zero    m = s≤s z≤n
    s≤s′ (suc j) m = s≤s z≤n
  ... | veq refl rewrite cmp3-eq (deg g ∸ 1) =
    let e1 : ent g (deg g ∸ 1) ≡ (unit (s g) , unit (t g))
        e1 = trans (ent-in g (deg g ∸ 1) 1 (trans (sym (pos dg)) (sym (+-suc (deg g ∸ 1) 0 ∙′ cong suc (+-zero _)))))
                   (step-unit g gN dg)
    in trans (cong (λ z → snd z , snd z) e1)
         (sym (ent-in (t g) (deg g ∸ 1) 0 (trans (dt g gN dg) (sym (+-zero _)))))
    where
    _∙′_ = trans
  ... | vgt l rewrite cmp3-gt l = sym (ent-zero (t g) j (subst (_< j) (sym (dt g gN dg)) l))

  ----------------------------------------------------------------------
  -- The boundaries of an atom are the atoms of its source and target.

  private
    sL : ∀ g → g < N → (dg : 1 ≤ deg g) → deg g ≤ L → deg (s g) ≤ L
    sL g gN dg gL = subst (_≤ L) (sym (ds g gN dg)) (≤-trans (∸1≤ (deg g)) gL)
      where
      ∸1≤ : ∀ d → d ∸ 1 ≤ d
      ∸1≤ zero    = z≤n
      ∸1≤ (suc d) = ≤-suc (≤-refl d)

    tL : ∀ g → g < N → (dg : 1 ≤ deg g) → deg g ≤ L → deg (t g) ≤ L
    tL g gN dg gL = subst (_≤ L) (sym (dt g gN dg)) (≤-trans (∸1≤ (deg g)) gL)
      where
      ∸1≤ : ∀ d → d ∸ 1 ≤ d
      ∸1≤ zero    = z≤n
      ∸1≤ (suc d) = ≤-suc (≤-refl d)

  atom-src : ∀ g (gN : g < N) (gL : deg g ≤ L) (dg : 1 ≤ deg g) →
             ν.src (deg g ∸ 1) (atom g gN gL) ≡ atom (s g) (sN g gN dg) (sL g gN dg gL)
  atom-src g gN gL dg = ≡-cell K L
    (trans (cong (srcT (ADC.𝕄 K) (deg g ∸ 1)) (atomT≡ (ent g) 0))
      (trans (src-tab (deg g ∸ 1) 0 (ent g))
        (trans (tabE (srcF ((deg g ∸ 1) + 0) (ent g)) (ent (s g)) 0 pt) (sym (atomT≡ (ent (s g)) 0)))))
    where
    pt : ∀ j → 0 ≤ j → srcF ((deg g ∸ 1) + 0) (ent g) j ≡ ent (s g) j
    pt j _ rewrite +-zero (deg g ∸ 1) = src-row g gN dg j

  atom-tgt : ∀ g (gN : g < N) (gL : deg g ≤ L) (dg : 1 ≤ deg g) →
             ν.tgt (deg g ∸ 1) (atom g gN gL) ≡ atom (t g) (tN g gN dg) (tL g gN dg gL)
  atom-tgt g gN gL dg = ≡-cell K L
    (trans (cong (tgtT (ADC.𝕄 K) (deg g ∸ 1)) (atomT≡ (ent g) 0))
      (trans (tgt-tab (deg g ∸ 1) 0 (ent g))
        (trans (tabE (tgtF ((deg g ∸ 1) + 0) (ent g)) (ent (t g)) 0 pt) (sym (atomT≡ (ent (t g)) 0)))))
    where
    pt : ∀ j → 0 ≤ j → tgtF ((deg g ∸ 1) + 0) (ent g) j ≡ ent (t g) j
    pt j _ rewrite +-zero (deg g ∸ 1) = tgt-row g gN dg j

  ----------------------------------------------------------------------
  -- Freeness on the globular set Γ.

  G : Set
  G = AtomG B H L

  degG : G → Nat
  degG (i , _ , _) = deg i

  sG tG : (g : G) → 1 ≤ degG g → G
  sG (i , iN , iL) dg = s i , sN i iN dg , sL i iN dg iL
  tG (i , iN , iL) dg = t i , tN i iN dg , tL i iN dg iL

  private
    one? : ∀ d → (d ≡ 0) ⊎ (1 ≤ d)
    one? zero    = inj₁ refl
    one? (suc d) = inj₂ (s≤s z≤n)

    wd : Sd → (g : G) → (degG g ≡ 0) ⊎ (1 ≤ degG g) → Expr G
    wd σ  g (inj₁ _)  = gen g
    wd σ⁻ g (inj₂ dg) = gen (sG g dg)
    wd σ⁺ g (inj₂ dg) = gen (tG g dg)

    ¬1≤0 : ∀ {d} → d ≡ 0 → 1 ≤ d → ⊥
    ¬1≤0 refl ()

  -- The attaching words: single generators.
  W : Sd → G → Expr G
  W σ g = wd σ g (one? (degG g))

  open Syn degG W

  W-co : ∀ σ g → CO (W σ g)
  W-co σ g with one? (degG g)
  W-co σ  g | inj₁ _  = co-gen g
  W-co σ⁻ g | inj₂ dg = co-gen (sG g dg)
  W-co σ⁺ g | inj₂ dg = co-gen (tG g dg)

  W-deg : ∀ σ g → DegLe (degG g ∸ 1) (W σ g)
  W-deg σ g with one? (degG g)
  W-deg σ  (i , iN , iL) | inj₁ e  = dl-gen (≤-of (trans e (cong (_∸ 1) (sym e))))
  W-deg σ⁻ (i , iN , iL) | inj₂ dg = dl-gen (≤-of (ds i iN dg))
  W-deg σ⁺ (i , iN , iL) | inj₂ dg = dl-gen (≤-of (dt i iN dg))

  module Free (𝒟 : ωCat) (κ : G → ωCat.C 𝒟)
              (dimκ : ∀ g → ωCat.src 𝒟 (degG g) (κ g) ≡ κ g)
              (κs : ∀ g (dg : 1 ≤ degG g) → ωCat.src 𝒟 (degG g ∸ 1) (κ g) ≡ κ (sG g dg))
              (κt : ∀ g (dg : 1 ≤ degG g) → ωCat.tgt 𝒟 (degG g ∸ 1) (κ g) ≡ κ (tG g dg)) where
    private
      module Eν = Eval (nu K L) (ιν B H L)
      module ED = Eval 𝒟 κ

      W-evν : ∀ σ g → 1 ≤ degG g → Eν.Ev (W σ g) (Sem.bdC (nu K L) (ιν B H L) σ (degG g ∸ 1) (ιν B H L g))
      W-evν σ g d1 with one? (degG g)
      W-evν σ  g d1 | inj₁ e = ⊥-elim (¬1≤0 e d1)
      W-evν σ⁻ (i , iN , iL) d1 | inj₂ dg = subst (Eν.Ev (gen (sG (i , iN , iL) dg))) (sym (atom-src i iN iL dg)) (Eν.ev-gen _)
      W-evν σ⁺ (i , iN , iL) d1 | inj₂ dg = subst (Eν.Ev (gen (tG (i , iN , iL) dg))) (sym (atom-tgt i iN iL dg)) (Eν.ev-gen _)

      W-evD : ∀ σ g → 1 ≤ degG g → ED.Ev (W σ g) (Sem.bdC 𝒟 κ σ (degG g ∸ 1) (κ g))
      W-evD σ g d1 with one? (degG g)
      W-evD σ  g d1 | inj₁ e = ⊥-elim (¬1≤0 e d1)
      W-evD σ⁻ g d1 | inj₂ dg = subst (ED.Ev (gen (sG g dg))) (sym (κs g dg)) (ED.ev-gen _)
      W-evD σ⁺ g d1 | inj₂ dg = subst (ED.Ev (gen (tG g dg))) (sym (κt g dg)) (ED.ev-gen _)

      module LH = LF.Lift.Hyps B H L 𝒟 κ W W-co W-deg W-evν dimκ W-evD

    -- A map of globular sets Γ → 𝒟 extends to a strict functor ν(λΓ) → 𝒟 ...
    functor : Functor (nu K L) 𝒟
    functor = LH.functor

    functor-gen : ∀ g → Functor.F functor (ιν B H L g) ≡ κ g
    functor-gen = LH.functor-gen

  -- ... and uniquely: strict functors that agree on the atoms agree.
  unique : ∀ {𝒞 : ωCat} (Φ Ψ : Functor (nu K L) 𝒞) →
           (∀ g → Functor.F Φ (ιν B H L g) ≡ Functor.F Ψ (ιν B H L g)) → ∀ x → Functor.F Φ x ≡ Functor.F Ψ x
  unique {𝒞} Φ Ψ h = uniqueness (toGen Φ) (toGen Ψ) (λ i iN iL → h (i , iN , iL))
    where
    toGen : Functor (nu K L) 𝒞 → Gen.Functor B H L 𝒞
    toGen Φ = record { F = Functor.F Φ ; F-src = Functor.F-src Φ ; F-tgt = Functor.F-tgt Φ ; F-comp = Functor.F-comp Φ }

------------------------------------------------------------------------
-- Example: the 2-globe α : f ⇒ g : x → y (listed x, f, α, g, y). A
-- strict functor out of ν(λD²) is a 2-cell of the target with its
-- boundary, and every such 2-cell gives one.

module D² where
  open import CaTTExp.Strict.BasisCheck using (BD²; hyp-D²)

  s₂ t₂ : Nat → Nat
  s₂ 1 = 0
  s₂ 2 = 1
  s₂ 3 = 0
  s₂ _ = 0
  t₂ 1 = 4
  t₂ 2 = 3
  t₂ 3 = 4
  t₂ _ = 0

  private
    D = Atom.deg BD²

  bm₂ : ∀ i → i < 5 → 1 ≤ D i → at 0c (Basis.bminus BD²) i ≡ unit (s₂ i)
  bm₂ 1 _ _ = refl
  bm₂ 2 _ _ = refl
  bm₂ 3 _ _ = refl
  bm₂ 0 _ ()
  bm₂ 4 _ ()
  bm₂ (suc (suc (suc (suc (suc i))))) (s≤s (s≤s (s≤s (s≤s (s≤s ()))))) _

  bp₂ : ∀ i → i < 5 → 1 ≤ D i → at 0c (Basis.bplus BD²) i ≡ unit (t₂ i)
  bp₂ 1 _ _ = refl
  bp₂ 2 _ _ = refl
  bp₂ 3 _ _ = refl
  bp₂ 0 _ ()
  bp₂ 4 _ ()
  bp₂ (suc (suc (suc (suc (suc i))))) (s≤s (s≤s (s≤s (s≤s (s≤s ()))))) _

  sN₂ : ∀ i → i < 5 → 1 ≤ D i → s₂ i < 5
  sN₂ 1 _ _ = s≤s z≤n
  sN₂ 2 _ _ = s≤s (s≤s z≤n)
  sN₂ 3 _ _ = s≤s z≤n
  sN₂ 0 _ ()
  sN₂ 4 _ ()
  sN₂ (suc (suc (suc (suc (suc i))))) (s≤s (s≤s (s≤s (s≤s (s≤s ()))))) _

  tN₂ : ∀ i → i < 5 → 1 ≤ D i → t₂ i < 5
  tN₂ 1 _ _ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
  tN₂ 2 _ _ = s≤s (s≤s (s≤s (s≤s z≤n)))
  tN₂ 3 _ _ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
  tN₂ 0 _ ()
  tN₂ 4 _ ()
  tN₂ (suc (suc (suc (suc (suc i))))) (s≤s (s≤s (s≤s (s≤s (s≤s ()))))) _

  ds₂ : ∀ i → i < 5 → 1 ≤ D i → D (s₂ i) ≡ D i ∸ 1
  ds₂ 1 _ _ = refl
  ds₂ 2 _ _ = refl
  ds₂ 3 _ _ = refl
  ds₂ 0 _ ()
  ds₂ 4 _ ()
  ds₂ (suc (suc (suc (suc (suc i))))) (s≤s (s≤s (s≤s (s≤s (s≤s ()))))) _

  dt₂ : ∀ i → i < 5 → 1 ≤ D i → D (t₂ i) ≡ D i ∸ 1
  dt₂ 1 _ _ = refl
  dt₂ 2 _ _ = refl
  dt₂ 3 _ _ = refl
  dt₂ 0 _ ()
  dt₂ 4 _ ()
  dt₂ (suc (suc (suc (suc (suc i))))) (s≤s (s≤s (s≤s (s≤s (s≤s ()))))) _

  open Glob BD² hyp-D² 2 s₂ t₂ bm₂ bp₂ sN₂ tN₂ ds₂ dt₂ public
