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

module Lift {N : Nat} (B : Basis N) (H : Hyp B) (L : Nat)
            (𝒟 : ωCat) (κ : AtomG B H L → ωCat.C 𝒟)
            (W : Sd → AtomG B H L → Expr (AtomG B H L)) where
  open Basis B
  open Hyp H
  open Atom B
  open Gen B H L hiding (W)
  open Rows B H L
  open TabAt (ADC.𝕄 K)

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
