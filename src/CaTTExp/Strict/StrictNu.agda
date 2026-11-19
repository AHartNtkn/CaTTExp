------------------------------------------------------------------------
-- The strict model of L lands in strict ω-categories (ledger A5, N3).
--
-- Strict.Soundness proves that every derivable t : arr A s u over a
-- pasting context Γ is a tower cell of K(Γ)(x, y) (`sound-tm`), where
-- x, y are the endpoints of A. Strict.TowerNu reads tower cells as
-- cells of the strict ω-category `nu K L` of Strict.Nu, the input of
-- `OmegaSound.sound-in`. Here the two meet:
--
--   * `KΓ Γ x y : ADC` is K(Γ)(x, y) on sorted bags, with the decidable
--     basis test `isBasis Γ x y` (Basis → T isBasis is `basis→`);
--   * `term-cell`: every derivable t : arr A s u over a pasting context
--     gives, for every L ≥ dim A, a cell of `nu (KΓ Γ x y) L`, namely
--     `tabOf L (towerOf t (arr A s u))`.
------------------------------------------------------------------------
module CaTTExp.Strict.StrictNu where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Soundness using (module Soundness)
open import CaTTExp.Strict.SortBag using (module BagADC)
open import CaTTExp.Strict.Omega using (_≤_)
open import CaTTExp.Strict.TowerNu using (module TowerNu)
open import CaTTExp.Gray.Pure hiding (Tuple)
import CaTTExp.Strict.Nu as Nu

------------------------------------------------------------------------
-- A decidable basis test.

private
  ∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-intro {true} _ q = q

  ==T : ∀ n → T (n ==ℕ n)
  ==T n = subst T (sym (==-true n)) tt

mutual
  isWFT : Ctx → Nat → Nat → Tuple → Bool
  isWFT Γ x y []      = x ==ℕ y
  isWFT Γ x y (v ∷ w) = wftStep Γ x y w (endsL (lookup Γ v))

  wftStep : Ctx → Nat → Nat → Tuple → Maybe (Nat × Nat) → Bool
  wftStep Γ x y w nothing        = false
  wftStep Γ x y w (just (a , z)) = (x ==ℕ a) ∧ isWFT Γ z y w

wft→ : ∀ Γ x y w → WFT Γ x y w → T (isWFT Γ x y w)
wft→ Γ x y []      refl          = ==T x
wft→ Γ x y (v ∷ w) (z , e , p) rewrite e = ∧-intro (==T x) (wft→ Γ z y w p)

isBasis : Ctx → Nat → Nat → Nat → Tuple → Bool
isBasis Γ x y k w = isWFT Γ x y w ∧ (deg Γ w ==ℕ k)

basis→ : ∀ Γ x y k w → Basis Γ x y k w → T (isBasis Γ x y k w)
basis→ Γ x y k w (p , refl) = ∧-intro (wft→ Γ x y w p) (==T (deg Γ w))

------------------------------------------------------------------------
-- K(Γ)(x, y) as an augmented directed complex, and the cells of L in it.

KΓ : Ctx → Nat → Nat → Nu.ADC
KΓ Γ x y = BagADC.adc (∂T Γ) (isBasis Γ x y)

module _ (Γ : Ctx) (x y : Nat) where
  open TowerNu (∂T Γ) (isBasis Γ x y) (Basis Γ x y) (basis→ Γ x y) public
    using (tabOf; cell→)

-- Every derivable t : arr A s u over a pasting context is, for every
-- L ≥ dim A, a cell of the strict ω-category ν(K(Γ)(x, y)) truncated at L.
term-cell : ∀ {Γ t A s u} → PsInv Γ → Γ ⊢tm t ∶ arr A s u → ∀ L → dim A ≤ L →
            Σ (Nat × Nat) λ e → (endsV (arr A s u) ≡ just e) ×
              Nu.IsCell (KΓ Γ (fst e) (snd e)) L (tabOf Γ (fst e) (snd e) L (towerOf t (arr A s u)))
term-cell {Γ} {t} {A} {s} {u} inv dt L dL =
  let (e , ee , _ , _ , c) = Soundness.sound-tm inv dt
  in e , ee , cell→ Γ (fst e) (snd e) L (dim A) (towerOf t (arr A s u)) dL c

term-cellν : ∀ {Γ t A s u} → PsInv Γ → Γ ⊢tm t ∶ arr A s u → ∀ L → dim A ≤ L →
             Σ (Nat × Nat) λ e → (endsV (arr A s u) ≡ just e) × Nu.Cell (KΓ Γ (fst e) (snd e)) L
term-cellν inv dt L dL =
  let (e , ee , c) = term-cell inv dt L dL in e , ee , (_ , c)
