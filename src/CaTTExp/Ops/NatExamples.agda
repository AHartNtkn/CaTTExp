------------------------------------------------------------------------
-- Examples for the recursor (CaTTExp.Ops.Nat). Each positive example
-- is `from-just (check Γ t A)`, so it typechecks only if the certified
-- checker accepts t at exactly A.
------------------------------------------------------------------------
module CaTTExp.Ops.NatExamples where

open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Ops.Nat

open Signature ℕsig using (Ctx; Ty; Tm; ε; _▸_; ⋆; arr; coh)

-- Identities and the two unit coherences, as plain CaTT coherences.
D₀ D₁ : Ctx
D₀ = ε ▸ ⋆
D₁ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1)

idc : Tm → Tm
idc x = coh D₀ (arr ⋆ (v 0) (v 0)) ⟪ x ∷ [] ⟫

-- f ; 1 ⇒ f
runit : Tm → Tm → Tm → Tm
runit x y g = coh D₁ (arr (arr ⋆ (v 0) (v 1)) (comp (v 0) (v 1) (v 2) (v 1) (idc (v 1))) (v 2))
                 ⟪ x ∷ y ∷ g ∷ [] ⟫

-- f ; 1 ⇒ 1 ; f
swapU : Tm → Tm → Tm → Tm
swapU x y g = coh D₁ (arr (arr ⋆ (v 0) (v 1)) (comp (v 0) (v 1) (v 2) (v 1) (idc (v 1)))
                                             (comp (v 0) (v 0) (idc (v 0)) (v 1) (v 2)))
                 ⟪ x ∷ y ∷ g ∷ [] ⟫

------------------------------------------------------------------------
-- 1. In the empty context: doubling, rec(zero, succ ; succ) : N → N.

ss : Tm
ss = comp N N S N S

double : ε ⊢tm rec N Z ss ∶ arr ⋆ N N
double = from-just (check ε _ _)

double-Z : ε ⊢tm recZ N Z ss ∶ arr (arr ⋆ 𝟙 N) (comp 𝟙 N Z N (rec N Z ss)) Z
double-Z = from-just (check ε _ _)

double-S : ε ⊢tm recS N Z ss ∶ arr (arr ⋆ N N) (comp N N S N (rec N Z ss)) (comp N N (rec N Z ss) N ss)
double-S = from-just (check ε _ _)

------------------------------------------------------------------------
-- 2. Over a parameter context: any B with b : ⊤ → B, g : B → B.

P : Ctx
P = ε ▸ ⋆ ▸ arr ⋆ 𝟙 (v 0) ▸ arr ⋆ (v 0) (v 0)

iter : P ⊢tm rec (v 0) (v 1) (v 2) ∶ arr ⋆ N (v 0)
iter = from-just (check P _ _)

-- Parameters that are themselves composites: iterate g ; g from b.
iter₂ : P ⊢tm rec (v 0) (v 1) (comp (v 0) (v 0) (v 2) (v 0) (v 2)) ∶ arr ⋆ N (v 0)
iter₂ = from-just (check P _ _)

------------------------------------------------------------------------
-- 3. η for N: the identity N → N satisfies the recursion equations of
-- rec(zero, succ), so uniqueness gives a cell 1_N ⇒ rec(zero, succ).

η-N : ε ⊢tm uniq N Z S (idc N) (runit 𝟙 N Z) (swapU N N S) ∶ arr (arr ⋆ N N) (idc N) (rec N Z S)
η-N = from-just (check ε _ _)

------------------------------------------------------------------------
-- Negatives.

-- f must be an endomap of A.
_ : is-just (infer ε (rec N Z Z)) ≡ false
_ = refl

-- The base point must be an element of A.
_ : is-just (infer P (rec (v 0) Z (v 2))) ≡ false
_ = refl

-- Uniqueness needs both recursion cells (swapping their roles fails).
_ : is-just (infer ε (uniq N Z S (idc N) (swapU N N S) (runit 𝟙 N Z))) ≡ false
_ = refl
