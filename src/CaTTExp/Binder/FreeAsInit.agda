------------------------------------------------------------------------
-- The free object as an INIT instance (ledger S37(g), U4.2 of
-- notes/unified-engine.md; S23 by definition).
--
-- ⟦Γ⟧ := μ(Δ_Γ), where Δ_Γ is "X with Γ placed in 𝒦(⊤, X)": a sort
-- X : ⋆ and, for each entry j of Γ, the suspension of its type with the
-- suspension's two objects sent to ⊤ and X and the earlier entries to
-- the earlier generators:
--
--   Δ_Γ = (X : ⋆, e_0 : (ΣA_0)[⊤, X], …, e_j : (ΣA_j)[⊤, X, e_0, …, e_{j−1}], …)
--
-- This is the type pattern of `GenHeads`' η_{Γ,j} with X in place of
-- ⟦Γ⟧. Then INIT's own formers (CaTTExp.Binder.Init) give everything
-- chapter 7 asks of the free object:
--
--   ⟦Γ⟧        = μ_0(Δ_Γ)                      (FREE)
--   η_{Γ,j}    = η_{j+1}(Δ_Γ)                  (GEN)
--   ⟨σ⟩, β_σ   = rec_0, rec_y at a model σ     (LIFT₀)
--   ⟨θ⟩        = uni_0, uni_y                  (LIFT₁)
--
-- with INIT's limits: rec_y needs the entries up to y "good" (every
-- touched coherence in their boundaries of dimension 1) and uni_y needs
-- y a map (ledger C1d (2)). Marks on Γ's entries are INIT's marks (an
-- inv generator is an entry marked inv), which `GenHeads` does not have
-- (ledger S26l).
--
-- Checked here (`refl`, with the certified checker and plain CaTT's
-- side condition), in `InitExamples`' signature (⊤ a base constant):
--   * Δ_{D¹} is the expected telescope, and μ, η_f, rec, rec_f, uni and
--     uni_x are typed; uni_f (a 2-cell) is rejected (C1d (2));
--   * for Γ with α : f ; g ⇒ h, μ, η_α and rec are typed, rec_α is
--     rejected (its boundary is a 2-dimensional coherence: C1d (2));
--   * the walking isomorphism (f marked inv) is accepted.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Init
open import CaTTExp.Binder.InitExamples using (𝕊; X; one; tyOf; ok; sideOf; NK)
open import CaTTExp.Binder.Signature
open import CaTTExp.Suspension P.∅ using (Σty)
open import CaTTExp.Examples using (Comp₂; comp)

module CaTTExp.Binder.FreeAsInit where

open Signature 𝕊
open import CaTTExp.Binder.Typing 𝕊
open import CaTTExp.Binder.CheckWith 𝕊 cattSide varMark
open import CaTTExp.Binder.LimHeads using (module PureEmb)
open PureEmb NK Former
open import CaTTExp.Binder.Close NK Former using (clTel)

------------------------------------------------------------------------
-- Δ_Γ, written with free variables (X = var 0, e_i = var (i + 1)) and
-- then closed into a telescope.

-- (⊤, X, e_0, …, e_{j−1}) for ΣΓ's first 2 + j entries.
genArgs : Nat → Sub
genArgs j = (⟨⟩ ,ₛ one ,ₛ var 0) ++′ j
  where
  _++′_ : Sub → Nat → Sub
  σ ++′ zero    = σ
  σ ++′ (suc k) = (σ ++′ k) ,ₛ var (suc k)

-- Every entry is unmarked; `marked` below adds marks.
ΞΓ : P.Ctx → Ctx
ΞΓ P.ε       = ε ▸ ⋆
ΞΓ (Γ P.▸ A) = ΞΓ Γ ▸ peTy (Σty A) [ genArgs (P.len Γ) ]ty

ΔΓ : P.Ctx → Ctx
ΔΓ Γ = clTel 0 (ΞΓ Γ)

------------------------------------------------------------------------
-- D¹.

pv : Nat → P.Tm
pv = P.var

b : Nat → Tm
b = bvar 0

el : Ty
el = arr ⋆ one X

D1 : P.Ctx
D1 = P.ε P.▸ P.⋆ P.▸ P.⋆ P.▸ P.arr P.⋆ (pv 0) (pv 1)

-- ⟦D¹⟧ = μ(X, e_x, e_y : ⊤ → X, e_f : e_x ⇒ e_y).
d1-tel : ΔΓ D1 ≡ (ε ▸ ⋆ ▸ el ▸ el ▸ arr el (b 1) (b 2))
d1-tel = refl

-- A model in C: c, c′ : ⊤ → C and φ : c ⇒ c′, i.e. a diagram D¹ ⇒ C.
Γm : Ctx
Γm = ε ▸ ⋆ ▸ arr ⋆ one (var 0) ▸ arr ⋆ one (var 0) ▸ arr (arr ⋆ one (var 0)) (var 1) (var 2)

μD1 : Tm
μD1 = bnd μ 0 (ΔΓ D1) ⟨⟩

d1-free : tyOf ε μD1 ≡ just ⋆
d1-free = refl

d1-gen : tyOf ε (bnd η 3 (ΔΓ D1) ⟨⟩)
       ≡ just (arr (arr ⋆ one μD1) (bnd η 1 (ΔΓ D1) ⟨⟩) (bnd η 2 (ΔΓ D1) ⟨⟩))
d1-gen = refl

-- LIFT₀: ⟨σ⟩ : ⟦D¹⟧ → C, and the comparison at f.
d1-lift0 : tyOf Γm (bnd rec 0 (ΔΓ D1) (fresh 0 4)) ≡ just (arr ⋆ μD1 (var 0))
d1-lift0 = refl

-- (rec_f, uni_0, uni_x, uni_f): uni_f is a 2-cell's cylinder (C1d (2)).
d1-rest : ( ok (tyOf Γm (bnd recY 3 (ΔΓ D1) (fresh 0 4)))
          ∷ sideOf uni 0 (ΔΓ D1) ∷ sideOf uniY 1 (ΔΓ D1) ∷ sideOf uniY 3 (ΔΓ D1) ∷ [])
        ≡ (true ∷ true ∷ true ∷ false ∷ [])
d1-rest = refl

------------------------------------------------------------------------
-- A 2-cell whose source is a composite: α : f ; g ⇒ h.

Γc : P.Ctx
Γc = Comp₂ P.▸ P.arr P.⋆ (pv 0) (pv 3)
           P.▸ P.arr (P.arr P.⋆ (pv 0) (pv 3)) (comp (pv 0) (pv 1) (pv 2) (pv 3) (pv 4)) (pv 5)

comp-case : ( ok (tyOf ε (bnd μ 0 (ΔΓ Γc) ⟨⟩)) ∷ ok (tyOf ε (bnd η 7 (ΔΓ Γc) ⟨⟩))
            ∷ sideOf rec 0 (ΔΓ Γc) ∷ sideOf recY 7 (ΔΓ Γc) ∷ [])
          ≡ (true ∷ true ∷ true ∷ false ∷ [])
comp-case = refl

------------------------------------------------------------------------
-- Marks: the walking isomorphism, f marked inv.

arrowInv : Ctx
arrowInv = ε ▸ ⋆ ▸ el ▸ el ▸[ minv ∷ [] ] arr el (b 1) (b 2)

inv-case : ( ok (tyOf ε (bnd μ 0 arrowInv ⟨⟩)) ∷ ok (tyOf ε (bnd η 3 arrowInv ⟨⟩)) ∷ [])
         ≡ (true ∷ true ∷ [])
inv-case = refl
