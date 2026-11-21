------------------------------------------------------------------------
-- The kernel's typing rules and certified checker for (coh_S), over
-- any decision procedure for the side condition
-- (spec/02-lax-core.md §2.3; ledger S3a, S3b).
--
-- CaTTExp.Uniform.Kernel takes a length bound (`Graded`) for each
-- layer and decides SC with Rule.Decide. Layers with loops have no such
-- bound (CaTTExp.Uniform.RuleFin, header). This module takes instead,
-- for each Δ, A, a decision of SC between any two cells, which
-- Rule.Decide (from a bound) and RuleFin.DecideFin (from finite closed
-- universes) both provide. Kernel is this module at Rule.Decide.sc?.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Join.Quiver using (Dec; yes; no)
open import CaTTExp.Uniform.Rule

module CaTTExp.Uniform.KernelDec
  (𝕊      : Signature)
  (layer  : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Layer)
  (sc?    : ∀ Δ A (x y : Layer.Cell (layer Δ A)) → Dec (SC (layer Δ A) x y))
  (⟦_⟧    : ∀ Δ A → Signature.Tm 𝕊 → Maybe (Layer.Cell (layer Δ A)))
  where

open Signature 𝕊

private
  ⌊_⌋ : ∀ {P : Set} → Dec P → Bool
  ⌊ yes _ ⌋ = true
  ⌊ no _  ⌋ = false

  sideM : ∀ Δ A → Maybe (Layer.Cell (layer Δ A)) → Maybe (Layer.Cell (layer Δ A)) → Bool
  sideM Δ A (just x) (just y) = ⌊ sc? Δ A x y ⌋
  sideM Δ A _        _        = false

side : Ctx → Ty → Tm → Tm → Bool
side Δ A t u = sideM Δ A (⟦ Δ ⟧ A t) (⟦ Δ ⟧ A u)

-- The side condition as a proposition.
SCΔ : Ctx → Ty → Tm → Tm → Set
SCΔ Δ A t u = Σ (Layer.Cell (layer Δ A)) λ x → Σ (Layer.Cell (layer Δ A)) λ y →
              (⟦ Δ ⟧ A t ≡ just x) × (⟦ Δ ⟧ A u ≡ just y) × SC (layer Δ A) x y

side-sound : ∀ Δ A t u → T (side Δ A t u) → SCΔ Δ A t u
side-sound Δ A t u s with ⟦ Δ ⟧ A t | ⟦ Δ ⟧ A u
... | just x | just y with sc? Δ A x y
...   | yes p = x , y , refl , refl , p

side-complete : ∀ Δ A t u → SCΔ Δ A t u → T (side Δ A t u)
side-complete Δ A t u (x , y , ex , ey , s) rewrite ex | ey with sc? Δ A x y
... | yes _ = tt
... | no ¬s = ¬s s

-- The kernel's judgments; their coh rule is (coh_S).
open import CaTTExp.TypingWith 𝕊 side public

coh-S : ∀ {Γ Δ A t u σ} →
        Δ ⊢ps → Δ ⊢ctx → Δ ⊢ty arr A t u →
        SCΔ Δ A t u →
        Γ ⊢sub σ ∶ Δ →
        Γ ⊢tm coh Δ (arr A t u) σ ∶ (arr A t u) [ σ ]ty
coh-S {Δ = Δ} {A} {t} {u} p w a sc s = coh-wf p w a (side-complete Δ A t u sc) s

-- Inversion: a derived coherence satisfies the side condition.
coh-S⁻¹ : ∀ {Γ Δ A t u σ B} → Γ ⊢tm coh Δ (arr A t u) σ ∶ B → SCΔ Δ A t u
coh-S⁻¹ {Δ = Δ} {A} {t} {u} (coh-wf _ _ _ s _) = side-sound Δ A t u s

-- The certified checker: every success carries a derivation.
module Checker where
  open import CaTTExp.CheckWith 𝕊 side public

-- And it is complete (CaTTExp.Completeness), under that module's two
-- hypotheses on the signature of constants.
module CheckerComplete
  (==K-refl : ∀ k → T (k ==K k))
  (valid?-complete : ∀ k → Valid k → T (is-just (valid? k))) where
  open import CaTTExp.Completeness 𝕊 side ==K-refl valid?-complete public
