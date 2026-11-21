------------------------------------------------------------------------
-- The kernel's typing rules and certified checker, with the uniform
-- side condition (coh_S) of spec/02-lax-core.md §2.3 (ledger S3).
--
-- Parameters: for every pasting context Δ and type A,
--   layer Δ A    the layer of F_{V+S}(Δ) holding the strict images of
--                terms of type A, with the letters one dimension up;
--   graded Δ A   a bound on the length of paths in that layer;
--   ⟦_⟧ Δ A      the strict interpretation of terms (partial: it may
--                fail on ill-typed input).
--
-- The side condition is then
--
--   side Δ A t u = true  ⟺  ⟦t⟧ = just x, ⟦u⟧ = just y, and SC x y
--
-- (side-sound, side-complete), with SC as in CaTTExp.Uniform.Rule:
-- a path of letters from x to y whose support is full. The typing
-- rules are CaTTExp.TypingWith at this side condition, whose coh rule
-- is then exactly (coh_S); the checker is CaTTExp.CheckWith, sound by
-- construction and complete by CaTTExp.Completeness.
--
-- This module does not construct the layers of F_{V+S}: it is the
-- kernel checker relative to them. CaTTExp.Uniform.Grid constructs
-- the layer in which the switch laws act (degree four, suspended
-- grids), for every setting S.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Uniform.Rule

module CaTTExp.Uniform.Kernel
  (𝕊      : Signature)
  (layer  : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Layer)
  (graded : ∀ Δ A → Graded (layer Δ A))
  (⟦_⟧    : ∀ Δ A → Signature.Tm 𝕊 → Maybe (Layer.Cell (layer Δ A)))
  where

open Signature 𝕊

private
  sideM : ∀ Δ A → Maybe (Layer.Cell (layer Δ A)) → Maybe (Layer.Cell (layer Δ A)) → Bool
  sideM Δ A (just x) (just y) = Decide.⌊sc⌋ (layer Δ A) (graded Δ A) x y
  sideM Δ A _        _        = false

side : Ctx → Ty → Tm → Tm → Bool
side Δ A t u = sideM Δ A (⟦ Δ ⟧ A t) (⟦ Δ ⟧ A u)

-- The side condition as a proposition.
SCΔ : Ctx → Ty → Tm → Tm → Set
SCΔ Δ A t u = Σ (Layer.Cell (layer Δ A)) λ x → Σ (Layer.Cell (layer Δ A)) λ y →
              (⟦ Δ ⟧ A t ≡ just x) × (⟦ Δ ⟧ A u ≡ just y) × SC (layer Δ A) x y

side-sound : ∀ Δ A t u → T (side Δ A t u) → SCΔ Δ A t u
side-sound Δ A t u s with ⟦ Δ ⟧ A t | ⟦ Δ ⟧ A u
... | just x | just y = x , y , refl , refl , Decide.⌊sc⌋-sound (layer Δ A) (graded Δ A) x y s

side-complete : ∀ Δ A t u → SCΔ Δ A t u → T (side Δ A t u)
side-complete Δ A t u (x , y , ex , ey , s) rewrite ex | ey =
  Decide.⌊sc⌋-complete (layer Δ A) (graded Δ A) x y s

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
