------------------------------------------------------------------------
-- Ledger item A4: functoriality of ⟦_⟧ is NOT derivable in the sketch
-- of CaTTExp.Sketch.Representables. This replaces the informal argument
-- of notes/agda-sketch-findings.md (finding 2) by a proof.
--
-- The separating model is B(ℤ/2) (CaTTExp.GroupModel): one object,
-- the group ℤ/2 = (Bool, xor) as 1-cells, identities above. Every ⟦Γ⟧
-- goes to the object and every ⟦σ⟧ to the non-identity element.
-- Soundness says a 2-cell f ⇒ g forces ⟦f⟧ = ⟦g⟧ in ℤ/2, but
--   ⟦s⟧ ; ⟦id⟧ ↦ 1 + 1 = 0     while    ⟦s⟧ ↦ 1,
--   ⟦id_Γ⟧ ↦ 1                 while    id(⟦Γ⟧) ↦ 0,
--   ⟦σ ∘ τ⟧ ↦ 1                while    ⟦σ⟧ ; ⟦τ⟧ ↦ 0.
-- So no term, in the empty context or in any context with a valid
-- environment in B(ℤ/2), has any of these types, in either direction.
------------------------------------------------------------------------
module CaTTExp.Sketch.NonDerivable where

open import CaTTExp.Prelude
open import CaTTExp.Signature
import CaTTExp.Pure as P
import CaTTExp.Examples as PE
open import CaTTExp.Sketch.Representables

open Signature 𝔸
open import CaTTExp.Typing 𝔸
open import CaTTExp.Subst 𝔸 cattSide using (Closed)
open import CaTTExp.GroupModel 𝔸

------------------------------------------------------------------------
-- The group ℤ/2.

private
  xor : Bool → Bool → Bool
  xor true  b = not b
  xor false b = b

ℤ₂ : Group
ℤ₂ = record
  { G = Bool ; _·_ = xor ; e = false ; _⁻¹ = λ b → b
  ; assoc = λ { true true true → refl ; true true false → refl
              ; true false c → refl ; false b c → refl }
  ; idˡ = λ _ → refl
  ; idʳ = λ { true → refl ; false → refl }
  ; invˡ = λ { true → refl ; false → refl }
  ; invʳ = λ { true → refl ; false → refl }
  }

------------------------------------------------------------------------
-- The interpretation of the constants.

M : AmbK → Bool
M (rep _)     = false
M (fun _ _ _) = true

closedA : Closed
closedA (rep _)     = tt
closedA (fun _ _ _) = tt , tt , tt

open Model closedA ℤ₂ M using (ValidEnv; module Sound)
open Sound (λ { (rep _) _ _ → tt ; (fun _ _ _) _ _ → tt })

------------------------------------------------------------------------
-- The three non-derivability results. Each is stated for an arbitrary
-- context Γ that has a valid environment in B(ℤ/2) (for instance the
-- empty context, or any context without 2-cell variables), and for
-- both orientations.

private
  absurd : false ≡ true → ⊥
  absurd ()

  absurd′ : true ≡ false → ⊥
  absurd′ ()

-- 1. ⟦s⟧ ; ⟦id_{D₁}⟧ and ⟦s⟧ are not related by any cell.
no-unitor : ∀ {Γ ρ s} → ValidEnv Γ ρ →
            Γ ⊢tm s ∶ arr (arr ⋆ ⟦ PE.D₀ ⟧ ⟦ PE.D₁ ⟧) s⨾id ⟦s⟧ → ⊥
no-unitor V d = absurd (sound d V)

no-unitor⁻¹ : ∀ {Γ ρ s} → ValidEnv Γ ρ →
              Γ ⊢tm s ∶ arr (arr ⋆ ⟦ PE.D₀ ⟧ ⟦ PE.D₁ ⟧) ⟦s⟧ s⨾id → ⊥
no-unitor⁻¹ V d = absurd′ (sound d V)

-- 2. ⟦id_Γ⟧ and the ambient identity on ⟦Γ⟧ are not related.
idᴬ : Tm → Tm
idᴬ x = coh D₀ᴬ (arr ⋆ (var 0) (var 0)) (⟨⟩ ,ₛ x)

⟦id⟧ : P.Ctx → Tm
⟦id⟧ Γ = cst (fun Γ Γ (P.idₛ Γ))

no-id : ∀ {Γ ρ s} Θ → ValidEnv Γ ρ →
        Γ ⊢tm s ∶ arr (arr ⋆ ⟦ Θ ⟧ ⟦ Θ ⟧) (⟦id⟧ Θ) (idᴬ ⟦ Θ ⟧) → ⊥
no-id Θ V d = absurd′ (sound d V)

no-id⁻¹ : ∀ {Γ ρ s} Θ → ValidEnv Γ ρ →
          Γ ⊢tm s ∶ arr (arr ⋆ ⟦ Θ ⟧ ⟦ Θ ⟧) (idᴬ ⟦ Θ ⟧) (⟦id⟧ Θ) → ⊥
no-id⁻¹ Θ V d = absurd (sound d V)

-- 3. ⟦σ ∘ τ⟧ and ⟦σ⟧ ; ⟦τ⟧ are not related. Here Δ ⊢ σ : Γ₁ and
-- Θ ⊢ τ : Δ, so ⟦σ⟧ : ⟦Γ₁⟧ → ⟦Δ⟧, ⟦τ⟧ : ⟦Δ⟧ → ⟦Θ⟧ and
-- ⟦σ ∘ τ⟧ : ⟦Γ₁⟧ → ⟦Θ⟧.
no-comp : ∀ {Γ ρ s} Γ₁ Δ Θ σ τ → ValidEnv Γ ρ →
          Γ ⊢tm s ∶ arr (arr ⋆ ⟦ Γ₁ ⟧ ⟦ Θ ⟧)
                       (cst (fun Γ₁ Θ (σ P.∘ τ)))
                       (cst (fun Γ₁ Δ σ) ⨾ cst (fun Δ Θ τ) [ ⟦ Γ₁ ⟧ , ⟦ Δ ⟧ , ⟦ Θ ⟧ ]) → ⊥
no-comp Γ₁ Δ Θ σ τ V d = absurd′ (sound d V)

no-comp⁻¹ : ∀ {Γ ρ s} Γ₁ Δ Θ σ τ → ValidEnv Γ ρ →
            Γ ⊢tm s ∶ arr (arr ⋆ ⟦ Γ₁ ⟧ ⟦ Θ ⟧)
                         (cst (fun Γ₁ Δ σ) ⨾ cst (fun Δ Θ τ) [ ⟦ Γ₁ ⟧ , ⟦ Δ ⟧ , ⟦ Θ ⟧ ])
                         (cst (fun Γ₁ Θ (σ P.∘ τ))) → ⊥
no-comp⁻¹ Γ₁ Δ Θ σ τ V d = absurd (sound d V)

-- In particular, in the empty context.
no-unitor-closed : ∀ {s} → ε ⊢tm s ∶ arr (arr ⋆ ⟦ PE.D₀ ⟧ ⟦ PE.D₁ ⟧) s⨾id ⟦s⟧ → ⊥
no-unitor-closed = no-unitor {ρ = λ _ → false} (λ i A ())
