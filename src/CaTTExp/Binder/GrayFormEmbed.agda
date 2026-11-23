------------------------------------------------------------------------
-- The object formulas of the Gray biclosed rules
-- (CaTTExp.Gray.Biclosed.Syntax, `Fm`) as kernel object terms built
-- with the formers of CaTTExp.Binder.GrayForm:
--
--   obj i ↦ ρ i,   X ⊗ Y ↦ X ⊗ Y,   A \\ C ↦ A\C,   C // A ↦ C/A.
--
-- Every formula built from object atoms is sent to a well-typed object
-- (`fm-wf`), for every coh side condition and mark judgment, provided
-- the atoms are sent to objects. Representables ⟦Θ⟧ and free objects
-- ⟦Θ⟧♭ are chapter 7's heads, which the binder kernel does not have
-- yet; formulas containing them have no image (`nothing`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.GrayForm
import CaTTExp.Binder.Mark as BM
open import CaTTExp.Gray.Biclosed.Syntax using (Fm; obj; rep; shp; _⊗_; _\\_; _//_)

module CaTTExp.Binder.GrayFormEmbed (𝕊₀ : Old.Signature) where

open import CaTTExp.Binder.GrayFormLaws 𝕊₀
open Signature 𝕊
open GrayFormConstruction K GBF (λ b → b)

fmTm : (Nat → Tm) → Fm → Maybe Tm
fmTm ρ (obj i)  = just (ρ i)
fmTm ρ (rep _)  = nothing
fmTm ρ (shp _)  = nothing
fmTm ρ (X ⊗ Y)  = fmTm ρ X >>= λ a → fmTm ρ Y >>= λ b → just (a ⊗ᵗ b)
fmTm ρ (A \\ C) = fmTm ρ A >>= λ a → fmTm ρ C >>= λ c → just (a \\ᵗ c)
fmTm ρ (C // A) = fmTm ρ C >>= λ c → fmTm ρ A >>= λ a → just (c //ᵗ a)

module _ (side′ : Ctx → Ty → Tm → Tm → Bool) (mark : Ctx → BM.Mark → Tm → Bool) where

  open import CaTTExp.Binder.TypingWith 𝕊 side′ mark

  private
    bind2 : ∀ {Γ} (mx my : Maybe Tm) (f : Tm → Tm → Tm) {t} →
            (∀ {a c} → Γ ⊢tm a ∶ ⋆ → Γ ⊢tm c ∶ ⋆ → Γ ⊢tm f a c ∶ ⋆) →
            (∀ {a} → mx ≡ just a → Γ ⊢tm a ∶ ⋆) →
            (∀ {c} → my ≡ just c → Γ ⊢tm c ∶ ⋆) →
            (mx >>= λ a → my >>= λ c → just (f a c)) ≡ just t → Γ ⊢tm t ∶ ⋆
    bind2 (just a) (just c) f k hx hy refl = k (hx refl) (hy refl)
    bind2 (just a) nothing  f k hx hy ()
    bind2 nothing  _        f k hx hy ()

  fm-wf : ∀ {Γ} (ρ : Nat → Tm) → (∀ i → Γ ⊢tm ρ i ∶ ⋆) →
          ∀ X {t} → fmTm ρ X ≡ just t → Γ ⊢tm t ∶ ⋆
  fm-wf ρ hρ (obj i)  refl = hρ i
  fm-wf ρ hρ (rep _)  ()
  fm-wf ρ hρ (shp _)  ()
  fm-wf ρ hρ (X ⊗ Y)  e = bind2 (fmTm ρ X) (fmTm ρ Y) _⊗ᵗ_  (gb-wf side′ mark tensorK)
                            (fm-wf ρ hρ X) (fm-wf ρ hρ Y) e
  fm-wf ρ hρ (A \\ C) e = bind2 (fmTm ρ A) (fmTm ρ C) _\\ᵗ_ (gb-wf side′ mark lhomK)
                            (fm-wf ρ hρ A) (fm-wf ρ hρ C) e
  fm-wf ρ hρ (C // A) e = bind2 (fmTm ρ C) (fmTm ρ A) _//ᵗ_ (gb-wf side′ mark rhomK)
                            (fm-wf ρ hρ C) (fm-wf ρ hρ A) e
