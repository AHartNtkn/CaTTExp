------------------------------------------------------------------------
-- Checks of RCProc.TypedSub by evaluation: on the 1-disc x, y, f : x → y,
-- the identity entries (in context order) build a typed substitution,
-- and the swapped entries y, x, f are refused (f's type is then y → x).
------------------------------------------------------------------------
module CaTTExp.RCProc.TypedSubExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.RCProc.TypedSub

private
  Γ₀ Γ₁ D : Ctx
  Γ₀ = ε ▸ ⋆
  Γ₁ = Γ₀ ▸ ⋆
  D  = Γ₁ ▸ arr ⋆ (var 0) (var 1)

  w₀ : Γ₀ ⊢ctx
  w₀ = ▸-wf ε-wf (⋆-wf ε-wf)
  w₁ : Γ₁ ⊢ctx
  w₁ = ▸-wf w₀ (⋆-wf w₀)
  wD : D ⊢ctx
  wD = ▸-wf w₁ (arr-wf (var-wf w₁ refl) (var-wf w₁ refl))

  x y f : TTm D
  x = tt[ var 0 ∶ ⋆ , var-wf wD refl ]
  y = tt[ var 1 ∶ ⋆ , var-wf wD refl ]
  f = tt[ var 2 ∶ arr ⋆ (var 0) (var 1) , var-wf wD refl ]

  isJust : ∀ {a} {X : Set a} → Maybe X → Bool
  isJust (just _) = true
  isJust nothing  = false

ok : isJust (buildSub wD D (x ∷ y ∷ f ∷ [])) ≡ true
ok = refl

refused : isJust (buildSub wD D (y ∷ x ∷ f ∷ [])) ≡ false
refused = refl
