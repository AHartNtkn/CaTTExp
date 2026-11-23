------------------------------------------------------------------------
-- Strictifying interchange is never conservative over two-tier L
-- (notes/surface-conservativity.md §4.4, Proposition 4.6).
--
-- Take any surface definitional equality E over two-tier L (any
-- relation satisfying (E) of CaTTExp.Surface.Conservativity) that makes
-- the two layerings of a horizontal pair equal in the pasting context
-- ΣD¹ ∨ ΣD¹ (HComp):
--
--     HComp ∣ (f◁β);(α▷g′)  ≈  (α▷g);(f′◁β)
--
-- as every surface that strictifies interchange must. Then the surface
-- is not conservative at HComp: the interchanger ich : βα → αβ, read
-- at the ≈-equal type αβ → βα, inhabits the reverse interchanger type,
-- which no kernel term has (Strict.ReverseInterchanger).
--
-- This holds for every such E, whatever else it identifies, so every
-- subset of {associators, unitors, interchange} containing interchange
-- fails, already in a pasting context and in dimension 3.
------------------------------------------------------------------------
module CaTTExp.Surface.StrictInterchange where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure
open import CaTTExp.Gray.Examples using (HComp; ichTy⁻; αβ; βα; αβ-wf; βα-wf; ich-wf)
open import CaTTExp.Strict.ReverseInterchanger using (no-reverse-interchanger)
import CaTTExp.Subst ∅ graySide as Sb
open import CaTTExp.Weakening ∅ graySide using (wk-ty)
open import CaTTExp.Surface.Conservativity ∅ graySide (λ ())

-- The kernel's presupposition for two-tier L over the empty signature.
private
  closed : Sb.Closed
  closed ()

  lookup-wf : ∀ {Γ i A} → Γ ⊢ctx → lookup Γ i ≡ just A → Γ ⊢ty A
  lookup-wf {Γ ▸ B} {i} (▸-wf w b) eq with i ==ℕ len Γ
  ... | true  = subst (λ X → (Γ ▸ B) ⊢ty X) (just-inj eq) (wk-ty b (▸-wf w b))
    where
    just-inj : ∀ {x y : Ty} → just x ≡ just y → x ≡ y
    just-inj refl = refl
  ... | false = wk-ty (lookup-wf w eq) (▸-wf w b)

presup : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A
presup (var-wf w eq)      = lookup-wf w eq
presup (coh-wf _ _ a _ s) = Sb.ty[] closed a s
presup (cst-wf {k} _ _)   = ⊥-elim k

strict-interchange-not-conservative :
  (E : SurfaceEq) → SurfaceEq._∣_≈t_ E HComp βα αβ → ¬ ConservativeAt E HComp
strict-interchange-not-conservative E eq =
  Embed.reverse-breaks E presup ich-wf αβ-wf βα-wf eq no-reverse-interchanger
