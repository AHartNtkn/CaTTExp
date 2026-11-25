------------------------------------------------------------------------
-- Checks of RCProc.Descent.MapGen by evaluation.  Γ is the chain
-- x —f→ y —g→ z; the generators are its five variables, listed in
-- dependency order (y, x, f, z, g: a different order from Γ's), and
-- f ;₀ g is expanded.  The abstract context H is built, the composite
-- is abstracted into it, and substituting back along H → Γ gives
-- f ;₀ g again.
------------------------------------------------------------------------
module CaTTExp.RCProc.Descent.MapGenExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (tm[])
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.TypedOps using (rcomp?; decTm)
open import CaTTExp.RCProc.GlueP using (treeCtx; varT)
open import CaTTExp.RCProc.Descent.MapGen

private
  T₂ : Tree
  T₂ = node (leaf ∷ leaf ∷ [])

  Γ : Ctx
  Γ = ctxOf T₂

  wΓ : Γ ⊢ctx
  wΓ = treeCtx T₂

  v : Nat → Maybe (TTm Γ)
  v = varT wΓ

  fg : Maybe (TTm Γ)
  fg = v 2 >>= λ f → v 4 >>= λ g → rcomp? 0 0 f g

  isVar : Tm → Bool
  isVar (var _) = true
  isVar _       = false

  exp : Tm → Bool
  exp t = not (isVar t)

  gs : Maybe (List (TTm Γ))
  gs = v 1 >>= λ y → v 0 >>= λ x → v 2 >>= λ f → v 3 >>= λ z → v 4 >>= λ g →
         just (y ∷ x ∷ f ∷ z ∷ g ∷ [])

  A : Maybe (Abs Γ)
  A = gs >>= absCtx wΓ exp

  back : Maybe Tm
  back = A >>= λ a → fg >>= λ t → absT exp a t >>= λ t′ → subH wΓ a >>= λ σ → just (tm t′ [ fst σ ]tm)

_ : is-just A ≡ true
_ = refl

_ : is-just (back >>= λ b → fg >>= λ t → decTm b (tm t) >>= λ _ → just tt) ≡ true
_ = refl
