------------------------------------------------------------------------
-- A certified typechecker, for any decidable coh side condition: every
-- `just` it returns carries a derivation, so a successful run *is* a
-- proof that the input is well typed. (It is not proved complete; a `nothing` proves nothing.)
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.CheckWith
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.TypingWith 𝕊 side
open import CaTTExp.PastingTrees 𝕊 using (checkPs)

private
  -- Decide syntactic equality of types and transport along it.
  castTy : ∀ {Γ t} A B → Γ ⊢tm t ∶ A → Maybe (Γ ⊢tm t ∶ B)
  castTy A B d = go (A ==Ty B) (==Ty-sound A B)
    where
    go : (b : Bool) → (T b → A ≡ B) → Maybe _
    go true  eq = just (subst (_ ⊢tm _ ∶_) (eq tt) d)
    go false _  = nothing

  inferVar : ∀ Γ i → Γ ⊢ctx → (m : Maybe Ty) → lookup Γ i ≡ m →
             Maybe (Σ Ty (Γ ⊢tm var i ∶_))
  inferVar Γ i w nothing  _  = nothing
  inferVar Γ i w (just A) eq = just (A , var-wf w eq)

mutual
  checkCtx : (Γ : Ctx) → Maybe (Γ ⊢ctx)
  checkCtx ε       = just ε-wf
  checkCtx (Γ ▸ A) = checkCtx Γ >>= λ w → checkTy Γ w A >>= λ a → just (▸-wf w a)

  checkTy : (Γ : Ctx) → Γ ⊢ctx → (A : Ty) → Maybe (Γ ⊢ty A)
  checkTy Γ w ⋆ = just (⋆-wf w)
  checkTy Γ w (arr A t u) =
    inferTm Γ w t >>= λ { (A₁ , d₁) →
    inferTm Γ w u >>= λ { (A₂ , d₂) →
    castTy A₁ A d₁ >>= λ e₁ →
    castTy A₂ A d₂ >>= λ e₂ →
    just (arr-wf e₁ e₂) } }

  inferTm : (Γ : Ctx) → Γ ⊢ctx → (t : Tm) → Maybe (Σ Ty (Γ ⊢tm t ∶_))
  inferTm Γ w (var i) = inferVar Γ i w (lookup Γ i) refl
  inferTm Γ w (coh Δ ⋆ σ) = nothing
  inferTm Γ w (coh Δ (arr A t u) σ) =
    checkPs Δ >>= λ p →
    checkCtx Δ >>= λ wΔ →
    checkTy Δ wΔ (arr A t u) >>= λ a →
    guard (side Δ A t u) λ ok →
    checkSub Γ w σ Δ >>= λ s →
    just (_ , coh-wf p wΔ a ok s)
  inferTm Γ w (cst k) = valid? k >>= λ v → just (ty k , cst-wf w v)

  checkSub : (Γ : Ctx) → Γ ⊢ctx → (σ : Sub) (Δ : Ctx) → Maybe (Γ ⊢sub σ ∶ Δ)
  checkSub Γ w ⟨⟩       ε       = just (⟨⟩-wf w)
  checkSub Γ w (σ ,ₛ t) (Δ ▸ A) =
    checkSub Γ w σ Δ >>= λ s →
    inferTm Γ w t >>= λ { (B , d) →
    castTy B (A [ σ ]ty) d >>= λ e →
    just (,-wf s e) }
  checkSub Γ w _ _ = nothing

-- Convenience: typecheck a term in a context, returning its type and
-- derivation.
infer : (Γ : Ctx) (t : Tm) → Maybe (Σ Ty (Γ ⊢tm t ∶_))
infer Γ t = checkCtx Γ >>= λ w → inferTm Γ w t
