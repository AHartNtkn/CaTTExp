------------------------------------------------------------------------
-- A certified checker for CaTTExp.Ops.Typing: every `just` carries a
-- derivation. A coh is tried first as a plain coherence, then as a
-- declared operation.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Ops.Check
  (𝕊 : Signature)
  (ops : List (Σ (Signature.Ctx 𝕊) (λ _ → Signature.Ty 𝕊)))
  where

open Signature 𝕊
open import CaTTExp.Ops.Typing 𝕊 ops public
open import CaTTExp.Typing 𝕊 using (cattSide)
open import CaTTExp.PastingCheck 𝕊 using (checkPs)

castWith : ∀ {Γ t A B} (b : Bool) → (T b → A ≡ B) → Γ ⊢tm t ∶ A → Maybe (Γ ⊢tm t ∶ B)
castWith true  eq d = just (subst (_ ⊢tm _ ∶_) (eq tt) d)
castWith false _  _ = nothing

castTy : ∀ {Γ t} A B → Γ ⊢tm t ∶ A → Maybe (Γ ⊢tm t ∶ B)
castTy A B d = castWith (A ==Ty B) (==Ty-sound A B) d

inferVar : ∀ Γ i → Γ ⊢ctx → (m : Maybe Ty) → lookup Γ i ≡ m →
           Maybe (Σ Ty (Γ ⊢tm var i ∶_))
inferVar Γ i w nothing  _  = nothing
inferVar Γ i w (just A) eq = just (A , var-wf w eq)

orElse : ∀ {a} {A : Set a} → Maybe A → Maybe A → Maybe A
orElse (just x) _ = just x
orElse nothing  m = m

-- Find (Δ, B) among the declared operations.
member : (Δ : Ctx) (B : Ty) (os : List (Σ Ctx (λ _ → Ty))) → Maybe ((Δ , B) ∈ os)
member Δ B []              = nothing
member Δ B ((Δ' , B') ∷ os) = orElse (go (Δ' ==Ctx Δ) (==Ctx-sound Δ' Δ) (B' ==Ty B) (==Ty-sound B' B))
                                     (member Δ B os >>= λ p → just (there p))
  where
  go : (b : Bool) → (T b → Δ' ≡ Δ) → (c : Bool) → (T c → B' ≡ B) →
       Maybe ((Δ , B) ∈ ((Δ' , B') ∷ os))
  go true p true q = just (subst (λ Z → (Δ , B) ∈ ((Z , B') ∷ os)) (sym (p tt))
                            (subst (λ Z → (Δ , B) ∈ ((Δ , Z) ∷ os)) (sym (q tt)) here))
  go _ _ _ _ = nothing

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
  inferTm Γ w (coh Δ ⋆ σ) =
    member Δ ⋆ ops >>= λ m → checkSub Γ w σ Δ >>= λ s → just (_ , op-wf m s)
  inferTm Γ w (coh Δ (arr A t u) σ) =
    orElse
      (checkPs Δ >>= λ p →
       checkCtx Δ >>= λ wΔ →
       checkTy Δ wΔ (arr A t u) >>= λ a →
       guard (cattSide Δ A t u) λ ok →
       checkSub Γ w σ Δ >>= λ s →
       just (_ , coh-wf p wΔ a ok s))
      (member Δ (arr A t u) ops >>= λ m →
       checkSub Γ w σ Δ >>= λ s →
       just (_ , op-wf m s))
  inferTm Γ w (cst k) = valid? k >>= λ v → just (ty k , cst-wf w v)

  checkSub : (Γ : Ctx) → Γ ⊢ctx → (σ : Sub) (Δ : Ctx) → Maybe (Γ ⊢sub σ ∶ Δ)
  checkSub Γ w ⟨⟩       ε       = just (⟨⟩-wf w)
  checkSub Γ w (σ ,ₛ t) (Δ ▸ A) =
    checkSub Γ w σ Δ >>= λ s →
    inferTm Γ w t >>= λ { (B , d) →
    castTy B (A [ σ ]ty) d >>= λ e →
    just (,-wf s e) }
  checkSub Γ w _ _ = nothing

infer : (Γ : Ctx) (t : Tm) → Maybe (Σ Ty (Γ ⊢tm t ∶_))
infer Γ t = checkCtx Γ >>= λ w → inferTm Γ w t

check : (Γ : Ctx) (t : Tm) (A : Ty) → Maybe (Γ ⊢tm t ∶ A)
check Γ t A = infer Γ t >>= λ { (B , d) → castTy B A d }
