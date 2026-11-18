------------------------------------------------------------------------
-- A certified checker for CaTTExp.Trunc.Typing: every `just` carries a
-- derivation. It tries the plain coh rule first, then the three
-- truncation contexts.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Trunc.Check
  (𝕊 : Signature)
  (μ : Signature.Tm 𝕊 → Maybe Nat)
  where

open Signature 𝕊
open import CaTTExp.Trunc.Typing 𝕊 μ public
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

half : Nat → Nat
half (suc (suc n)) = suc (half n)
half _             = zero

-- Decide Δ ≡ Δ' and B ≡ B', and move a coh derivation along.
same : ∀ {Γ σ X} Δ' B' Δ B → Γ ⊢tm coh Δ' B' σ ∶ X → Maybe (Γ ⊢tm coh Δ B σ ∶ X)
same {Γ} {σ} {X} Δ' B' Δ B d = go (Δ' ==Ctx Δ) (==Ctx-sound Δ' Δ) (B' ==Ty B) (==Ty-sound B' B)
  where
  go : (b : Bool) → (T b → Δ' ≡ Δ) → (c : Bool) → (T c → B' ≡ B) → Maybe (Γ ⊢tm coh Δ B σ ∶ X)
  go true p true q = just (subst (λ Z → Γ ⊢tm coh Z B σ ∶ X) (p tt)
                             (subst (λ Z → Γ ⊢tm coh Δ' Z σ ∶ X) (q tt) d))
  go _ _ _ _ = nothing

-- Decide a boolean and hand its proof to a continuation.
decide : ∀ {a} {A : Set a} (b : Bool) → (T b → Maybe A) → Maybe A
decide = guard

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
    orElse
      (checkPs Δ >>= λ p →
       checkCtx Δ >>= λ wΔ →
       checkTy Δ wΔ (arr A t u) >>= λ a →
       guard (cattSide Δ A t u) λ ok →
       checkSub Γ w σ Δ >>= λ s →
       just (_ , coh-wf p wΔ a ok s))
    (orElse
      -- (T-fill): Δ has length 2k + 4
      (let k = half (len Δ ∸ 4) in
       checkSub Γ w σ (TF k) >>= λ s →
       decide (allows (μ (objOf σ)) (suc k)) λ ok →
       same (TF k) (TFty k) Δ (arr A t u) (tfill-wf s ok) >>= λ d → just (_ , d))
    (orElse
      -- (T-inv): Δ has length 2j + 5
      (let j = half (len Δ ∸ 5) in
       checkSub Γ w σ (TI j) >>= λ s →
       decide (allows (μ (objOf σ)) (suc (suc j))) λ ok →
       same (TI j) (TIty j) Δ (arr A t u) (tinv-wf s ok) >>= λ d → just (_ , d))
      -- (T-ctr)
      (checkSub Γ w σ TC >>= λ s →
       decide (allows (μ (objOf σ)) 0) λ ok →
       same TC TCty Δ (arr A t u) (tctr-wf s ok) >>= λ d → just (_ , d))))
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

-- Typecheck t against a given type.
check : (Γ : Ctx) (t : Tm) (A : Ty) → Maybe (Γ ⊢tm t ∶ A)
check Γ t A = infer Γ t >>= λ { (B , d) → castTy B A d }
