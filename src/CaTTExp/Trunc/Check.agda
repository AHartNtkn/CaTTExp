------------------------------------------------------------------------
-- A certified checker for CaTTExp.Trunc.Typing: every `just` carries a
-- derivation. It tries the plain coh rule first, then the three
-- truncation contexts.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Trunc.Check (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Trunc.Typing 𝕊 public
open import CaTTExp.Typing 𝕊 using (cattSide)
open import CaTTExp.PastingCheck 𝕊 using (checkPs)

castWith : ∀ {Γ M t A B} (b : Bool) → (T b → A ≡ B) → Γ ∣ M ⊢tm t ∶ A → Maybe (Γ ∣ M ⊢tm t ∶ B)
castWith true  eq d = just (subst (_ ∣ _ ⊢tm _ ∶_) (eq tt) d)
castWith false _  _ = nothing

castTy : ∀ {Γ M t} A B → Γ ∣ M ⊢tm t ∶ A → Maybe (Γ ∣ M ⊢tm t ∶ B)
castTy A B d = castWith (A ==Ty B) (==Ty-sound A B) d

inferVar : ∀ Γ M i → Γ ∣ M ⊢ctx → (m : Maybe Ty) → lookup Γ i ≡ m →
           Maybe (Σ Ty (Γ ∣ M ⊢tm var i ∶_))
inferVar Γ M i w nothing  _  = nothing
inferVar Γ M i w (just A) eq = just (A , var-wf w eq)

orElse : ∀ {a} {A : Set a} → Maybe A → Maybe A → Maybe A
orElse (just x) _ = just x
orElse nothing  m = m

half : Nat → Nat
half (suc (suc n)) = suc (half n)
half _             = zero

-- Decide Δ ≡ Δ' and B ≡ B', and move a coh derivation along.
same : ∀ {Γ M σ X} Δ' B' Δ B → Γ ∣ M ⊢tm coh Δ' B' σ ∶ X → Maybe (Γ ∣ M ⊢tm coh Δ B σ ∶ X)
same {Γ} {M} {σ} {X} Δ' B' Δ B d = go (Δ' ==Ctx Δ) (==Ctx-sound Δ' Δ) (B' ==Ty B) (==Ty-sound B' B)
  where
  go : (b : Bool) → (T b → Δ' ≡ Δ) → (c : Bool) → (T c → B' ≡ B) → Maybe (Γ ∣ M ⊢tm coh Δ B σ ∶ X)
  go true p true q = just (subst (λ Z → Γ ∣ M ⊢tm coh Z B σ ∶ X) (p tt)
                             (subst (λ Z → Γ ∣ M ⊢tm coh Δ' Z σ ∶ X) (q tt) d))
  go _ _ _ _ = nothing

-- Decide a boolean and hand its proof to a continuation.
decide : ∀ {a} {A : Set a} (b : Bool) → (T b → Maybe A) → Maybe A
decide = guard

mutual
  checkCtx : (Γ : Ctx) (M : Marks) → Maybe (Γ ∣ M ⊢ctx)
  checkCtx ε       M = just ε-wf
  checkCtx (Γ ▸ A) M = checkCtx Γ M >>= λ w → checkTy Γ M w A >>= λ a → just (▸-wf w a)

  checkTy : (Γ : Ctx) (M : Marks) → Γ ∣ M ⊢ctx → (A : Ty) → Maybe (Γ ∣ M ⊢ty A)
  checkTy Γ M w ⋆ = just (⋆-wf w)
  checkTy Γ M w (arr A t u) =
    inferTm Γ M w t >>= λ { (A₁ , d₁) →
    inferTm Γ M w u >>= λ { (A₂ , d₂) →
    castTy A₁ A d₁ >>= λ e₁ →
    castTy A₂ A d₂ >>= λ e₂ →
    just (arr-wf e₁ e₂) } }

  inferTm : (Γ : Ctx) (M : Marks) → Γ ∣ M ⊢ctx → (t : Tm) → Maybe (Σ Ty (Γ ∣ M ⊢tm t ∶_))
  inferTm Γ M w (var i) = inferVar Γ M i w (lookup Γ i) refl
  inferTm Γ M w (coh Δ ⋆ σ) = nothing
  inferTm Γ M w (coh Δ (arr A t u) σ) =
    orElse
      (checkPs Δ >>= λ p →
       checkCtx Δ none >>= λ wΔ →
       checkTy Δ none wΔ (arr A t u) >>= λ a →
       guard (cattSide Δ A t u) λ ok →
       checkSub Γ M w σ Δ >>= λ s →
       just (_ , coh-wf p wΔ a ok s))
    (orElse
      -- (T-fill): Δ has length 2k + 4
      (let k = half (len Δ ∸ 4) in
       checkSub Γ M w σ (TF k) >>= λ s →
       decide (allows (markOf M (objOf σ)) (suc k)) λ ok →
       same (TF k) (TFty k) Δ (arr A t u) (tfill-wf s ok) >>= λ d → just (_ , d))
    (orElse
      -- (T-inv): Δ has length 2j + 5
      (let j = half (len Δ ∸ 5) in
       checkSub Γ M w σ (TI j) >>= λ s →
       decide (allows (markOf M (objOf σ)) (suc (suc j))) λ ok →
       same (TI j) (TIty j) Δ (arr A t u) (tinv-wf s ok) >>= λ d → just (_ , d))
      -- (T-ctr)
      (checkSub Γ M w σ TC >>= λ s →
       decide (allows (markOf M (objOf σ)) 0) λ ok →
       same TC TCty Δ (arr A t u) (tctr-wf s ok) >>= λ d → just (_ , d))))
  inferTm Γ M w (cst k) = valid? k >>= λ v → just (ty k , cst-wf w v)

  checkSub : (Γ : Ctx) (M : Marks) → Γ ∣ M ⊢ctx → (σ : Sub) (Δ : Ctx) → Maybe (Γ ∣ M ⊢sub σ ∶ Δ)
  checkSub Γ M w ⟨⟩       ε       = just (⟨⟩-wf w)
  checkSub Γ M w (σ ,ₛ t) (Δ ▸ A) =
    checkSub Γ M w σ Δ >>= λ s →
    inferTm Γ M w t >>= λ { (B , d) →
    castTy B (A [ σ ]ty) d >>= λ e →
    just (,-wf s e) }
  checkSub Γ M w _ _ = nothing

infer : (Γ : Ctx) (M : Marks) (t : Tm) → Maybe (Σ Ty (Γ ∣ M ⊢tm t ∶_))
infer Γ M t = checkCtx Γ M >>= λ w → inferTm Γ M w t

-- Typecheck t against a given type.
check : (Γ : Ctx) (M : Marks) (t : Tm) (A : Ty) → Maybe (Γ ∣ M ⊢tm t ∶ A)
check Γ M t A = infer Γ M t >>= λ { (B , d) → castTy B A d }
