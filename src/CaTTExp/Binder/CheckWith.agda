------------------------------------------------------------------------
-- A certified typechecker for CaTT with binders, for any decidable coh
-- side condition and any binder interface: every `just` it returns
-- carries a derivation. It is complete (CaTTExp.Binder.Completeness).
--
-- Checking a binder checks its telescope opened with fresh variables.
-- An opened entry is not a structural subterm of the binder, so the
-- checker recurses on fuel; `infer` and friends supply the size of the
-- input, which always suffices (opening with variables preserves size).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM

module CaTTExp.Binder.CheckWith
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (mark : Signature.Ctx 𝕊 → BM.Mark → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.Binder.TypingWith 𝕊 side mark

-- Decide syntactic equality of types and transport along it.
castWith : ∀ {Γ t A B} (b : Bool) → (T b → A ≡ B) → Γ ⊢tm t ∶ A → Maybe (Γ ⊢tm t ∶ B)
castWith true  eq d = just (subst (_ ⊢tm _ ∶_) (eq tt) d)
castWith false _  _ = nothing

castTy : ∀ {Γ t} A B → Γ ⊢tm t ∶ A → Maybe (Γ ⊢tm t ∶ B)
castTy A B d = castWith (A ==Ty B) (==Ty-sound A B) d

inferVar : ∀ Γ i → Γ ⊢ctx → (m : Maybe Ty) → lookup Γ i ≡ m →
           Maybe (Σ Ty (Γ ⊢tm var i ∶_))
inferVar Γ i w nothing  _  = nothing
inferVar Γ i w (just A) eq = just (A , var-wf w eq)

mutual
  checkCtx : Nat → (Γ : Ctx) → Maybe (Γ ⊢ctx)
  checkCtx zero    _       = nothing
  checkCtx (suc f) ε       = just ε-wf
  checkCtx (suc f) (Γ ▸[ _ ] A) = checkCtx f Γ >>= λ w → checkTy f Γ w A >>= λ a → just (▸-wf w a)

  checkTy : Nat → (Γ : Ctx) → Γ ⊢ctx → (A : Ty) → Maybe (Γ ⊢ty A)
  checkTy zero    Γ w _ = nothing
  checkTy (suc f) Γ w ⋆ = just (⋆-wf w)
  checkTy (suc f) Γ w (arr A t u) =
    inferTm f Γ w t >>= λ { (A₁ , d₁) →
    inferTm f Γ w u >>= λ { (A₂ , d₂) →
    castTy A₁ A d₁ >>= λ e₁ →
    castTy A₂ A d₂ >>= λ e₂ →
    just (arr-wf e₁ e₂) } }

  inferTm : Nat → (Γ : Ctx) → Γ ⊢ctx → (t : Tm) → Maybe (Σ Ty (Γ ⊢tm t ∶_))
  inferTm zero    Γ w _ = nothing
  inferTm (suc f) Γ w (var i) = inferVar Γ i w (lookup Γ i) refl
  inferTm (suc f) Γ w (bvar _ _) = nothing
  inferTm (suc f) Γ w (coh Δ ⋆ σ) = nothing
  inferTm (suc f) Γ w (coh Δ (arr A t u) σ) =
    checkPs Δ >>= λ p →
    checkCtx f Δ >>= λ wΔ →
    checkTy f Δ wΔ (arr A t u) >>= λ a →
    guard (side Δ A t u) λ ok →
    checkSub f Γ w σ Δ >>= λ s →
    just (_ , coh-wf p wΔ a ok s)
  inferTm (suc f) Γ w (cst k) = valid? k >>= λ v → just (ty k , cst-wf w v)
  inferTm (suc f) Γ w (bnd b y Δ ts) =
    guard (scTel? (len Γ) Δ) λ sc →
    guard (lcTel? 1 Δ) λ l →
    checkTel f Γ w Δ >>= λ wt →
    guard (bside b y Δ) λ ok →
    checkArgs f Γ w ts (bargs b y Δ) >>= λ as →
    just (_ , bnd-wf sc l wt ok as)

  -- The telescope opened after Γ.
  checkTel : Nat → (Γ : Ctx) → Γ ⊢ctx → (Δ : Ctx) → Maybe ((Γ ⧺ openTel (len Γ) Δ) ⊢ctx)
  checkTel zero    Γ w _       = nothing
  checkTel (suc f) Γ w ε       = just w
  checkTel (suc f) Γ w (Δ ▸[ _ ] A) =
    checkTel f Γ w Δ >>= λ w′ →
    checkTy f (Γ ⧺ openTel (len Γ) Δ) w′ (opTy 0 (fresh (len Γ) (len Δ)) A) >>= λ a →
    just (▸-wf w′ a)

  checkSub : Nat → (Γ : Ctx) → Γ ⊢ctx → (σ : Sub) (Δ : Ctx) → Maybe (Γ ⊢sub σ ∶ Δ)
  checkSub zero    Γ w _        _       = nothing
  checkSub (suc f) Γ w ⟨⟩       ε       = just (⟨⟩-wf w)
  checkSub (suc f) Γ w (σ ,ₛ t) (Δ ▸[ ms ] A) =
    checkSub f Γ w σ Δ >>= λ s →
    inferTm f Γ w t >>= λ { (B , d) →
    castTy B (A [ σ ]ty) d >>= λ e →
    guard (marksOK Γ ms t) λ o →
    just (,-wf s e o) }
  checkSub (suc f) Γ w _ _ = nothing

  checkArgs : Nat → (Γ : Ctx) → Γ ⊢ctx → (ts : Sub) (Θ : Ctx) → Maybe (Γ ⊢args ts ∶ Θ)
  checkArgs zero    Γ w _         _       = nothing
  checkArgs (suc f) Γ w ⟨⟩        ε       = just (⟨⟩-a w)
  checkArgs (suc f) Γ w (ts ,ₛ t) (Θ ▸[ ms ] A) =
    checkArgs f Γ w ts Θ >>= λ s →
    inferTm f Γ w t >>= λ { (B , d) →
    castTy B (opTy 0 ts A) d >>= λ e →
    guard (marksOK Γ ms t) λ o →
    just (,-a s e o) }
  checkArgs (suc f) Γ w _ _ = nothing

-- Entry points, with fuel the size of the input.
ctx? : (Γ : Ctx) → Maybe (Γ ⊢ctx)
ctx? Γ = checkCtx (sizeTel Γ) Γ

infer : (Γ : Ctx) (t : Tm) → Maybe (Σ Ty (Γ ⊢tm t ∶_))
infer Γ t = ctx? Γ >>= λ w → inferTm (sizeTm t) Γ w t
