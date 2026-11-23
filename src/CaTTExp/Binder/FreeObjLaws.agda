------------------------------------------------------------------------
-- The free-object head (CaTTExp.Binder.FreeObj): stability laws,
-- generic in the former set (`side-stableF` etc., for use beside other
-- formers), and BinderLaws and PresupLaws over any binder-free 𝕊₀
-- (every side condition and mark judgment). Also (FREE) itself:
-- `free-wf` (Γ closed, locally closed and well formed after Θ gives
-- Θ ⊢ ⟦Γ⟧ : ⋆) and its inversion `free-inv`.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (Binders; extend)
open import CaTTExp.Binder.FreeObj
import CaTTExp.Binder.Laws as Laws
import CaTTExp.Binder.Mark as BM

module CaTTExp.Binder.FreeObjLaws (𝕊₀ : Old.Signature) where

𝕊 : Signature
𝕊 = extend 𝕊₀ (freeBinders (Old.Signature.K 𝕊₀))

open Signature 𝕊
open Laws 𝕊
open FreeConstruction K FreeF (λ b → b)
open import CaTTExp.Binder.SyntaxLemmas K B

closed-tel : ∀ Γ σ → T (scTel? 0 Γ) → Γ [ σ ]tel ≡ Γ
closed-tel ε            σ _ = refl
closed-tel (Γ ▸[ ms ] A) σ p =
  let (a , b) = T∧ {scTel? 0 Γ} p in cong₂ (_▸[ ms ]_) (closed-tel Γ σ a) (closed-ty A σ b)

side-stableF : ∀ b y Δ σ → LC σ → T (sideF b y Δ) → T (sideF b y (Δ [ σ ]tel))
side-stableF free y Δ σ _ p rewrite closed-tel Δ σ (snd (T∧ {y ==ℕ 0} p)) = p

freeLaws : BinderLaws
freeLaws = record
  { side-stable = side-stableF
  ; args-stable = λ _ _ _ _ _ _ → refl
  ; res-stable  = λ _ _ _ _ _ _ → refl
  ; res-sc      = λ _ _ _ _ _ _ → tt
  }

module _ (side′ : Ctx → Ty → Tm → Tm → Bool) (mark : Ctx → BM.Mark → Tm → Bool) where

  open import CaTTExp.Binder.TypingWith 𝕊 side′ mark
  open import CaTTExp.Binder.Presup 𝕊 side′ mark using (PresupLaws; tm-ctx)

  -- A well-formed extension has a well-formed prefix.
  prefix-wf : ∀ Θ Ξ → (Θ ⧺ Ξ) ⊢ctx → Θ ⊢ctx
  prefix-wf Θ ε            w            = w
  prefix-wf Θ (Ξ ▸[ _ ] _) (▸-wf w _) = prefix-wf Θ Ξ w

  freePresup : PresupLaws
  freePresup = record
    { bargs-sc = λ _ _ _ _ _ _ → tt
    ; res-wf   = λ {Γ} {b} {y} {Δ} _ _ w _ → ⋆-wf (prefix-wf Γ (openTel (len Γ) Δ) w)
    }

  -- (FREE), and its inversion.
  free-wf : ∀ {Θ Γ} → T (scTel? 0 Γ) → T (lcTel? 1 Γ) → (Θ ⧺ openTel (len Θ) Γ) ⊢ctx → Θ ⊢tm ⟦ Γ ⟧ ∶ ⋆
  free-wf {Θ} {Γ} c l w =
    bnd-wf (scTel-mono0 Γ c) l w (∧T {0 ==ℕ 0} tt c) (⟨⟩-a (prefix-wf Θ _ w))
    where
    scTel-mono0 : ∀ Γ → T (scTel? 0 Γ) → T (scTel? (len Θ) Γ)
    scTel-mono0 ε _ = tt
    scTel-mono0 (Γ ▸[ _ ] A) p = let (a , b) = T∧ {scTel? 0 Γ} p in ∧T (scTel-mono0 Γ a) (scTy-mono (len Θ) A b)

  free-inv : ∀ {Θ Γ A} → Θ ⊢tm ⟦ Γ ⟧ ∶ A → (A ≡ ⋆) × T (scTel? 0 Γ) × (Θ ⧺ openTel (len Θ) Γ) ⊢ctx
  free-inv (bnd-wf _ _ w s _) = refl , snd (T∧ {0 ==ℕ 0} s) , w
