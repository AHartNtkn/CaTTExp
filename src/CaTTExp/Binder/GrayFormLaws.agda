------------------------------------------------------------------------
-- The Gray object formers (CaTTExp.Binder.GrayForm) over any
-- binder-free signature 𝕊₀:
--
--  * grayLaws: the stability laws (CaTTExp.Binder.Laws.BinderLaws), so
--    substitution and weakening are admissible for 𝕊₀ + ⊗, \, / with
--    every coh side condition and every stable mark judgment
--    (CaTTExp.Binder.Subst), and the checker is complete
--    (CaTTExp.Binder.Completeness);
--  * grayPresup: the presupposition law (CaTTExp.Binder.Presup), for
--    every side condition and mark judgment;
--  * gb-wf and gb-inv: (GB-form) is derivable, and it is the only way
--    to type a Gray former: a well-typed A ⊗ B, A\B or B/A has type ⋆
--    and object arguments.
--
-- Conservativity over 𝕊₀ is CaTTExp.Binder.Embed for this interface
-- (`Embed.CaTT 𝕊₀ (grayFormBinders K)` for plain CaTT).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (Binders; extend)
open import CaTTExp.Binder.GrayForm
import CaTTExp.Binder.Laws as Laws
import CaTTExp.Binder.Mark as BM

module CaTTExp.Binder.GrayFormLaws (𝕊₀ : Old.Signature) where

𝕊 : Signature
𝕊 = extend 𝕊₀ (grayFormBinders (Old.Signature.K 𝕊₀))

open Signature 𝕊
open Laws 𝕊
open GrayFormConstruction K GBF (λ b → b)
open import CaTTExp.Binder.GrayFormLawsGen K GBF (λ b → b)
open import CaTTExp.Binder.SyntaxLemmas K B using (T∧)

grayLaws : BinderLaws
grayLaws = record
  { side-stable = side-stableG
  ; args-stable = args-stableG
  ; res-stable  = res-stableG
  ; res-sc      = res-scG
  }

module _ (side′ : Ctx → Ty → Tm → Tm → Bool) (mark : Ctx → BM.Mark → Tm → Bool) where

  open import CaTTExp.Binder.TypingWith 𝕊 side′ mark
  open import CaTTExp.Binder.Presup 𝕊 side′ mark using (PresupLaws; tm-ctx)

  side-ne : ∀ b y Δ ms A → T (side b y (Δ ▸[ ms ] A)) → ⊥
  side-ne b y Δ ms A p = snd (T∧ {y ==ℕ 0} {false} p)

  -- Γ ▸ ⋆ ▸ ⋆ is well formed when Γ is.
  ⋆⋆-wf : ∀ {Γ} → Γ ⊢ctx → (Γ ▸ ⋆ ▸ ⋆) ⊢ctx
  ⋆⋆-wf w = ▸-wf (▸-wf w (⋆-wf w)) (⋆-wf (▸-wf w (⋆-wf w)))

  res-wfG : ∀ {Γ b y Δ} → T (scTel? (len Γ) Δ) → T (lcTel? 1 Δ) →
            (Γ ⧺ openTel (len Γ) Δ) ⊢ctx → T (side b y Δ) →
            (Γ ⧺ openTel (len Γ) (args b y Δ)) ⊢ty
              opTy 0 (fresh (len Γ) (len (args b y Δ))) (res b y Δ)
  res-wfG {Δ = ε}            _ _ w _ = ⋆-wf (⋆⋆-wf w)
  res-wfG {b = b} {y = y} {Δ = Δ ▸[ ms ] A} _ _ _ p = ⊥-elim (side-ne b y Δ ms A p)

  grayPresup : PresupLaws
  grayPresup = record { bargs-sc = bargs-scG ; res-wf = λ {Γ} {b} {y} {Δ} → res-wfG {Γ} {b} {y} {Δ} }

  -- (GB-form).
  gb-wf : ∀ {Γ a c} k → Γ ⊢tm a ∶ ⋆ → Γ ⊢tm c ∶ ⋆ → Γ ⊢tm gbApp k a c ∶ ⋆
  gb-wf k da dc = bnd-wf tt tt w tt (,-a (,-a (⟨⟩-a w) da tt) dc tt)
    where w = tm-ctx da

  -- Inversion: (GB-form) is the only rule typing a Gray former.
  gb-inv : ∀ {Γ a c A} k → Γ ⊢tm gbApp k a c ∶ A →
           (A ≡ ⋆) × (Γ ⊢tm a ∶ ⋆) × (Γ ⊢tm c ∶ ⋆)
  gb-inv k (bnd-wf _ _ _ _ (,-a (,-a (⟨⟩-a _) da _) dc _)) = refl , da , dc
