------------------------------------------------------------------------
-- Stability laws for ⟦Γ⟧, ⊤ and the generic diagram η_Γ together
-- (CaTTExp.Binder.GenHeads), over any binder-free 𝕊₀: BinderLaws, so
-- substitution, weakening, the certified checker and its completeness
-- hold (CaTTExp.Binder.Laws). Every head is closed (no arguments, a
-- closed telescope for ⟦Γ⟧, an empty one for ⊤ and η, and a closed
-- type), so substitution fixes all of them.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (extend)
open import CaTTExp.Binder.GenHeads
open import CaTTExp.Binder.FreeObj using (free)
import CaTTExp.Pure as P
import CaTTExp.Binder.Laws as Laws

module CaTTExp.Binder.GenHeadsLaws (𝕊₀ : Old.Signature) where

𝕊 : Signature
𝕊 = extend 𝕊₀ (genBinders (Old.Signature.K 𝕊₀))

open Signature 𝕊
open Laws 𝕊
open GenConstruction K GenF (λ b → b)
open import CaTTExp.Binder.SyntaxLemmas K B

closed-tel : ∀ Γ σ → T (scTel? 0 Γ) → Γ [ σ ]tel ≡ Γ
closed-tel ε            σ _ = refl
closed-tel (Γ ▸[ ms ] A) σ p =
  let (a , b) = T∧ {scTel? 0 Γ} p in cong₂ (_▸[ ms ]_) (closed-tel Γ σ a) (closed-ty A σ b)

private
  -- The four conjuncts of η's side condition after the telescope test.
  gen-ty : ∀ Γ j Δ → T (sideG (gen Γ) j Δ) → T (scTy? 0 (genTy Γ j))
  gen-ty Γ j Δ p =
    let (_ , q₁) = T∧ {isεC Δ} p
        (_ , q₂) = T∧ {is-just (P.checkCtx Γ)} q₁
        (_ , q₃) = T∧ {is-just (P.lookup Γ j)} q₂
    in fst (T∧ {scTy? 0 (genTy Γ j)} q₃)

side-stableG : ∀ b y Δ σ → LC σ → T (sideG b y Δ) → T (sideG b y (Δ [ σ ]tel))
side-stableG (frF free) y Δ σ _ p rewrite closed-tel Δ σ (snd (T∧ {y ==ℕ 0} p)) = p
side-stableG unit    y ε σ _ p = p
side-stableG (gen Γ) j ε σ _ p = p
side-stableG unit    y (_ ▸[ _ ] _) σ _ ()
side-stableG (gen Γ) j (_ ▸[ _ ] _) σ _ ()

res-stableG : ∀ b y Δ σ → LC σ → T (sideG b y Δ) → resG b y (Δ [ σ ]tel) ≡ (resG b y Δ) [ σ ]ty
res-stableG (frF _) y Δ σ _ _ = refl
res-stableG unit    y Δ σ _ _ = refl
res-stableG (gen Γ) j Δ σ _ p = sym (closed-ty (genTy Γ j) σ (gen-ty Γ j Δ p))

res-scG : ∀ b y Δ n → T (sideG b y Δ) → T (scTel? n Δ) → T (scTy? n (resG b y Δ))
res-scG (frF _) y Δ n _ _ = tt
res-scG unit    y Δ n _ _ = tt
res-scG (gen Γ) j Δ n p _ = scTy-mono n (genTy Γ j) (gen-ty Γ j Δ p)

genLaws : BinderLaws
genLaws = record
  { side-stable = side-stableG
  ; args-stable = λ _ _ _ _ _ _ → refl
  ; res-stable  = res-stableG
  ; res-sc      = res-scG
  }
