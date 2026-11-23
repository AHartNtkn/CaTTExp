------------------------------------------------------------------------
-- DES's binder interface satisfies the stability laws
-- (CaTTExp.Binder.Laws.BinderLaws), over any binder-free signature 𝕊₀.
-- So substitution and weakening are admissible for 𝕊₀ + DES with every
-- coh side condition and every stable mark judgment
-- (CaTTExp.Binder.Subst), the checker is complete
-- (CaTTExp.Binder.Completeness), and the extension is conservative
-- (CaTTExp.Binder.Embed; for plain CaTT, `Embed.CaTT 𝕊₀ (desBinders K)`,
-- and for L, CaTTExp.Gray.DesSide).
--
-- The argument telescope and the result type of a destructor mention
-- no parameter (only its own bound variables), and the telescope is
-- empty, so substitution leaves all three unchanged.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (Binders; extend)
open import CaTTExp.Binder.Des
import CaTTExp.Binder.Laws as Laws

module CaTTExp.Binder.DesLaws (𝕊₀ : Old.Signature) where

𝕊 : Signature
𝕊 = extend 𝕊₀ (desBinders (Old.Signature.K 𝕊₀))

open Signature 𝕊
open DesConstruction K DesF (λ b → b)
open Laws 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B using (LC)

private
  tyB-[] : ∀ n σ → tyB n [ σ ]ty ≡ tyB n
  tyB-[] zero    σ = refl
  tyB-[] (suc n) σ = cong (λ A → arr A (b0 (n + n)) (b0 (suc (n + n)))) (tyB-[] n σ)

  diskB-[] : ∀ n σ → diskB n [ σ ]tel ≡ diskB n
  diskB-[] zero    σ = refl
  diskB-[] (suc n) σ rewrite diskB-[] n σ | tyB-[] n σ | tyB-[] (suc n) σ = refl

  argsD-[] : ∀ n σ → argsD n [ σ ]tel ≡ argsD n
  argsD-[] n σ rewrite diskB-[] n σ | tyB-[] n σ | tyB-[] (suc n) σ = refl

  bvs-∘ : ∀ k σ → bvs k ∘ σ ≡ bvs k
  bvs-∘ zero    σ = refl
  bvs-∘ (suc k) σ = cong (_,ₛ b0 k) (bvs-∘ k σ)

  sc-tyB : ∀ m n → scTy? m (tyB n) ≡ true
  sc-tyB m zero    = refl
  sc-tyB m (suc n) rewrite sc-tyB m n = refl

  sc-bvs : ∀ m k → scSub? m (bvs k) ≡ true
  sc-bvs m zero    = refl
  sc-bvs m (suc k) rewrite sc-bvs m k = refl

  isε-[] : ∀ Δ σ → isε (Δ [ σ ]tel) ≡ isε Δ
  isε-[] ε              σ = refl
  isε-[] (_ ▸[ _ ] _)   σ = refl

  res-closed : ∀ b y Δ σ → (res b y Δ) [ σ ]ty ≡ res b y Δ
  res-closed (des _ zero)      y Δ σ = refl
  res-closed (linv (suc n))    y Δ σ rewrite tyB-[] n σ = refl
  res-closed (rinv (suc n))    y Δ σ rewrite tyB-[] n σ = refl
  res-closed (unitL (suc n))   y Δ σ rewrite tyB-[] n σ | bvs-∘ (n + n) σ | bvs-∘ (3 + (n + n)) σ = refl
  res-closed (unitR (suc n))   y Δ σ rewrite tyB-[] n σ | bvs-∘ (n + n) σ | bvs-∘ (3 + (n + n)) σ = refl

  res-sc : ∀ b y Δ m → T (scTy? m (res b y Δ))
  res-sc (des _ zero)    y Δ m = tt
  res-sc (linv (suc n))  y Δ m rewrite sc-tyB m n = tt
  res-sc (rinv (suc n))  y Δ m rewrite sc-tyB m n = tt
  res-sc (unitL (suc n)) y Δ m rewrite sc-tyB m n | sc-bvs m (n + n) | sc-bvs m (3 + (n + n)) = tt
  res-sc (unitR (suc n)) y Δ m rewrite sc-tyB m n | sc-bvs m (n + n) | sc-bvs m (3 + (n + n)) = tt

desLaws : BinderLaws
desLaws = record
  { side-stable = side-st
  ; args-stable = args-st
  ; res-stable  = λ b y Δ σ _ _ → sym (res-closed b y Δ σ)
  ; res-sc      = λ b y Δ m _ _ → res-sc b y Δ m
  }
  where
  side-st : ∀ b y Δ σ → LC σ → T (bside b y Δ) → T (bside b y (Δ [ σ ]tel))
  side-st (des _ zero)    y Δ σ _ ()
  side-st (des _ (suc n)) y Δ σ _ p rewrite isε-[] Δ σ = p

  args-st : ∀ b y Δ σ → LC σ → T (bside b y Δ) → bargs b y (Δ [ σ ]tel) ≡ (bargs b y Δ) [ σ ]tel
  args-st (des _ zero)    y Δ σ _ ()
  args-st (des _ (suc n)) y Δ σ _ _ = sym (argsD-[] n σ)
