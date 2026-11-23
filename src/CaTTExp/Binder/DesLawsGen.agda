------------------------------------------------------------------------
-- The stability laws of DES's binder interface, former by former, over
-- any set B of formers into which DES injects (`inj`): the fields of
-- CaTTExp.Binder.Laws.BinderLaws for DES (CaTTExp.Binder.DesLaws) and
-- for DES beside INIT (CaTTExp.Binder.InitDes). The argument telescope
-- and the result type of a destructor mention no parameter, and the
-- telescope is empty, so substitution leaves all three unchanged.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Des

module CaTTExp.Binder.DesLawsGen (K B : Set) (inj : DesF → B) where

open import CaTTExp.Binder.Syntax K B
open DesConstruction K B inj
open import CaTTExp.Binder.SyntaxLemmas K B using (LC)

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


side-stableD : ∀ b y Δ σ → LC σ → T (side b y Δ) → T (side b y (Δ [ σ ]tel))
side-stableD (des _ zero)    y Δ σ _ ()
side-stableD (des _ (suc n)) y Δ σ _ p rewrite isε-[] Δ σ = p

args-stableD : ∀ b y Δ σ → LC σ → T (side b y Δ) → args b y (Δ [ σ ]tel) ≡ (args b y Δ) [ σ ]tel
args-stableD (des _ zero)    y Δ σ _ ()
args-stableD (des _ (suc n)) y Δ σ _ _ = sym (argsD-[] n σ)

res-stableD : ∀ b y Δ σ → LC σ → T (side b y Δ) → res b y (Δ [ σ ]tel) ≡ (res b y Δ) [ σ ]ty
res-stableD b y Δ σ _ _ = sym (res-closed b y Δ σ)

res-scD : ∀ b y Δ m → T (side b y Δ) → T (scTel? m Δ) → T (scTy? m (res b y Δ))
res-scD b y Δ m _ _ = res-sc b y Δ m
