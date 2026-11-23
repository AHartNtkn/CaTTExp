------------------------------------------------------------------------
-- The stability laws of the Gray object formers' binder interface
-- (CaTTExp.Binder.GrayForm), former by former, over any set B of
-- formers into which they inject (`inj`): the fields of
-- CaTTExp.Binder.Laws.BinderLaws for them. The telescope is empty and
-- the arity context (A B : ⋆) and the result type ⋆ mention nothing,
-- so substitution leaves all three unchanged.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.GrayForm

module CaTTExp.Binder.GrayFormLawsGen (K B : Set) (inj : GBF → B) where

open import CaTTExp.Binder.Syntax K B
open GrayFormConstruction K B inj
open import CaTTExp.Binder.SyntaxLemmas K B using (LC)

isε-[] : ∀ Δ σ → isε (Δ [ σ ]tel) ≡ isε Δ
isε-[] ε            σ = refl
isε-[] (_ ▸[ _ ] _) σ = refl

side-stableG : ∀ b y Δ σ → LC σ → T (side b y Δ) → T (side b y (Δ [ σ ]tel))
side-stableG b y Δ σ _ p rewrite isε-[] Δ σ = p

args-stableG : ∀ b y Δ σ → LC σ → T (side b y Δ) → args b y (Δ [ σ ]tel) ≡ (args b y Δ) [ σ ]tel
args-stableG b y Δ σ _ _ = refl

res-stableG : ∀ b y Δ σ → LC σ → T (side b y Δ) → res b y (Δ [ σ ]tel) ≡ (res b y Δ) [ σ ]ty
res-stableG b y Δ σ _ _ = refl

res-scG : ∀ b y Δ m → T (side b y Δ) → T (scTel? m Δ) → T (scTy? m (res b y Δ))
res-scG b y Δ m _ _ = tt

-- For the presupposition law: the arity context is scoped anywhere.
bargs-scG : ∀ b y Δ n → T (side b y Δ) → T (scTel? n Δ) → T (scTel? n (args b y Δ))
bargs-scG b y Δ n _ _ = tt

-- The side condition forces the empty telescope and selector 0.
side-ε : ∀ b y Δ → T (side b y Δ) → Δ ≡ ε
side-ε b y ε            _ = refl
side-ε b y (_ ▸[ _ ] _) p with y ==ℕ 0
side-ε b y (_ ▸[ _ ] _) () | true
side-ε b y (_ ▸[ _ ] _) () | false
