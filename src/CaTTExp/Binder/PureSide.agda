------------------------------------------------------------------------
-- Pure syntax (CaTTExp.Pure, no constants) inside the syntax of any
-- signature with binders (CaTTExp.Binder.Pasting's embTy, embTm,
-- embCtx): the operations plain CaTT's side condition is made of
-- commute with the embedding, so the binder kernel's `cattSide` agrees
-- with pure CaTT's on embedded syntax (`cattSide-pure`). Facts proved
-- for pure CaTT's side condition (CaTTExp.Derived) thus transfer to
-- every binder signature.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Pure as P

module CaTTExp.Binder.PureSide (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Binder.Pasting 𝕊 using (embTy; embTm; embCtx; embSub)
import CaTTExp.Binder.Typing 𝕊 as NT

len-p : ∀ Γ → len (embCtx Γ) ≡ P.len Γ
len-p P.ε       = refl
len-p (Γ P.▸ _) = cong suc (len-p Γ)

dim-p : ∀ A → dim (embTy A) ≡ P.dim A
dim-p P.⋆           = refl
dim-p (P.arr A _ _) = cong suc (dim-p A)

dimCtx-p : ∀ Γ → dimCtx (embCtx Γ) ≡ P.dimCtx Γ
dimCtx-p P.ε       = refl
dimCtx-p (Γ P.▸ A) rewrite dim-p A | dimCtx-p Γ = refl

mutual
  fvTy-p : ∀ A → fvTy (embTy A) ≡ P.fvTy A
  fvTy-p P.⋆ = refl
  fvTy-p (P.arr A t u) rewrite fvTy-p A | fvTm-p t | fvTm-p u = refl

  fvTm-p : ∀ t → fvTm (embTm t) ≡ P.fvTm t
  fvTm-p (P.var i)     = refl
  fvTm-p (P.coh _ _ σ) = fvSub-p σ
  fvTm-p (P.cst ())

  fvSub-p : ∀ σ → fvSub (embSub σ) ≡ P.fvSub σ
  fvSub-p P.⟨⟩ = refl
  fvSub-p (σ P.,ₛ t) rewrite fvSub-p σ | fvTm-p t = refl

fvTmTy-p : ∀ t A → fvTmTy (embTm t) (embTy A) ≡ P.fvTmTy t A
fvTmTy-p t A rewrite fvTm-p t | fvTy-p A = refl

downFrom-p : ∀ n → downFrom n ≡ P.downFrom n
downFrom-p zero    = refl
downFrom-p (suc n) = cong (n ∷_) (downFrom-p n)

varsCtx-p : ∀ Γ → varsCtx (embCtx Γ) ≡ P.varsCtx Γ
varsCtx-p Γ = trans (cong downFrom (len-p Γ)) (downFrom-p (P.len Γ))

srcVars-p : ∀ i Γ → srcVars i (embCtx Γ) ≡ P.srcVars i Γ
srcVars-p i P.ε                 = refl
srcVars-p i (P.ε P.▸ _)         = refl
srcVars-p i (Γ P.▸ A P.▸ _) rewrite dim-p A | len-p Γ | srcVars-p i Γ = refl

dropLast-p : ∀ xs → dropLastᴸ xs ≡ P.dropLastᴸ xs
dropLast-p []           = refl
dropLast-p (x ∷ [])     = refl
dropLast-p (x ∷ y ∷ xs) = cong (x ∷_) (dropLast-p (y ∷ xs))

tgtVars-p : ∀ i Γ → tgtVars i (embCtx Γ) ≡ P.tgtVars i Γ
tgtVars-p i P.ε                 = refl
tgtVars-p i (P.ε P.▸ _)         = refl
tgtVars-p i (Γ P.▸ A P.▸ _) rewrite dim-p A | len-p Γ | tgtVars-p i Γ | dropLast-p (P.tgtVars i Γ) = refl

∂⁻-p : ∀ Γ → ∂⁻ (embCtx Γ) ≡ P.∂⁻ Γ
∂⁻-p Γ rewrite dimCtx-p Γ = srcVars-p _ Γ

∂⁺-p : ∀ Γ → ∂⁺ (embCtx Γ) ≡ P.∂⁺ Γ
∂⁺-p Γ rewrite dimCtx-p Γ = tgtVars-p _ Γ

cattSide-pure : ∀ Δ A t u → NT.cattSide (embCtx Δ) (embTy A) (embTm t) (embTm u) ≡ P.cattSide Δ A t u
cattSide-pure Δ A t u
  rewrite fvTmTy-p t A | fvTmTy-p u A | varsCtx-p Δ | ∂⁻-p Δ | ∂⁺-p Δ = refl
