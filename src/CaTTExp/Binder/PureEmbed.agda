------------------------------------------------------------------------
-- Pure CaTT derivations embed into the binder kernel, for any
-- signature, coh side condition and mark judgment, provided the side
-- condition accepts what pure CaTT's does on embedded syntax
-- (`SidePure`; for plain CaTT's side it is CaTTExp.Binder.PureSide.
-- cattSide-pure). Embedded contexts are unmarked, so no mark premise
-- arises.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM
import CaTTExp.Pure as P

module CaTTExp.Binder.PureEmbed
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (mark : Signature.Ctx 𝕊 → BM.Mark → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.Binder.TypingWith 𝕊 side mark

SidePure : Set
SidePure = ∀ Δ A t u → T (P.cattSide Δ A t u) → T (side (embCtx Δ) (embTy A) (embTm t) (embTm u))

-- Embedding commutes with lookup and substitution.
len-emb : ∀ Γ → len (embCtx Γ) ≡ P.len Γ
len-emb P.ε       = refl
len-emb (Γ P.▸ _) = cong suc (len-emb Γ)

private
  just-inj : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
  just-inj refl = refl

lookup-emb : ∀ Γ i {A} → P.lookup Γ i ≡ just A → lookup (embCtx Γ) i ≡ just (embTy A)
lookup-emb P.ε       i ()
lookup-emb (Γ P.▸ B) i e rewrite len-emb Γ with i ==ℕ P.len Γ
... | true  = cong (λ X → just (embTy X)) (just-inj e)
... | false = lookup-emb Γ i e

mutual
  emb-[]ty : ∀ A σ → embTy (A P.[ σ ]ty) ≡ embTy A [ embSub σ ]ty
  emb-[]ty P.⋆           σ = refl
  emb-[]ty (P.arr A t u) σ rewrite emb-[]ty A σ | emb-[]tm t σ | emb-[]tm u σ = refl

  emb-[]tm : ∀ t σ → embTm (t P.[ σ ]tm) ≡ embTm t [ embSub σ ]tm
  emb-[]tm (P.var i)     σ = lk i σ
    where
    lk : ∀ i σ → embTm (P.lookupₛ σ i) ≡ lookupₛ (embSub σ) i
    lk i P.⟨⟩       = refl
    lk i (σ P.,ₛ t) with i ==ℕ P.lenₛ σ in e
    ... | true  rewrite lenₛ-emb σ | e = refl
    ... | false rewrite lenₛ-emb σ | e = lk i σ
  emb-[]tm (P.coh Q B τ) σ = cong (coh (embCtx Q) (embTy B)) (emb-∘ τ σ)
  emb-[]tm (P.cst ())    σ

  emb-∘ : ∀ τ σ → embSub (τ P.∘ σ) ≡ embSub τ ∘ embSub σ
  emb-∘ P.⟨⟩       σ = refl
  emb-∘ (τ P.,ₛ t) σ rewrite emb-∘ τ σ | emb-[]tm t σ = refl

  lenₛ-emb : ∀ σ → lenₛ (embSub σ) ≡ P.lenₛ σ
  lenₛ-emb P.⟨⟩       = refl
  lenₛ-emb (σ P.,ₛ _) = cong suc (lenₛ-emb σ)

ps-emb₀ : ∀ {Δ} → Δ P.⊢ps → embCtx Δ ⊢ps
ps-emb₀ {Δ} (P.ps d) = Δ , toPure-ps d , P.ps d

module _ (sp : SidePure) where
  mutual
    ctx-emb : ∀ {Γ} → Γ P.⊢ctx → embCtx Γ ⊢ctx
    ctx-emb P.ε-wf       = ε-wf
    ctx-emb (P.▸-wf w a) = ▸-wf (ctx-emb w) (ty-emb a)

    ty-emb : ∀ {Γ A} → Γ P.⊢ty A → embCtx Γ ⊢ty embTy A
    ty-emb (P.⋆-wf w)     = ⋆-wf (ctx-emb w)
    ty-emb (P.arr-wf d e) = arr-wf (tm-emb d) (tm-emb e)

    tm-emb : ∀ {Γ t A} → Γ P.⊢tm t ∶ A → embCtx Γ ⊢tm embTm t ∶ embTy A
    tm-emb {Γ} (P.var-wf {i = i} w e) = var-wf (ctx-emb w) (lookup-emb Γ i e)
    tm-emb {Γ} (P.coh-wf {Δ} {A} {t} {u} {σ} p w a s γ) =
      subst (embCtx Γ ⊢tm coh (embCtx Δ) (embTy (P.arr A t u)) (embSub σ) ∶_) (sym (emb-[]ty (P.arr A t u) σ))
        (coh-wf (ps-emb₀ p) (ctx-emb w) (ty-emb a) (sp Δ A t u s) (sub-emb γ))
    tm-emb (P.cst-wf {k = ()} _ _)

    sub-emb : ∀ {Γ σ Δ} → Γ P.⊢sub σ ∶ Δ → embCtx Γ ⊢sub embSub σ ∶ embCtx Δ
    sub-emb (P.⟨⟩-wf w)    = ⟨⟩-wf (ctx-emb w)
    sub-emb {Γ} (P.,-wf {σ = σ} {t = t} {A = A} γ d) =
      ,-wf (sub-emb γ) (subst (embCtx Γ ⊢tm embTm t ∶_) (emb-[]ty A σ) (tm-emb d)) tt
