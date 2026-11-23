------------------------------------------------------------------------
-- Pasting contexts for the syntax with binders.
--
-- A pasting context is built from ⋆, arr and variables only, so it is
-- pure CaTT syntax. Rather than restate Finster–Mimram's judgment, we
-- reuse it: Δ ⊢ps holds when Δ is the image of a pure context Δ₀
-- (CaTTExp.Pure, no constants) with Δ₀ ⊢ps. `toPure` recognises that
-- image, so the judgment is decided by CaTTExp.PastingCheck.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Pure as P
import CaTTExp.Pasting
import CaTTExp.PastingCheck

module CaTTExp.Binder.Pasting (𝕊 : Signature) where

open Signature 𝕊
open CaTTExp.Pasting P.∅ using () renaming (_⊢ps to _⊢ps₀)
open CaTTExp.PastingCheck P.∅ using () renaming (checkPs to checkPs₀; checkPs-complete to checkPs₀-complete)

------------------------------------------------------------------------
-- The embedding of pure syntax, and its partial inverse.

mutual
  embTy : P.Ty → Ty
  embTy P.⋆           = ⋆
  embTy (P.arr A t u) = arr (embTy A) (embTm t) (embTm u)

  embTm : P.Tm → Tm
  embTm (P.var i)     = var i
  embTm (P.coh Γ A σ) = coh (embCtx Γ) (embTy A) (embSub σ)
  embTm (P.cst ())

  embCtx : P.Ctx → Ctx
  embCtx P.ε       = ε
  embCtx (Γ P.▸ A) = embCtx Γ ▸ embTy A

  embSub : P.Sub → Sub
  embSub P.⟨⟩       = ⟨⟩
  embSub (σ P.,ₛ t) = embSub σ ,ₛ embTm t

-- Pasting contexts only need ⋆, arr and variables.
toPureTm : Tm → Maybe P.Tm
toPureTm (var i) = just (P.var i)
toPureTm _       = nothing

toPureTy : Ty → Maybe P.Ty
toPureTy ⋆           = just P.⋆
toPureTy (arr A t u) =
  toPureTy A >>= λ A₀ → toPureTm t >>= λ t₀ → toPureTm u >>= λ u₀ → just (P.arr A₀ t₀ u₀)

toPure : Ctx → Maybe P.Ctx
toPure ε       = just P.ε
toPure (Γ ▸ A) = toPure Γ >>= λ Γ₀ → toPureTy A >>= λ A₀ → just (Γ₀ P.▸ A₀)
-- Pasting contexts are unmarked.
toPure (Γ ▸[ _ ∷ _ ] A) = nothing

private
  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  bind-just : ∀ {a b} {A : Set a} {Z : Set b} (m : Maybe A) (f : A → Maybe Z) {z} →
              (m >>= f) ≡ just z → Σ A λ x → (m ≡ just x) × (f x ≡ just z)
  bind-just (just x) f e = x , refl , e

toPureTm-sound : ∀ t {t₀} → toPureTm t ≡ just t₀ → embTm t₀ ≡ t
toPureTm-sound (var i) refl = refl
toPureTm-sound (bvar _ _) ()
toPureTm-sound (coh _ _ _) ()
toPureTm-sound (cst _) ()
toPureTm-sound (bnd _ _ _ _) ()

toPureTy-sound : ∀ A {A₀} → toPureTy A ≡ just A₀ → embTy A₀ ≡ A
toPureTy-sound ⋆ refl = refl
toPureTy-sound (arr A t u) e
  with bind-just (toPureTy A) _ e
... | A₀ , eA , e₁ with bind-just (toPureTm t) _ e₁
... | t₀ , et , e₂ with bind-just (toPureTm u) _ e₂
... | u₀ , eu , refl =
  cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
    (toPureTy-sound A eA) (cong₂ _,_ (toPureTm-sound t et) (toPureTm-sound u eu))

toPure-sound : ∀ Γ {Γ₀} → toPure Γ ≡ just Γ₀ → embCtx Γ₀ ≡ Γ
toPure-sound ε refl = refl
toPure-sound (Γ ▸ A) e with bind-just (toPure Γ) _ e
... | Γ₀ , eΓ , e₁ with bind-just (toPureTy A) _ e₁
... | A₀ , eA , refl = cong₂ _▸_ (toPure-sound Γ eΓ) (toPureTy-sound A eA)
toPure-sound (Γ ▸[ _ ∷ _ ] A) ()

-- Pasting contexts are built from variables (CaTTExp.Pasting), so
-- toPure succeeds on their images.
private
  data PureVarTy : P.Ty → Set where
    ⋆-pv   : PureVarTy P.⋆
    arr-pv : ∀ {A i j} → PureVarTy A → PureVarTy (P.arr A (P.var i) (P.var j))

  toPureTy-emb : ∀ {A} → PureVarTy A → toPureTy (embTy A) ≡ just A
  toPureTy-emb ⋆-pv = refl
  toPureTy-emb (arr-pv p) rewrite toPureTy-emb p = refl

  open import CaTTExp.Pasting P.∅ using (_⊢ps_∶_; pss; pse; psd; ps)

  ps-var-ty : ∀ {Γ x A} → Γ ⊢ps x ∶ A → PureVarTy A
  ps-var-ty pss     = ⋆-pv
  ps-var-ty (pse d) = arr-pv (ps-var-ty d)
  ps-var-ty (psd d) with ps-var-ty d
  ... | arr-pv p = p

toPure-ps : ∀ {Γ x A} → Γ ⊢ps x ∶ A → toPure (embCtx Γ) ≡ just Γ
toPure-ps pss = refl
toPure-ps (pse {Γ} {x} {A} d)
  rewrite toPure-ps d | toPureTy-emb (ps-var-ty d) = refl
toPure-ps (psd d) = toPure-ps d

------------------------------------------------------------------------
-- The judgment and its decision procedure.

infix 4 _⊢ps

_⊢ps : Ctx → Set
Δ ⊢ps = Σ P.Ctx λ Δ₀ → (toPure Δ ≡ just Δ₀) × (Δ₀ ⊢ps₀)

ps-emb : ∀ {Δ} → Δ ⊢ps → Σ P.Ctx λ Δ₀ → embCtx Δ₀ ≡ Δ
ps-emb {Δ} (Δ₀ , e , _) = Δ₀ , toPure-sound Δ e

checkPsWith : (Δ : Ctx) (m : Maybe P.Ctx) → toPure Δ ≡ m → Maybe (Δ ⊢ps)
checkPsWith Δ nothing   _ = nothing
checkPsWith Δ (just Δ₀) e = checkPs₀ Δ₀ >>= λ p → just (Δ₀ , e , p)

checkPs : (Δ : Ctx) → Maybe (Δ ⊢ps)
checkPs Δ = checkPsWith Δ (toPure Δ) refl

checkPs-complete : ∀ {Δ} → Δ ⊢ps → T (is-just (checkPs Δ))
checkPs-complete {Δ} (Δ₀ , e , p) = go (toPure Δ) refl e
  where
  ok : ∀ {a b} {A : Set a} {Z : Set b} (m : Maybe A) (f : A → Maybe Z) →
       T (is-just m) → (∀ x → T (is-just (f x))) → T (is-just (m >>= f))
  ok (just x) f _ k = k x
  go : (m : Maybe P.Ctx) (e′ : toPure Δ ≡ m) → m ≡ just Δ₀ →
       T (is-just (checkPsWith Δ m e′))
  go .(just Δ₀) e′ refl = ok (checkPs₀ Δ₀) _ (checkPs₀-complete p) λ _ → tt
