------------------------------------------------------------------------
-- Well-typed syntax with binders is scoped (every free variable is
-- below the length of the context) and well-typed terms are locally
-- closed (no dangling bound variable).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Laws as Laws

module CaTTExp.Binder.Scoping
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.TypingWith 𝕊 side
open Laws 𝕊

------------------------------------------------------------------------
-- Local closure of terms.

mutual
  tm-lc : ∀ {Γ t A} → Γ ⊢tm t ∶ A → T (lcTm? 0 t)
  tm-lc (var-wf _ _) = tt
  tm-lc (coh-wf _ _ _ _ s) = sub-lc s
  tm-lc (cst-wf _ _) = tt
  tm-lc (bnd-wf _ l _ _ as) = ∧T l (args-lc as)

  sub-lc : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → LC σ
  sub-lc (⟨⟩-wf _) = tt
  sub-lc (,-wf s d) = ∧T (sub-lc s) (tm-lc d)

  args-lc : ∀ {Γ ts Θ} → Γ ⊢args ts ∶ Θ → LC ts
  args-lc (⟨⟩-a _) = tt
  args-lc (,-a s d) = ∧T (args-lc s) (tm-lc d)

------------------------------------------------------------------------
-- Scoping.

lookup-< : ∀ Γ i {A} → lookup Γ i ≡ just A → T (i <ℕ len Γ)
lookup-< (Γ ▸ B) i eq with i ==ℕ len Γ in e
... | true  rewrite ==→≡ i (len Γ) e = <-self (len Γ)
... | false = <-suc i (len Γ) (lookup-< Γ i eq)

module _ (closed : Closed) (laws : BinderLaws) where

  open BinderLaws laws

  mutual
    ctx-lookup : ∀ {Γ i A} → Γ ⊢ctx → lookup Γ i ≡ just A → T (i <ℕ len Γ) × T (scTy? (len Γ) A)
    ctx-lookup {Γ ▸ B} {i} {A} (▸-wf w b) eq with i ==ℕ len Γ in e
    ... | true  = ==→<suc i (len Γ) e
                , subst (λ X → T (scTy? (suc (len Γ)) X)) (just-inj eq) (scTy-suc {len Γ} B (ty-sc b))
    ... | false = let (p , a) = ctx-lookup w eq in <-suc i (len Γ) p , scTy-suc {len Γ} A a

    ty-sc : ∀ {Γ A} → Γ ⊢ty A → T (scTy? (len Γ) A)
    ty-sc (⋆-wf _)     = tt
    ty-sc (arr-wf d e) = ∧T (tm-ty-sc d) (∧T (tm-sc d) (tm-sc e))

    tm-sc : ∀ {Γ t A} → Γ ⊢tm t ∶ A → T (scTm? (len Γ) t)
    tm-sc (var-wf w eq)          = fst (ctx-lookup w eq)
    tm-sc (coh-wf _ _ _ _ s)     = fst (sub-sc s)
    tm-sc (cst-wf _ _)           = tt
    tm-sc (bnd-wf sc _ _ _ as)   = ∧T sc (args-sc as)

    tm-ty-sc : ∀ {Γ t A} → Γ ⊢tm t ∶ A → T (scTy? (len Γ) A)
    tm-ty-sc (var-wf w eq) = snd (ctx-lookup w eq)
    tm-ty-sc (coh-wf {A = A} {t} {u} {σ} _ _ a _ s) =
      let (sσ , l) = sub-sc s in
      sc-ty[] (arr A t u) σ (subst (λ n → T (scTy? n (arr A t u))) (sym l) (ty-sc a)) sσ
    tm-ty-sc {Γ} (cst-wf {k} _ _) = scTy-mono (len Γ) (ty k) (closed k)
    tm-ty-sc {Γ} (bnd-wf {b} {y} {Δ} {ts} sc _ _ ok as) =
      sc-opTy 0 ts (bres b y Δ) (args-sc as) (res-sc b y Δ (len Γ) ok sc)

    sub-sc : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → T (scSub? (len Γ) σ) × (lenₛ σ ≡ len Δ)
    sub-sc (⟨⟩-wf _)  = tt , refl
    sub-sc (,-wf s d) = let (p , l) = sub-sc s in ∧T p (tm-sc d) , cong suc l

    args-sc : ∀ {Γ ts Θ} → Γ ⊢args ts ∶ Θ → T (scSub? (len Γ) ts)
    args-sc (⟨⟩-a _)  = tt
    args-sc (,-a s d) = ∧T (args-sc s) (tm-sc d)

  sub-ctx : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → Γ ⊢ctx
  sub-ctx (⟨⟩-wf w)  = w
  sub-ctx (,-wf s _) = sub-ctx s
