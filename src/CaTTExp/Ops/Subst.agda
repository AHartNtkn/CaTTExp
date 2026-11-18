------------------------------------------------------------------------
-- Admissibility of substitution for CaTT with declared operations
-- (CaTTExp.Ops.Typing):
--
--   Γ ⊢ t ∶ A   and   Δ ⊢ σ ∶ Γ   imply   Δ ⊢ t[σ] ∶ A[σ]
--
-- Hypotheses: the signature's constants have closed types (`Closed`,
-- as in CaTTExp.Subst), and every declared operation (Δ, B) is scoped:
-- each type of Δ mentions only earlier variables, and B only variables
-- of Δ (`OpsScoped`). Both are checkable on the declaration.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Ops.Subst
  (𝕊 : Signature)
  (ops : List (Σ (Signature.Ctx 𝕊) (λ _ → Signature.Ty 𝕊)))
  where

open Signature 𝕊
open import CaTTExp.Typing 𝕊 using (cattSide)
open import CaTTExp.Ops.Typing 𝕊 ops
open import CaTTExp.Subst 𝕊 cattSide
  using (ScTy; ScTm; ScSub; Closed; scTy-suc; scTy-mono; lookupₛ-∘;
         ext-ty; assoc-ty; closed-ty; sc-ty[])

private
  <-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc zero    (suc n) _ = tt
  <-suc (suc i) (suc n) p = <-suc i n p

  ==→<suc : ∀ i n → (i ==ℕ n) ≡ true → T (i <ℕ suc n)
  ==→<suc zero    zero    _ = tt
  ==→<suc (suc i) (suc n) p = ==→<suc i n p
  ==→<suc zero    (suc n) ()
  ==→<suc (suc i) zero    ()

  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

ScCtx : Ctx → Set
ScCtx ε       = ⊤
ScCtx (Γ ▸ A) = ScCtx Γ × ScTy (len Γ) A

OpsScoped : Set
OpsScoped = ∀ {Δ B} → (Δ , B) ∈ ops → ScCtx Δ × ScTy (len Δ) B

module _ (closed : Closed) (opsSc : OpsScoped) where

  mutual
    ctx-lookup : ∀ {Γ i A} → Γ ⊢ctx → lookup Γ i ≡ just A → T (i <ℕ len Γ) × ScTy (len Γ) A
    ctx-lookup {Γ ▸ B} {i} (▸-wf w b) eq with i ==ℕ len Γ in e
    ... | true  = ==→<suc i (len Γ) e
                , subst (ScTy (suc (len Γ))) (just-inj eq) (scTy-suc B (ty-sc b))
    ... | false = let (p , a) = ctx-lookup w eq in <-suc i (len Γ) p , scTy-suc _ a

    ty-sc : ∀ {Γ A} → Γ ⊢ty A → ScTy (len Γ) A
    ty-sc (⋆-wf _)     = tt
    ty-sc (arr-wf d e) = tm-ty-sc d , tm-sc d , tm-sc e

    tm-sc : ∀ {Γ t A} → Γ ⊢tm t ∶ A → ScTm (len Γ) t
    tm-sc (var-wf w eq)      = fst (ctx-lookup w eq)
    tm-sc (coh-wf _ _ _ _ s) = fst (sub-sc s)
    tm-sc (cst-wf _ _)       = tt
    tm-sc (op-wf _ s)        = fst (sub-sc s)

    tm-ty-sc : ∀ {Γ t A} → Γ ⊢tm t ∶ A → ScTy (len Γ) A
    tm-ty-sc (var-wf w eq) = snd (ctx-lookup w eq)
    tm-ty-sc (coh-wf {A = A} {t} {u} {σ} _ _ a _ s) =
      let (sσ , l) = sub-sc s in
      sc-ty[] (arr A t u) σ (subst (λ n → ScTy n (arr A t u)) (sym l) (ty-sc a)) sσ
    tm-ty-sc {Γ} (cst-wf {k} _ _) = scTy-mono (len Γ) (ty k) (closed k)
    tm-ty-sc (op-wf {B = B} {σ} m s) =
      let (sσ , l) = sub-sc s in
      sc-ty[] B σ (subst (λ n → ScTy n B) (sym l) (snd (opsSc m))) sσ

    sub-sc : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → ScSub (len Γ) σ × (lenₛ σ ≡ len Δ)
    sub-sc (⟨⟩-wf _)  = tt , refl
    sub-sc (,-wf s d) = let (p , l) = sub-sc s in (p , tm-sc d) , cong suc l

  ctx-sc : ∀ {Γ} → Γ ⊢ctx → ScCtx Γ
  ctx-sc ε-wf       = tt
  ctx-sc (▸-wf w a) = ctx-sc w , ty-sc a

  sub-ctx : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → Γ ⊢ctx
  sub-ctx (⟨⟩-wf w)  = w
  sub-ctx (,-wf s _) = sub-ctx s

  lookup-sub : ∀ {Γ Δ σ i A} → Γ ⊢ctx → lookup Γ i ≡ just A →
               Δ ⊢sub σ ∶ Γ → Δ ⊢tm lookupₛ σ i ∶ A [ σ ]ty
  lookup-sub {Γ ▸ B} {Δ} {σ ,ₛ s} {i} {A} (▸-wf w b) eq (,-wf sd d)
    with sub-sc sd
  ... | (_ , l) with i ==ℕ len Γ in e
  ...   | true  rewrite l | e =
          subst (λ X → Δ ⊢tm s ∶ X [ σ ,ₛ s ]ty) (just-inj eq)
            (subst (Δ ⊢tm s ∶_)
              (sym (ext-ty B σ s (subst (λ n → ScTy n B) (sym l) (ty-sc b)))) d)
  ...   | false rewrite l | e =
          subst (Δ ⊢tm lookupₛ σ i ∶_)
            (sym (ext-ty A σ s (subst (λ n → ScTy n A) (sym l) (snd (ctx-lookup w eq)))))
            (lookup-sub w eq sd)

  private
    tyAt : ∀ {Γ τ Θ} B → Γ ⊢sub τ ∶ Θ → ScTy (len Θ) B → ScTy (lenₛ τ) B
    tyAt B sτ p = subst (λ n → ScTy n B) (sym (snd (sub-sc sτ))) p

  mutual
    tm[] : ∀ {Γ Δ t A σ} → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Δ ⊢tm t [ σ ]tm ∶ A [ σ ]ty
    tm[] (var-wf w eq) s = lookup-sub w eq s
    tm[] {Δ = Δ} {σ = σ} (coh-wf {Δ = Θ} {A} {t} {u} {τ} p w a ok sτ) s =
      subst (Δ ⊢tm coh Θ (arr A t u) (τ ∘ σ) ∶_)
        (sym (assoc-ty (arr A t u) τ σ (tyAt (arr A t u) sτ (ty-sc a))))
        (coh-wf p w a ok (sub∘ (ctx-sc w) sτ s))
    tm[] {Δ = Δ} {σ = σ} (cst-wf {k} _ v) s =
      subst (Δ ⊢tm cst k ∶_) (sym (closed-ty (ty k) σ (closed k))) (cst-wf (sub-ctx s) v)
    tm[] {Δ = Δ} {σ = σ} (op-wf {Θ} {B} {τ} m sτ) s =
      subst (Δ ⊢tm coh Θ B (τ ∘ σ) ∶_)
        (sym (assoc-ty B τ σ (tyAt B sτ (snd (opsSc m)))))
        (op-wf m (sub∘ (fst (opsSc m)) sτ s))

    ty[] : ∀ {Γ Δ A σ} → Γ ⊢ty A → Δ ⊢sub σ ∶ Γ → Δ ⊢ty A [ σ ]ty
    ty[] (⋆-wf _)     s = ⋆-wf (sub-ctx s)
    ty[] (arr-wf d e) s = arr-wf (tm[] d s) (tm[] e s)

    sub∘ : ∀ {Θ Γ Δ τ σ} → ScCtx Θ → Γ ⊢sub τ ∶ Θ → Δ ⊢sub σ ∶ Γ → Δ ⊢sub τ ∘ σ ∶ Θ
    sub∘ _ (⟨⟩-wf _) s = ⟨⟩-wf (sub-ctx s)
    sub∘ {Θ ▸ A} {Δ = Δ} {τ ,ₛ t} {σ} (w , a) (,-wf sτ d) s =
      ,-wf (sub∘ w sτ s)
        (subst (Δ ⊢tm t [ σ ]tm ∶_)
          (assoc-ty A τ σ (subst (λ n → ScTy n A) (sym (snd (sub-sc sτ))) a))
          (tm[] d s))
