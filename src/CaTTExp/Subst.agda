------------------------------------------------------------------------
-- Admissibility of substitution, for every side condition.
--
--   Γ ⊢ t ∶ A   and   Δ ⊢ σ ∶ Γ   imply   Δ ⊢ t[σ] ∶ A[σ]
--
-- The proof never inspects the side condition: a coh's side condition
-- is about its own pasting context Δ and type, and substitution only
-- acts on the coh's argument substitution. So the theorem holds for
-- plain CaTT (CaTTExp.Typing) and two-tier L (CaTTExp.Gray.Typing)
-- alike, and for any other side condition of the same shape.
--
-- The one hypothesis is that the signature's constants have closed
-- types (`Closed`); pure CaTT (the empty signature) satisfies it
-- trivially. Without it the theorem is false: a constant whose type
-- mentions var 0 keeps that type after substitution.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Subst
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.TypingWith 𝕊 side

------------------------------------------------------------------------
-- Arithmetic on the builtin boolean comparisons.

private
  <-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc zero    (suc n) _ = tt
  <-suc (suc i) (suc n) p = <-suc i n p

  <→≢ : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
  <→≢ zero    (suc n) _ = refl
  <→≢ (suc i) (suc n) p = <→≢ i n p

  <suc-≢ : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
  <suc-≢ zero    zero    _ ()
  <suc-≢ zero    (suc n) _ _ = tt
  <suc-≢ (suc i) zero    p _ = ⊥-elim (no-<0 i p)
    where
    no-<0 : ∀ i → T (i <ℕ zero) → ⊥
    no-<0 _ ()
  <suc-≢ (suc i) (suc n) p q = <suc-≢ i n p q

  ==→<suc : ∀ i n → (i ==ℕ n) ≡ true → T (i <ℕ suc n)
  ==→<suc zero    zero    _ = tt
  ==→<suc (suc i) (suc n) p = ==→<suc i n p
  ==→<suc zero    (suc n) ()
  ==→<suc (suc i) zero    ()

  ==→≡ : ∀ i n → (i ==ℕ n) ≡ true → i ≡ n
  ==→≡ i n p = ==ℕ-sound i n (subst T (sym p) tt)

  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

------------------------------------------------------------------------
-- Scoping: every variable is below n.

mutual
  ScTy : Nat → Ty → Set
  ScTy n ⋆           = ⊤
  ScTy n (arr A t u) = ScTy n A × ScTm n t × ScTm n u

  ScTm : Nat → Tm → Set
  ScTm n (var i)     = T (i <ℕ n)
  ScTm n (coh _ _ σ) = ScSub n σ
  ScTm n (cst _)     = ⊤

  ScSub : Nat → Sub → Set
  ScSub n ⟨⟩       = ⊤
  ScSub n (σ ,ₛ t) = ScSub n σ × ScTm n t

-- The signature hypothesis.
Closed : Set
Closed = ∀ k → ScTy 0 (ty k)

mutual
  scTy-suc : ∀ {n} A → ScTy n A → ScTy (suc n) A
  scTy-suc ⋆           _           = tt
  scTy-suc (arr A t u) (a , p , q) = scTy-suc A a , scTm-suc t p , scTm-suc u q

  scTm-suc : ∀ {n} t → ScTm n t → ScTm (suc n) t
  scTm-suc {n} (var i) p = <-suc i n p
  scTm-suc (coh _ _ σ) p = scSub-suc σ p
  scTm-suc (cst _)     _ = tt

  scSub-suc : ∀ {n} σ → ScSub n σ → ScSub (suc n) σ
  scSub-suc ⟨⟩       _       = tt
  scSub-suc (σ ,ₛ t) (p , q) = scSub-suc σ p , scTm-suc t q

scTy-mono : ∀ n A → ScTy 0 A → ScTy n A
scTy-mono zero    A p = p
scTy-mono (suc n) A p = scTy-suc A (scTy-mono n A p)

------------------------------------------------------------------------
-- Substitution lemmas on raw syntax.

lenₛ-∘ : ∀ τ σ → lenₛ (τ ∘ σ) ≡ lenₛ τ
lenₛ-∘ ⟨⟩       σ = refl
lenₛ-∘ (τ ,ₛ t) σ = cong suc (lenₛ-∘ τ σ)

lookupₛ-∘ : ∀ τ σ i → T (i <ℕ lenₛ τ) → lookupₛ (τ ∘ σ) i ≡ lookupₛ τ i [ σ ]tm
lookupₛ-∘ (τ ,ₛ t) σ i p rewrite lenₛ-∘ τ σ with i ==ℕ lenₛ τ in eq
... | true  = refl
... | false = lookupₛ-∘ τ σ i (<suc-≢ i (lenₛ τ) p eq)

-- Extending a substitution does not change terms scoped below it.
mutual
  ext-ty : ∀ A σ s → ScTy (lenₛ σ) A → A [ σ ,ₛ s ]ty ≡ A [ σ ]ty
  ext-ty ⋆           σ s _           = refl
  ext-ty (arr A t u) σ s (a , p , q) =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (ext-ty A σ s a) (cong₂ _,_ (ext-tm t σ s p) (ext-tm u σ s q))

  ext-tm : ∀ t σ s → ScTm (lenₛ σ) t → t [ σ ,ₛ s ]tm ≡ t [ σ ]tm
  ext-tm (var i)     σ s p rewrite <→≢ i (lenₛ σ) p = refl
  ext-tm (coh Δ A τ) σ s p = cong (coh Δ A) (ext-sub τ σ s p)
  ext-tm (cst k)     σ s _ = refl

  ext-sub : ∀ τ σ s → ScSub (lenₛ σ) τ → τ ∘ (σ ,ₛ s) ≡ τ ∘ σ
  ext-sub ⟨⟩       σ s _       = refl
  ext-sub (τ ,ₛ t) σ s (p , q) = cong₂ _,ₛ_ (ext-sub τ σ s p) (ext-tm t σ s q)

-- Associativity of substitution.
mutual
  assoc-ty : ∀ A τ σ → ScTy (lenₛ τ) A → A [ τ ]ty [ σ ]ty ≡ A [ τ ∘ σ ]ty
  assoc-ty ⋆           τ σ _           = refl
  assoc-ty (arr A t u) τ σ (a , p , q) =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (assoc-ty A τ σ a) (cong₂ _,_ (assoc-tm t τ σ p) (assoc-tm u τ σ q))

  assoc-tm : ∀ t τ σ → ScTm (lenₛ τ) t → t [ τ ]tm [ σ ]tm ≡ t [ τ ∘ σ ]tm
  assoc-tm (var i)     τ σ p = sym (lookupₛ-∘ τ σ i p)
  assoc-tm (coh Δ A ρ) τ σ p = cong (coh Δ A) (assoc-sub ρ τ σ p)
  assoc-tm (cst k)     τ σ _ = refl

  assoc-sub : ∀ ρ τ σ → ScSub (lenₛ τ) ρ → (ρ ∘ τ) ∘ σ ≡ ρ ∘ (τ ∘ σ)
  assoc-sub ⟨⟩       τ σ _       = refl
  assoc-sub (ρ ,ₛ t) τ σ (p , q) = cong₂ _,ₛ_ (assoc-sub ρ τ σ p) (assoc-tm t τ σ q)

-- Closed syntax is fixed by substitution.
mutual
  closed-ty : ∀ A σ → ScTy 0 A → A [ σ ]ty ≡ A
  closed-ty ⋆           σ _           = refl
  closed-ty (arr A t u) σ (a , p , q) =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (closed-ty A σ a) (cong₂ _,_ (closed-tm t σ p) (closed-tm u σ q))

  closed-tm : ∀ t σ → ScTm 0 t → t [ σ ]tm ≡ t
  closed-tm (var i)     σ ()
  closed-tm (coh Δ A ρ) σ p = cong (coh Δ A) (closed-sub ρ σ p)
  closed-tm (cst k)     σ _ = refl

  closed-sub : ∀ ρ σ → ScSub 0 ρ → ρ ∘ σ ≡ ρ
  closed-sub ⟨⟩       σ _       = refl
  closed-sub (ρ ,ₛ t) σ (p , q) = cong₂ _,ₛ_ (closed-sub ρ σ p) (closed-tm t σ q)

-- Substituting a scoped substitution preserves scoping.
mutual
  sc-ty[] : ∀ {n} A σ → ScTy (lenₛ σ) A → ScSub n σ → ScTy n (A [ σ ]ty)
  sc-ty[] ⋆           σ _           _ = tt
  sc-ty[] (arr A t u) σ (a , p , q) s = sc-ty[] A σ a s , sc-tm[] t σ p s , sc-tm[] u σ q s

  sc-tm[] : ∀ {n} t σ → ScTm (lenₛ σ) t → ScSub n σ → ScTm n (t [ σ ]tm)
  sc-tm[] (var i)     σ p s = sc-lookup σ i p s
  sc-tm[] (coh Δ A ρ) σ p s = sc-∘ ρ σ p s
  sc-tm[] (cst k)     σ _ _ = tt

  sc-∘ : ∀ {n} ρ σ → ScSub (lenₛ σ) ρ → ScSub n σ → ScSub n (ρ ∘ σ)
  sc-∘ ⟨⟩       σ _       _ = tt
  sc-∘ (ρ ,ₛ t) σ (p , q) s = sc-∘ ρ σ p s , sc-tm[] t σ q s

  sc-lookup : ∀ {n} σ i → T (i <ℕ lenₛ σ) → ScSub n σ → ScTm n (lookupₛ σ i)
  sc-lookup (σ ,ₛ t) i p (s , q) with i ==ℕ lenₛ σ in eq
  ... | true  = q
  ... | false = sc-lookup σ i (<suc-≢ i (lenₛ σ) p eq) s

------------------------------------------------------------------------
-- Well-typed syntax is scoped.

module _ (closed : Closed) where

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
    tm-sc (var-wf w eq)       = fst (ctx-lookup w eq)
    tm-sc (coh-wf _ _ _ _ s)  = fst (sub-sc s)
    tm-sc (cst-wf _ _)        = tt

    tm-ty-sc : ∀ {Γ t A} → Γ ⊢tm t ∶ A → ScTy (len Γ) A
    tm-ty-sc (var-wf w eq) = snd (ctx-lookup w eq)
    tm-ty-sc {Γ} (coh-wf {A = A} {t} {u} {σ} _ _ a _ s) =
      let (sσ , l) = sub-sc s in
      sc-ty[] (arr A t u) σ (subst (λ n → ScTy n (arr A t u)) (sym l) (ty-sc a)) sσ
    tm-ty-sc {Γ} (cst-wf {k} _ _) = scTy-mono (len Γ) (ty k) (closed k)

    sub-sc : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → ScSub (len Γ) σ × (lenₛ σ ≡ len Δ)
    sub-sc (⟨⟩-wf _)  = tt , refl
    sub-sc (,-wf s d) = let (p , l) = sub-sc s in (p , tm-sc d) , cong suc l

  sub-ctx : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → Γ ⊢ctx
  sub-ctx (⟨⟩-wf w)  = w
  sub-ctx (,-wf s _) = sub-ctx s

  ----------------------------------------------------------------------
  -- Variables.

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

  ----------------------------------------------------------------------
  -- The theorem.

  mutual
    tm[] : ∀ {Γ Δ t A σ} → Γ ⊢tm t ∶ A → Δ ⊢sub σ ∶ Γ → Δ ⊢tm t [ σ ]tm ∶ A [ σ ]ty
    tm[] (var-wf w eq) s = lookup-sub w eq s
    tm[] {Δ = Δ} {σ = σ} (coh-wf {Δ = Θ} {A} {t} {u} {τ} p w a ok sτ) s =
      subst (Δ ⊢tm coh Θ (arr A t u) (τ ∘ σ) ∶_)
        (sym (assoc-ty (arr A t u) τ σ
               (subst (λ n → ScTy n (arr A t u)) (sym (snd (sub-sc sτ))) (ty-sc a))))
        (coh-wf p w a ok (sub∘ w sτ s))
    tm[] {Δ = Δ} {σ = σ} (cst-wf {k} _ v) s =
      subst (Δ ⊢tm cst k ∶_) (sym (closed-ty (ty k) σ (closed k))) (cst-wf (sub-ctx s) v)

    ty[] : ∀ {Γ Δ A σ} → Γ ⊢ty A → Δ ⊢sub σ ∶ Γ → Δ ⊢ty A [ σ ]ty
    ty[] (⋆-wf _)     s = ⋆-wf (sub-ctx s)
    ty[] (arr-wf d e) s = arr-wf (tm[] d s) (tm[] e s)

    -- Composition of substitutions.
    sub∘ : ∀ {Θ Γ Δ τ σ} → Θ ⊢ctx → Γ ⊢sub τ ∶ Θ → Δ ⊢sub σ ∶ Γ → Δ ⊢sub τ ∘ σ ∶ Θ
    sub∘ _ (⟨⟩-wf _) s = ⟨⟩-wf (sub-ctx s)
    sub∘ {Θ ▸ A} {Δ = Δ} {τ ,ₛ t} {σ} (▸-wf w a) (,-wf sτ d) s =
      ,-wf (sub∘ w sτ s)
        (subst (Δ ⊢tm t [ σ ]tm ∶_)
          (assoc-ty A τ σ (subst (λ n → ScTy n A) (sym (snd (sub-sc sτ))) (ty-sc a)))
          (tm[] d s))
