------------------------------------------------------------------------
-- Admissibility of substitution for CaTT with truncation marks
-- (CaTTExp.Trunc.Typing):
--
--   Γ ∣ M ⊢ t ∶ A,   Δ ∣ N ⊢ σ ∶ Γ,   σ respects marks (Resp M N σ)
--   ⟹   Δ ∣ N ⊢ t[σ] ∶ A[σ]
--
-- Resp is T-var's certificate: every variable marked m in Γ goes to a
-- variable marked at most m in Δ (T-cum). Without it the theorem is
-- false: substituting an unmarked object for a set would keep fillers
-- that the target context does not have.
--
-- The raw-syntax lemmas are those of CaTTExp.Subst. The typed part is
-- the same proof with three more cases, one per truncation rule.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Trunc.Subst (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Typing 𝕊 using (cattSide)
open import CaTTExp.Trunc.Typing 𝕊
open import CaTTExp.Subst 𝕊 cattSide
  using (ScTy; ScTm; ScSub; Closed; scTy-suc; scTy-mono; lookupₛ-∘;
         ext-ty; assoc-ty; closed-ty; sc-ty[])

------------------------------------------------------------------------
-- Arithmetic.

private
  <-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc zero    (suc n) _ = tt
  <-suc (suc i) (suc n) p = <-suc i n p

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

  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  lt-plus : ∀ a x → T (x <ℕ suc (a + x))
  lt-plus zero    zero    = tt
  lt-plus zero    (suc x) = lt-plus zero x
  lt-plus (suc a) x       = <-suc x (suc (a + x)) (lt-plus a x)

  -- a ≤ b, b ≤ c ⟹ a ≤ c, with ≤ as < suc.
  ≤-trans : ∀ a b c → T (a <ℕ suc b) → T (b <ℕ suc c) → T (a <ℕ suc c)
  ≤-trans zero    b       c       _ _ = tt
  ≤-trans (suc a) (suc b) (suc c) p q = ≤-trans a b c p q
  ≤-trans (suc a) zero    c       () _
  ≤-trans (suc a) (suc b) zero    _ q = ⊥-elim (no b q)
    where
    no : ∀ b → T (suc b <ℕ 1) → ⊥
    no zero    ()
    no (suc b) ()

scTy-up : ∀ a {n} A → ScTy n A → ScTy (a + n) A
scTy-up zero    A p = p
scTy-up (suc a) A p = scTy-suc A (scTy-up a A p)

------------------------------------------------------------------------
-- Scoping of contexts, and of the three generic contexts.

ScCtx : Ctx → Set
ScCtx ε       = ⊤
ScCtx (Γ ▸ A) = ScCtx Γ × ScTy (len Γ) A

lenTF : ∀ k → len (TF k) ≡ suc (suc (suc (suc (dbl k))))
lenTF zero    = refl
lenTF (suc k) = cong (λ n → suc (suc n)) (lenTF k)

sc-globe : ∀ j → ScTy (suc (suc (dbl j))) (globeTy j)
sc-globe zero    = tt , tt , tt
sc-globe (suc j) = scTy-up 2 (globeTy j) (sc-globe j) , lt-plus 1 (dbl j) , lt-plus 0 (suc (dbl j))

sc-TF : ∀ k → ScCtx (TF k)
sc-TF zero    = (((tt , tt) , tt) , sc-globe 0) , scTy-suc {2} (globeTy 0) (sc-globe 0)
sc-TF (suc k) =
  let g = subst (λ n → ScTy n (globeTy (suc k))) (sym (lenTF k)) (sc-globe (suc k)) in
  (sc-TF k , g) , scTy-suc (globeTy (suc k)) g

sc-TFty : ∀ k → ScTy (len (TF k)) (TFty k)
sc-TFty k = subst (λ n → ScTy n (TFty k)) (sym (lenTF k))
  (scTy-up 2 (globeTy k) (sc-globe k) , lt-plus 1 (dbl k) , lt-plus 0 (suc (suc (suc (dbl k)))))

sc-TI : ∀ j → ScCtx (TI j)
sc-TI j = sc-TF j , subst (λ n → ScTy n (globeTy (suc j))) (sym (lenTF j)) (sc-globe (suc j))

sc-TIty : ∀ j → ScTy (len (TI j)) (TIty j)
sc-TIty j = subst (λ n → ScTy (suc n) (TIty j)) (sym (lenTF j))
  (scTy-up 3 (globeTy j) (sc-globe j) , lt-plus 1 (suc (suc (dbl j))) , lt-plus 2 (suc (suc (dbl j))))

sc-TC : ScCtx TC
sc-TC = (tt , tt) , tt

sc-TCty : ScTy (len TC) TCty
sc-TCty = tt , tt , tt

-- C (variable 1) is in range.
one<TF : ∀ k → T (1 <ℕ len (TF k))
one<TF zero    = tt
one<TF (suc k) = tt

one<TI : ∀ j → T (1 <ℕ len (TI j))
one<TI zero    = tt
one<TI (suc j) = tt

------------------------------------------------------------------------
-- Marks are transported by mark-respecting substitutions.

mark-sub : ∀ M N t σ j → Resp M N σ → T (allows (markOf M t) j) →
           T (allows (markOf N (t [ σ ]tm)) j)
mark-sub M N (var i) σ j r p with M i in eq
... | just m with markOf N (lookupₛ σ i) | r i m eq
...   | just m' | q = ≤-trans m' m j q p
...   | nothing | ()
mark-sub M N (var i) σ j r () | nothing
mark-sub M N (coh _ _ _) σ j r ()
mark-sub M N (cst _)     σ j r ()

objOf-∘ : ∀ τ σ → T (1 <ℕ lenₛ τ) → objOf (τ ∘ σ) ≡ objOf τ [ σ ]tm
objOf-∘ τ σ p = lookupₛ-∘ τ σ 1 p

------------------------------------------------------------------------
-- Well-typed syntax is scoped.

module _ (closed : Closed) where

  mutual
    ctx-lookup : ∀ {Γ M i A} → Γ ∣ M ⊢ctx → lookup Γ i ≡ just A → T (i <ℕ len Γ) × ScTy (len Γ) A
    ctx-lookup {Γ ▸ B} {i = i} (▸-wf w b) eq with i ==ℕ len Γ in e
    ... | true  = ==→<suc i (len Γ) e
                , subst (ScTy (suc (len Γ))) (just-inj eq) (scTy-suc B (ty-sc b))
    ... | false = let (p , a) = ctx-lookup w eq in <-suc i (len Γ) p , scTy-suc _ a

    ty-sc : ∀ {Γ M A} → Γ ∣ M ⊢ty A → ScTy (len Γ) A
    ty-sc (⋆-wf _)     = tt
    ty-sc (arr-wf d e) = tm-ty-sc d , tm-sc d , tm-sc e

    tm-sc : ∀ {Γ M t A} → Γ ∣ M ⊢tm t ∶ A → ScTm (len Γ) t
    tm-sc (var-wf w eq)      = fst (ctx-lookup w eq)
    tm-sc (coh-wf _ _ _ _ s) = fst (sub-sc s)
    tm-sc (cst-wf _ _)       = tt
    tm-sc (tfill-wf s _)     = fst (sub-sc s)
    tm-sc (tinv-wf s _)      = fst (sub-sc s)
    tm-sc (tctr-wf s _)      = fst (sub-sc s)

    tm-ty-sc : ∀ {Γ M t A} → Γ ∣ M ⊢tm t ∶ A → ScTy (len Γ) A
    tm-ty-sc (var-wf w eq) = snd (ctx-lookup w eq)
    tm-ty-sc (coh-wf {A = A} {t} {u} {σ} _ _ a _ s) =
      let (sσ , l) = sub-sc s in
      sc-ty[] (arr A t u) σ (subst (λ n → ScTy n (arr A t u)) (sym l) (ty-sc a)) sσ
    tm-ty-sc {Γ} (cst-wf {k} _ _) = scTy-mono (len Γ) (ty k) (closed k)
    tm-ty-sc (tfill-wf {k} {σ} s _) =
      let (sσ , l) = sub-sc s in
      sc-ty[] (TFty k) σ (subst (λ n → ScTy n (TFty k)) (sym l) (sc-TFty k)) sσ
    tm-ty-sc (tinv-wf {j} {σ} s _) =
      let (sσ , l) = sub-sc s in
      sc-ty[] (TIty j) σ (subst (λ n → ScTy n (TIty j)) (sym l) (sc-TIty j)) sσ
    tm-ty-sc (tctr-wf {σ} s _) =
      let (sσ , l) = sub-sc s in
      sc-ty[] TCty σ (subst (λ n → ScTy n TCty) (sym l) sc-TCty) sσ

    sub-sc : ∀ {Γ M σ Δ} → Γ ∣ M ⊢sub σ ∶ Δ → ScSub (len Γ) σ × (lenₛ σ ≡ len Δ)
    sub-sc (⟨⟩-wf _)  = tt , refl
    sub-sc (,-wf s d) = let (p , l) = sub-sc s in (p , tm-sc d) , cong suc l

  ctx-sc : ∀ {Γ M} → Γ ∣ M ⊢ctx → ScCtx Γ
  ctx-sc ε-wf       = tt
  ctx-sc (▸-wf w a) = ctx-sc w , ty-sc a

  sub-ctx : ∀ {Γ M σ Δ} → Γ ∣ M ⊢sub σ ∶ Δ → Γ ∣ M ⊢ctx
  sub-ctx (⟨⟩-wf w)  = w
  sub-ctx (,-wf s _) = sub-ctx s

  ----------------------------------------------------------------------
  -- Variables.

  lookup-sub : ∀ {Γ M Δ N σ i A} → Γ ∣ M ⊢ctx → lookup Γ i ≡ just A →
               Δ ∣ N ⊢sub σ ∶ Γ → Δ ∣ N ⊢tm lookupₛ σ i ∶ A [ σ ]ty
  lookup-sub {Γ ▸ B} {Δ = Δ} {N} {σ ,ₛ s} {i} {A} (▸-wf w b) eq (,-wf sd d)
    with sub-sc sd
  ... | (_ , l) with i ==ℕ len Γ in e
  ...   | true  rewrite l | e =
          subst (λ X → Δ ∣ N ⊢tm s ∶ X [ σ ,ₛ s ]ty) (just-inj eq)
            (subst (Δ ∣ N ⊢tm s ∶_)
              (sym (ext-ty B σ s (subst (λ n → ScTy n B) (sym l) (ty-sc b)))) d)
  ...   | false rewrite l | e =
          subst (Δ ∣ N ⊢tm lookupₛ σ i ∶_)
            (sym (ext-ty A σ s (subst (λ n → ScTy n A) (sym l) (snd (ctx-lookup w eq)))))
            (lookup-sub w eq sd)

  ----------------------------------------------------------------------
  -- The theorem.

  private
    tyAt : ∀ {Γ M τ Θ} B → Γ ∣ M ⊢sub τ ∶ Θ → ScTy (len Θ) B → ScTy (lenₛ τ) B
    tyAt B sτ p = subst (λ n → ScTy n B) (sym (snd (sub-sc sτ))) p

    objOk : ∀ {Γ M N τ σ Θ} j → Γ ∣ M ⊢sub τ ∶ Θ → T (1 <ℕ len Θ) → Resp M N σ →
            T (allows (markOf M (objOf τ)) j) → T (allows (markOf N (objOf (τ ∘ σ))) j)
    objOk {M = M} {N = N} {τ} {σ} j sτ one r ok =
      subst (λ x → T (allows (markOf N x) j))
        (sym (objOf-∘ τ σ (subst (λ n → T (1 <ℕ n)) (sym (snd (sub-sc sτ))) one)))
        (mark-sub M N (objOf τ) σ j r ok)

  mutual
    tm[] : ∀ {Γ M Δ N t A σ} → Γ ∣ M ⊢tm t ∶ A → Δ ∣ N ⊢sub σ ∶ Γ → Resp M N σ →
           Δ ∣ N ⊢tm t [ σ ]tm ∶ A [ σ ]ty
    tm[] (var-wf w eq) s r = lookup-sub w eq s
    tm[] {Δ = Δ} {N} {σ = σ} (coh-wf {Δ = Θ} {A} {t} {u} {τ} p w a ok sτ) s r =
      subst (Δ ∣ N ⊢tm coh Θ (arr A t u) (τ ∘ σ) ∶_)
        (sym (assoc-ty (arr A t u) τ σ (tyAt (arr A t u) sτ (ty-sc a))))
        (coh-wf p w a ok (sub∘ (ctx-sc w) sτ s r))
    tm[] {Δ = Δ} {N} {σ = σ} (cst-wf {k} _ v) s r =
      subst (Δ ∣ N ⊢tm cst k ∶_) (sym (closed-ty (ty k) σ (closed k))) (cst-wf (sub-ctx s) v)
    tm[] {Δ = Δ} {N} {σ = σ} (tfill-wf {k} {τ} sτ ok) s r =
      subst (Δ ∣ N ⊢tm coh (TF k) (TFty k) (τ ∘ σ) ∶_)
        (sym (assoc-ty (TFty k) τ σ (tyAt (TFty k) sτ (sc-TFty k))))
        (tfill-wf (sub∘ (sc-TF k) sτ s r) (objOk (suc k) sτ (one<TF k) r ok))
    tm[] {Δ = Δ} {N} {σ = σ} (tinv-wf {j} {τ} sτ ok) s r =
      subst (Δ ∣ N ⊢tm coh (TI j) (TIty j) (τ ∘ σ) ∶_)
        (sym (assoc-ty (TIty j) τ σ (tyAt (TIty j) sτ (sc-TIty j))))
        (tinv-wf (sub∘ (sc-TI j) sτ s r) (objOk (suc (suc j)) sτ (one<TI j) r ok))
    tm[] {Δ = Δ} {N} {σ = σ} (tctr-wf {τ} sτ ok) s r =
      subst (Δ ∣ N ⊢tm coh TC TCty (τ ∘ σ) ∶_)
        (sym (assoc-ty TCty τ σ (tyAt TCty sτ sc-TCty)))
        (tctr-wf (sub∘ sc-TC sτ s r) (objOk 0 sτ tt r ok))

    ty[] : ∀ {Γ M Δ N A σ} → Γ ∣ M ⊢ty A → Δ ∣ N ⊢sub σ ∶ Γ → Resp M N σ → Δ ∣ N ⊢ty A [ σ ]ty
    ty[] (⋆-wf _)     s r = ⋆-wf (sub-ctx s)
    ty[] (arr-wf d e) s r = arr-wf (tm[] d s r) (tm[] e s r)

    -- Composition of substitutions.
    sub∘ : ∀ {Θ Γ M Δ N τ σ} → ScCtx Θ → Γ ∣ M ⊢sub τ ∶ Θ → Δ ∣ N ⊢sub σ ∶ Γ → Resp M N σ →
           Δ ∣ N ⊢sub τ ∘ σ ∶ Θ
    sub∘ _ (⟨⟩-wf _) s r = ⟨⟩-wf (sub-ctx s)
    sub∘ {Θ ▸ A} {Δ = Δ} {N} {τ ,ₛ t} {σ} (w , a) (,-wf sτ d) s r =
      ,-wf (sub∘ w sτ s r)
        (subst (Δ ∣ N ⊢tm t [ σ ]tm ∶_)
          (assoc-ty A τ σ (subst (λ n → ScTy n A) (sym (snd (sub-sc sτ))) a))
          (tm[] d s r))
