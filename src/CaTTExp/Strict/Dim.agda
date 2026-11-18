------------------------------------------------------------------------
-- Dimensions of free variables (ledger item A3a).
--
-- For a derivable t : A,
--   * every free variable of t has dimension ≤ dim A, and
--   * every free variable of A has dimension < dim A.
-- The coh case uses the side condition: a coh over Δ with type
-- s →_B u has dim Δ ≤ dim B + 1, because s : B mentions a variable of
-- dimension dim Δ (coherence case) or dim Δ − 1 (operation case:
-- ∂⁻Δ contains one, CaTTExp.Strict.PsFacts.src-has).
--
-- The one hypothesis is the signature's: constants have closed types
-- (the same hypothesis as CaTTExp.Subst).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
import CaTTExp.Typing
import CaTTExp.Subst

module CaTTExp.Strict.Dim (𝕊 : Signature) (closed : CaTTExp.Subst.Closed 𝕊 (CaTTExp.Typing.cattSide 𝕊)) where

open Signature 𝕊
open import CaTTExp.Typing 𝕊
open import CaTTExp.Strict.PsFacts 𝕊
open import CaTTExp.Strict.Lambda 𝕊 using (_≤_; z≤n; s≤s; ≤-refl; ≤-trans; ≤-suc)
import CaTTExp.Subst 𝕊 cattSide as Sb
import CaTTExp.Weakening 𝕊 cattSide as Wk
open Sb using (ScTy; ScTm; ScSub)

------------------------------------------------------------------------
-- Booleans and membership.

private
  t≢f : true ≡ false → ⊥
  t≢f ()

  ∨-split : ∀ a b → (a ∨ b) ≡ true → (a ≡ true) ⊎′ (b ≡ true)
  ∨-split true  b _ = inl′ refl
  ∨-split false b p = inr′ p

  ∧-l : ∀ a b → T (a ∧ b) → T a
  ∧-l true b _ = tt

  ∧-r : ∀ a b → T (a ∧ b) → T b
  ∧-r true b p = p

  ∨-r : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
  ∨-r true  _ = refl
  ∨-r false p = p

  elem-++ˡ : ∀ v xs ys → elem v xs ≡ true → elem v (xs ++ ys) ≡ true
  elem-++ˡ v xs ys p rewrite elem-++ v xs ys | p = refl

  elem-++ʳ : ∀ v xs ys → elem v ys ≡ true → elem v (xs ++ ys) ≡ true
  elem-++ʳ v xs ys p rewrite elem-++ v xs ys = ∨-r (elem v xs) p

  elem-++-split : ∀ v xs ys → elem v (xs ++ ys) ≡ true → (elem v xs ≡ true) ⊎′ (elem v ys ≡ true)
  elem-++-split v xs ys p = ∨-split (elem v xs) (elem v ys) (trans (sym (elem-++ v xs ys)) p)

  elem-one : ∀ v i → elem v (i ∷ []) ≡ true → v ≡ i
  elem-one v i p with v ==ℕ i in e
  ... | true  = ==→≡ v i e
  ... | false = ⊥-elim (t≢f (sym p))

  no-elem-[] : ∀ v → elem v [] ≡ true → ⊥
  no-elem-[] v ()

⊆?-elem : ∀ xs ys v → T (⊆? xs ys) → elem v xs ≡ true → elem v ys ≡ true
⊆?-elem []       ys v _ ()
⊆?-elem (x ∷ xs) ys v p q with ∨-split (v ==ℕ x) (elem v xs) q
... | inl′ e rewrite ==→≡ v x e = T→≡ (∧-l (elem x ys) _ p)
... | inr′ e = ⊆?-elem xs ys v (∧-r (elem x ys) _ p) e

≈?-elem : ∀ xs ys → T (≈? xs ys) → ∀ v → elem v xs ≡ elem v ys
≈?-elem xs ys p v with elem v xs in e₁ | elem v ys in e₂
... | true  | true  = refl
... | false | false = refl
... | true  | false = ⊥-elim (t≢f (trans (sym (⊆?-elem xs ys v (∧-l (⊆? xs ys) _ p) e₁)) e₂))
... | false | true  = ⊥-elim (t≢f (trans (sym (⊆?-elem ys xs v (∧-r (⊆? xs ys) _ p) e₂)) e₁))

------------------------------------------------------------------------
-- Substitution and free variables.

dim-[] : ∀ A σ → dim (A [ σ ]ty) ≡ dim A
dim-[] ⋆           σ = refl
dim-[] (arr A t u) σ = cong suc (dim-[] A σ)

mutual
  fv-[]ty : ∀ A σ v → ScTy (lenₛ σ) A → elem v (fvTy (A [ σ ]ty)) ≡ true →
            Σ Nat λ x → (elem x (fvTy A) ≡ true) × T (x <ℕ lenₛ σ) × (elem v (fvTm (lookupₛ σ x)) ≡ true)
  fv-[]ty ⋆           σ v _ ()
  fv-[]ty (arr A t u) σ v (a , p , q) e
    with elem-++-split v (fvTy (A [ σ ]ty)) _ e
  ... | inl′ e₁ = let (x , m , l , r) = fv-[]ty A σ v a e₁ in x , elem-++ˡ x (fvTy A) _ m , l , r
  ... | inr′ e₂ with elem-++-split v (fvTm (t [ σ ]tm)) _ e₂
  ...   | inl′ e₃ = let (x , m , l , r) = fv-[]tm t σ v p e₃ in
                    x , elem-++ʳ x (fvTy A) _ (elem-++ˡ x (fvTm t) _ m) , l , r
  ...   | inr′ e₄ = let (x , m , l , r) = fv-[]tm u σ v q e₄ in
                    x , elem-++ʳ x (fvTy A) _ (elem-++ʳ x (fvTm t) _ m) , l , r

  fv-[]tm : ∀ t σ v → ScTm (lenₛ σ) t → elem v (fvTm (t [ σ ]tm)) ≡ true →
            Σ Nat λ x → (elem x (fvTm t) ≡ true) × T (x <ℕ lenₛ σ) × (elem v (fvTm (lookupₛ σ x)) ≡ true)
  fv-[]tm (var i)     σ v p e = i , cong (_∨ false) (==-refl i) , p , e
  fv-[]tm (coh Δ A τ) σ v p e = fv-∘ τ σ v p e
  fv-[]tm (cst k)     σ v _ ()

  fv-∘ : ∀ τ σ v → ScSub (lenₛ σ) τ → elem v (fvSub (τ ∘ σ)) ≡ true →
         Σ Nat λ x → (elem x (fvSub τ) ≡ true) × T (x <ℕ lenₛ σ) × (elem v (fvTm (lookupₛ σ x)) ≡ true)
  fv-∘ ⟨⟩       σ v _ ()
  fv-∘ (τ ,ₛ t) σ v (p , q) e with elem-++-split v (fvSub (τ ∘ σ)) _ e
  ... | inl′ e₁ = let (x , m , l , r) = fv-∘ τ σ v p e₁ in x , elem-++ˡ x (fvSub τ) _ m , l , r
  ... | inr′ e₂ = let (x , m , l , r) = fv-[]tm t σ v q e₂ in x , elem-++ʳ x (fvSub τ) _ m , l , r

-- Closed syntax has no free variables.
mutual
  sc0-ty : ∀ A → ScTy 0 A → fvTy A ≡ []
  sc0-ty ⋆           _           = refl
  sc0-ty (arr A t u) (a , p , q) rewrite sc0-ty A a | sc0-tm t p | sc0-tm u q = refl

  sc0-tm : ∀ t → ScTm 0 t → fvTm t ≡ []
  sc0-tm (var i)     ()
  sc0-tm (coh Δ A σ) p = sc0-sub σ p
  sc0-tm (cst k)     _ = refl

  sc0-sub : ∀ σ → ScSub 0 σ → fvSub σ ≡ []
  sc0-sub ⟨⟩       _       = refl
  sc0-sub (σ ,ₛ t) (p , q) rewrite sc0-sub σ p | sc0-tm t q = refl

------------------------------------------------------------------------
-- Contexts.

lookup-valid : ∀ {Γ i A} → Γ ⊢ctx → lookup Γ i ≡ just A → Γ ⊢ty A
lookup-valid ε-wf ()
lookup-valid {Γ ▸ B} {i} (▸-wf w b) eq with i ==ℕ len Γ
lookup-valid {Γ ▸ B} {i} (▸-wf w b) refl | true  = Wk.wk-ty b (▸-wf w b)
lookup-valid {Γ ▸ B} {i} (▸-wf w b) eq   | false = Wk.wk-ty (lookup-valid w eq) (▸-wf w b)

private
  max-l : ∀ a b → T (b <ℕ suc a) → max a b ≡ a
  max-l zero    zero    _ = refl
  max-l (suc a) zero    _ = refl
  max-l (suc a) (suc b) p = cong suc (max-l a b p)
  max-l zero    (suc b) ()

  max-r : ∀ a b → (b <ℕ suc a) ≡ false → max a b ≡ b
  max-r zero    b       _ = refl
  max-r (suc a) zero    ()
  max-r (suc a) (suc b) p = cong suc (max-r a b p)

  ≤-max-l : ∀ a b → a ≤ max a b
  ≤-max-l zero    b       = z≤n
  ≤-max-l (suc a) zero    = ≤-refl (suc a)
  ≤-max-l (suc a) (suc b) = s≤s (≤-max-l a b)

  ≤-max-r : ∀ a b → b ≤ max a b
  ≤-max-r zero    b       = ≤-refl b
  ≤-max-r (suc a) zero    = z≤n
  ≤-max-r (suc a) (suc b) = s≤s (≤-max-r a b)

-- The dimension of a non-empty context is attained.
max-attained : ∀ Γ A → Σ Nat λ w → (elem w (varsCtx (Γ ▸ A)) ≡ true) × (dimv (Γ ▸ A) w ≡ dimCtx (Γ ▸ A))
max-attained Γ A with dimCtx Γ <ℕ suc (dim A) in e
... | true  = len Γ , cong (_∨ elem (len Γ) (downFrom (len Γ))) (==-refl (len Γ)) ,
              trans (cong dimM (lookup-top Γ A)) (sym (max-l (dim A) (dimCtx Γ) (≡→T e)))
... | false = go Γ e
  where
  go : ∀ Γ → (dimCtx Γ <ℕ suc (dim A)) ≡ false →
       Σ Nat λ w → (elem w (varsCtx (Γ ▸ A)) ≡ true) × (dimv (Γ ▸ A) w ≡ dimCtx (Γ ▸ A))
  go ε       ()
  go (Γ ▸ B) e′ =
    let (w , m , d) = max-attained Γ B
        lw = elem-Below (len (Γ ▸ B)) w (varsCtx (Γ ▸ B)) (Below-downFrom (len (Γ ▸ B))) m
    in w , ∨-r (w ==ℕ len (Γ ▸ B)) m ,
       trans (dimv-wk (Γ ▸ B) A w lw) (trans d (sym (max-r (dim A) (dimCtx (Γ ▸ B)) e′)))

------------------------------------------------------------------------
-- Helpers.

ps-top : ∀ {Γ z C} → Γ ⊢ps z ∶ C → Σ Nat λ w → (elem w (varsCtx Γ) ≡ true) × (dimv Γ w ≡ dimCtx Γ)
ps-top pss                 = max-attained ε ⋆
ps-top (psd d)             = ps-top d
ps-top (pse {Γ} {x} {A} d) = max-attained (Γ ▸ A) _

∸1-< : ∀ n → T ((n ∸ 1) <ℕ suc n)
∸1-< zero    = tt
∸1-< (suc n) = <-suc n (suc n) (n<suc n)

just-inj′ : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
just-inj′ refl = refl

mutual
  sc-elem-ty : ∀ n A v → ScTy n A → elem v (fvTy A) ≡ true → T (v <ℕ n)
  sc-elem-ty n ⋆           v _ ()
  sc-elem-ty n (arr A t u) v (a , p , q) e with elem-++-split v (fvTy A) _ e
  ... | inl′ e₁ = sc-elem-ty n A v a e₁
  ... | inr′ e₂ with elem-++-split v (fvTm t) _ e₂
  ...   | inl′ e₃ = sc-elem-tm n t v p e₃
  ...   | inr′ e₄ = sc-elem-tm n u v q e₄

  sc-elem-tm : ∀ n t v → ScTm n t → elem v (fvTm t) ≡ true → T (v <ℕ n)
  sc-elem-tm n (var i)     v p e rewrite elem-one v i e = p
  sc-elem-tm n (coh Δ A σ) v p e = sc-elem-sub n σ v p e
  sc-elem-tm n (cst k)     v _ ()

  sc-elem-sub : ∀ n σ v → ScSub n σ → elem v (fvSub σ) ≡ true → T (v <ℕ n)
  sc-elem-sub n ⟨⟩       v _ ()
  sc-elem-sub n (σ ,ₛ t) v (p , q) e with elem-++-split v (fvSub σ) _ e
  ... | inl′ e₁ = sc-elem-sub n σ v p e₁
  ... | inr′ e₂ = sc-elem-tm n t v q e₂

------------------------------------------------------------------------
-- The dimension lemmas.

private
  ∸1-≤ : ∀ a b → (a ∸ 1) ≤ b → a ≤ suc b
  ∸1-≤ zero    b _ = z≤n
  ∸1-≤ (suc a) b p = s≤s (subst (_≤ b) (∸0 a) p)
    where
    ∸0 : ∀ a → a ∸ 0 ≡ a
    ∸0 zero    = refl
    ∸0 (suc a) = refl

  ≡≤ : ∀ {a b c} → a ≡ b → b ≤ c → a ≤ c
  ≡≤ refl p = p

  <→≤ : ∀ {a b} → suc a ≤ b → a ≤ b
  <→≤ (s≤s p) = ≤-suc p

  T<→≤ : ∀ a b → T (a <ℕ suc b) → a ≤ b
  T<→≤ zero    b       _ = z≤n
  T<→≤ (suc a) (suc b) p = s≤s (T<→≤ a b p)
  T<→≤ (suc a) zero    p = ⊥-elim (z a p)
    where
    z : ∀ a → T (suc a <ℕ 1) → ⊥
    z zero    ()
    z (suc a) ()

  i<lenₛ : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → lenₛ σ ≡ len Δ
  i<lenₛ s = snd (Sb.sub-sc closed s)

mutual
  dim-tm : ∀ {Γ t A} → Γ ⊢tm t ∶ A → ∀ v → elem v (fvTm t) ≡ true → dimv Γ v ≤ dim A
  dim-tm (var-wf {i} w eq) v p rewrite elem-one v i p | eq = ≤-refl _
  dim-tm (coh-wf {Δ = Δ} {A = B} {u = u} {σ = σ} pΔ wΔ (arr-wf ds du) side sσ) v p =
    ≤-trans (dim-sub sσ v p)
            (≤-trans (side-dim {u = u} pΔ wΔ ds side) (≡≤ (cong suc (sym (dim-[] B σ))) (≤-refl _)))
  dim-tm (cst-wf _ _) v ()

  dim-tyof : ∀ {Γ t A} → Γ ⊢tm t ∶ A → ∀ v → elem v (fvTy A) ≡ true → suc (dimv Γ v) ≤ dim A
  dim-tyof (var-wf w eq) v p = ctx-dims w eq v p
  dim-tyof {Γ} (coh-wf {Δ = Δ} {A = B} {t = s} {u = u} {σ = σ} pΔ wΔ a side sσ) v p =
    let l = i<lenₛ sσ
        sc = subst (λ n → ScTy n (arr B s u)) (sym l) (Sb.ty-sc closed a)
        (x , m , lx , r) = fv-[]ty (arr B s u) σ v sc p
    in ≤-trans (s≤s (dim-sub-at sσ x (subst (λ n → T (x <ℕ n)) l lx) v r))
               (≡≤ refl (subst (suc (dimv Δ x) ≤_) (cong suc (sym (dim-[] B σ))) (dim-ty a x m)))
  dim-tyof (cst-wf {k} _ _) v p rewrite sc0-ty (ty k) (closed k) = ⊥-elim (no-elem-[] v p)

  dim-ty : ∀ {Γ A} → Γ ⊢ty A → ∀ v → elem v (fvTy A) ≡ true → suc (dimv Γ v) ≤ dim A
  dim-ty (⋆-wf _) v ()
  dim-ty (arr-wf {A} {t} {u} dt du) v p with elem-++-split v (fvTy A) _ p
  ... | inl′ e₁ = ≤-suc (dim-tyof dt v e₁)
  ... | inr′ e₂ with elem-++-split v (fvTm t) _ e₂
  ...   | inl′ e₃ = s≤s (dim-tm dt v e₃)
  ...   | inr′ e₄ = s≤s (dim-tm du v e₄)

  ctx-dims : ∀ {Γ i A} → Γ ⊢ctx → lookup Γ i ≡ just A → ∀ v → elem v (fvTy A) ≡ true → suc (dimv Γ v) ≤ dim A
  ctx-dims ε-wf () v p
  ctx-dims {Γ ▸ B} {i} {A} (▸-wf w b) eq v p with i ==ℕ len Γ
  ... | true rewrite sym (just-inj′ eq) =
    ≡≤ (cong suc (dimv-wk Γ B v (sc-elem-ty (len Γ) B v (Sb.ty-sc closed b) p))) (dim-ty b v p)
  ... | false = ≡≤ (cong suc (dimv-wk Γ B v (sc-elem-ty (len Γ) A v (snd (Sb.ctx-lookup closed w eq)) p)))
                   (ctx-dims w eq v p)

  dim-sub : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → ∀ v → elem v (fvSub σ) ≡ true → dimv Γ v ≤ dimCtx Δ
  dim-sub (⟨⟩-wf _) v ()
  dim-sub (,-wf {σ = σ} {Δ = Δ} {t = t} {A = A} sσ dt) v p with elem-++-split v (fvSub σ) (fvTm t) p
  ... | inl′ e₁ = ≤-trans (dim-sub sσ v e₁) (≤-max-r (dim A) (dimCtx Δ))
  ... | inr′ e₂ = ≤-trans (dim-tm dt v e₂) (≡≤ (dim-[] A σ) (≤-max-l (dim A) (dimCtx Δ)))

  dim-sub-at : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → ∀ x → T (x <ℕ len Δ) → ∀ v →
               elem v (fvTm (lookupₛ σ x)) ≡ true → dimv Γ v ≤ dimv Δ x
  dim-sub-at (⟨⟩-wf _) x () v p
  dim-sub-at (,-wf {σ = σ} {Δ = Δ} {t = t} {A = A} sσ dt) x lx v p
    with x ==ℕ len Δ in e | i<lenₛ sσ
  ... | true  | l rewrite l | e | ==→≡ x (len Δ) e =
    ≤-trans (dim-tm dt v p) (≡≤ (dim-[] A σ) (≤-refl (dim A)))
  ... | false | l rewrite l | e =
    let lx′ = <suc-≢ x (len Δ) lx e in
    dim-sub-at sσ x lx′ v p

  dim-tmty : ∀ {Γ t A} → Γ ⊢tm t ∶ A → ∀ v → elem v (fvTmTy t A) ≡ true → dimv Γ v ≤ dim A
  dim-tmty {t = t} {A} d v p with elem-++-split v (fvTm t) (fvTy A) p
  ... | inl′ e = dim-tm d v e
  ... | inr′ e = <→≤ (dim-tyof d v e)

  side-dim : ∀ {Δ B s u} → Δ ⊢ps → Δ ⊢ctx → Δ ⊢tm s ∶ B → T (cattSide Δ B s u) → dimCtx Δ ≤ suc (dim B)
  side-dim {Δ} {B} {s} {u} (ps d) wΔ ds side with isCoh Δ B s u in ec
  ... | true =
    let (w , m , dw) = ps-top d
        m′ = trans (≈?-elem (fvTmTy s B) (varsCtx Δ) (∧-l (≈? (fvTmTy s B) (varsCtx Δ)) _ (≡→T ec)) w) m
    in ≤-suc (≡≤ (sym dw) (dim-tmty ds w m′))
  ... | false =
    let i = dimCtx Δ ∸ 1
        (w , m , dw) = src-has d i (∸1-< (dimCtx Δ))
        m′ = trans (≈?-elem (fvTmTy s B) (∂⁻ Δ) (∧-l (≈? (fvTmTy s B) (∂⁻ Δ)) _ side) w) m
    in ∸1-≤ (dimCtx Δ) (dim B) (≡≤ (sym dw) (dim-tmty ds w m′))

------------------------------------------------------------------------
-- Lists of variables.

lookup-just : ∀ Γ w → T (w <ℕ len Γ) → Σ Ty λ A → lookup Γ w ≡ just A
lookup-just (Γ ▸ B) w p with w ==ℕ len Γ in e
... | true  = B , refl
... | false = lookup-just Γ w (<suc-≢ w (len Γ) p e)

elem-downFrom : ∀ n w → T (w <ℕ n) → elem w (downFrom n) ≡ true
elem-downFrom (suc n) w p with w ==ℕ n in e
... | true  = refl
... | false = elem-downFrom n w (<suc-≢ w n p e)

nodup-downFrom : ∀ n → NoDup (downFrom n)
nodup-downFrom zero    = tt
nodup-downFrom (suc n) = Below-elem n (downFrom n) (Below-downFrom n) , nodup-downFrom n

fvSub-at : ∀ τ x v → T (x <ℕ lenₛ τ) → elem v (fvTm (lookupₛ τ x)) ≡ true → elem v (fvSub τ) ≡ true
fvSub-at (τ ,ₛ t) x v p q with x ==ℕ lenₛ τ in e
... | true  rewrite elem-++ v (fvSub τ) (fvTm t) | q = ∨-true′ (elem v (fvSub τ))
  where
  ∨-true′ : ∀ a → (a ∨ true) ≡ true
  ∨-true′ true  = refl
  ∨-true′ false = refl
... | false rewrite elem-++ v (fvSub τ) (fvTm t) | fvSub-at τ x v (<suc-≢ x (lenₛ τ) p e) q = refl

fvSub-split : ∀ τ v → elem v (fvSub τ) ≡ true →
              Σ Nat λ x → T (x <ℕ lenₛ τ) × (elem v (fvTm (lookupₛ τ x)) ≡ true)
fvSub-split ⟨⟩       v ()
fvSub-split (τ ,ₛ t) v p with elem v (fvSub τ) in e
... | true = let (x , l , m) = fvSub-split τ v e in
             x , <-suc x (lenₛ τ) l , trans (cong (λ s → elem v (fvTm s)) (skip x l)) m
  where
  skip : ∀ x → T (x <ℕ lenₛ τ) → lookupₛ (τ ,ₛ t) x ≡ lookupₛ τ x
  skip x l rewrite <→≢ x (lenₛ τ) l = refl
... | false = lenₛ τ , n<suc (lenₛ τ) , trans (cong (λ s → elem v (fvTm s)) top-is) p′
  where
  top-is : lookupₛ (τ ,ₛ t) (lenₛ τ) ≡ t
  top-is rewrite ==-refl (lenₛ τ) = refl
  p′ : elem v (fvTm t) ≡ true
  p′ = trans (sym (cong (false ∨_) refl)) (trans (cong (_∨ elem v (fvTm t)) (sym e)) (trans (sym (elem-++ v (fvSub τ) (fvTm t))) p))

