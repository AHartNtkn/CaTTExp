------------------------------------------------------------------------
-- Closing free variables into bound variables, and honest arity
-- contexts (ledger S27 (b); used by CaTTExp.Binder.HonestHeads and
-- CaTTExp.Binder.HeadSpec). Purely syntactic: parameterised by the
-- sets of constants and formers only, so a binder interface can be
-- *defined* with it before its signature exists.
------------------------------------------------------------------------
open import CaTTExp.Prelude

module CaTTExp.Binder.Close (K : Set) (B : Set) where

open import CaTTExp.Binder.Syntax K B
open import CaTTExp.Binder.SyntaxLemmas K B

-- Closing: free variable j becomes the bound variable j of the binder
-- at depth d. Bound variables already present (which, in locally
-- closed syntax, refer to binders inside the term) are left alone.

mutual
  clTy : Nat → Ty → Ty
  clTy d ⋆           = ⋆
  clTy d (arr A t u) = arr (clTy d A) (clTm d t) (clTm d u)

  clTm : Nat → Tm → Tm
  clTm d (var j)       = bvar d j
  clTm d (bvar e j)    = bvar e j
  clTm d (coh Θ A τ)   = coh Θ A (clSub d τ)
  clTm d (cst k)       = cst k
  clTm d (bnd b y Δ τ) = bnd b y (clTel (suc d) Δ) (clSub d τ)

  clTel : Nat → Ctx → Ctx
  clTel d ε             = ε
  clTel d (Δ ▸[ ms ] A) = clTel d Δ ▸[ ms ] clTy d A

  clSub : Nat → Sub → Sub
  clSub d ⟨⟩       = ⟨⟩
  clSub d (τ ,ₛ t) = clSub d τ ,ₛ clTm d t

len-clTel : ∀ d Δ → len (clTel d Δ) ≡ len Δ
len-clTel d ε             = refl
len-clTel d (Δ ▸[ _ ] _) = cong suc (len-clTel d Δ)

-- Closed syntax has no free variable.
mutual
  sc-clTy : ∀ d A → T (scTy? 0 (clTy d A))
  sc-clTy d ⋆           = tt
  sc-clTy d (arr A t u) = ∧T (sc-clTy d A) (∧T (sc-clTm d t) (sc-clTm d u))

  sc-clTm : ∀ d t → T (scTm? 0 (clTm d t))
  sc-clTm d (var j)       = tt
  sc-clTm d (bvar e j)    = tt
  sc-clTm d (coh Θ A τ)   = sc-clSub d τ
  sc-clTm d (cst k)       = tt
  sc-clTm d (bnd b y Δ τ) = ∧T (sc-clTel (suc d) Δ) (sc-clSub d τ)

  sc-clTel : ∀ d Δ → T (scTel? 0 (clTel d Δ))
  sc-clTel d ε             = tt
  sc-clTel d (Δ ▸[ _ ] A) = ∧T (sc-clTel d Δ) (sc-clTy d A)

  sc-clSub : ∀ d τ → T (scSub? 0 (clSub d τ))
  sc-clSub d ⟨⟩       = tt
  sc-clSub d (τ ,ₛ t) = ∧T (sc-clSub d τ) (sc-clTm d t)

------------------------------------------------------------------------
-- Opening the closure is substitution.

private
  pickOr-lookup : ∀ ts j t → T (j <ℕ lenₛ ts) → pickOr ts j t ≡ lookupₛ ts j
  pickOr-lookup (ts ,ₛ s) j t p with j ==ℕ lenₛ ts in e
  ... | true  = refl
  ... | false = pickOr-lookup ts j t (<suc-≢ j (lenₛ ts) p e)

  <→≢′ : ∀ e d → T (e <ℕ d) → (e ==ℕ d) ≡ false
  <→≢′ = <→≢

mutual
  open-clTy : ∀ d ts A → LC ts → T (scTy? (lenₛ ts) A) → T (lcTy? d A) →
              opTy d ts (clTy d A) ≡ A [ ts ]ty
  open-clTy d ts ⋆ _ _ _ = refl
  open-clTy d ts (arr A t u) l p q =
    let (a , p′) = T∧ {scTy? (lenₛ ts) A} p ; (b , c) = T∧ {scTm? (lenₛ ts) t} p′
        (a′ , q′) = T∧ {lcTy? d A} q ; (b′ , c′) = T∧ {lcTm? d t} q′ in
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (open-clTy d ts A l a a′) (cong₂ _,_ (open-clTm d ts t l b b′) (open-clTm d ts u l c c′))

  open-clTm : ∀ d ts t → LC ts → T (scTm? (lenₛ ts) t) → T (lcTm? d t) →
              opTm d ts (clTm d t) ≡ t [ ts ]tm
  open-clTm d ts (var j) l p _ rewrite ==-refl d = pickOr-lookup ts j (bvar d j) p
  open-clTm d ts (bvar e j) l _ q rewrite <→≢′ e d q = refl
  open-clTm d ts (coh Θ A τ) l p q = cong (coh Θ A) (open-clSub d ts τ l p q)
  open-clTm d ts (cst k) _ _ _ = refl
  open-clTm d ts (bnd b y Δ τ) l p q =
    let (a , c) = T∧ {scTel? (lenₛ ts) Δ} p ; (a′ , c′) = T∧ {lcTel? (suc d) Δ} q in
    cong₂ (bnd b y)
      (trans (cong (λ ρ → opTel (suc d) ρ (clTel (suc d) Δ)) (shSub-lc 0 ts (lc-ts ts l)))
             (open-clTel (suc d) ts Δ l a a′))
      (open-clSub d ts τ l c c′)
    where
    lc-ts : ∀ ts → LC ts → T (lcSub? 0 ts)
    lc-ts ts l = l

  open-clTel : ∀ d ts Δ → LC ts → T (scTel? (lenₛ ts) Δ) → T (lcTel? d Δ) →
               opTel d ts (clTel d Δ) ≡ Δ [ ts ]tel
  open-clTel d ts ε _ _ _ = refl
  open-clTel d ts (Δ ▸[ ms ] A) l p q =
    let (a , b) = T∧ {scTel? (lenₛ ts) Δ} p ; (a′ , b′) = T∧ {lcTel? d Δ} q in
    cong₂ (_▸[ ms ]_) (open-clTel d ts Δ l a a′) (open-clTy d ts A l b b′)

  open-clSub : ∀ d ts τ → LC ts → T (scSub? (lenₛ ts) τ) → T (lcSub? d τ) →
               opSub d ts (clSub d τ) ≡ τ ∘ ts
  open-clSub d ts ⟨⟩ _ _ _ = refl
  open-clSub d ts (τ ,ₛ t) l p q =
    let (a , b) = T∧ {scSub? (lenₛ ts) τ} p ; (a′ , b′) = T∧ {lcSub? d τ} q in
    cong₂ _,ₛ_ (open-clSub d ts τ l a a′) (open-clTm d ts t l b b′)

------------------------------------------------------------------------
-- Honest arity contexts: entry k mentions only the variables before it
-- and no bound variable.

Honest : Ctx → Set
Honest ε             = ⊤
Honest (G ▸[ _ ] A) = Honest G × T (scTy? (len G) A) × T (lcTy? 0 A)

-- Its Boolean test.
honest? : Ctx → Bool
honest? ε             = true
honest? (G ▸[ _ ] A) = honest? G ∧ scTy? (len G) A ∧ lcTy? 0 A

honest?-sound : ∀ G → T (honest? G) → Honest G
honest?-sound ε             _ = tt
honest?-sound (G ▸[ _ ] A) p =
  let (a , q) = T∧ {honest? G} p ; (b , c) = T∧ {scTy? (len G) A} q in
  honest?-sound G a , b , c

