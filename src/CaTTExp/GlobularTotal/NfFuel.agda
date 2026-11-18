------------------------------------------------------------------------
-- F2c, infrastructure for the coh case of (1′): fuel, depth, and
-- weakening of substitutions.
--
--   nf-det     : nf is independent of the fuel where it succeeds
--   nf-≥       : more fuel keeps a result
--   depth-look : an argument is no deeper than its substitution
--   dim-sub    : substitution keeps dimension
--   sub-len    : Γ ⊢ σ : Δ has one term per variable of Δ
--   tm-weak    : a term of Δ ignores terms of σ past len Δ
--   tm-scope   : the variables of a typed term and of its type are in
--                scope (likewise ctx-, ty-, sub-scope, sub-comp)
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.NfFuel where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; nf; depthTm; depthSub)
open import CaTTExp.GlobularTotal.NfSub using (nf-+)

private
  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

  +-zero : ∀ a → a + 0 ≡ a
  +-zero zero    = refl
  +-zero (suc a) = cong suc (+-zero a)

  +-comm : ∀ a b → a + b ≡ b + a
  +-comm zero    b = sym (+-zero b)
  +-comm (suc a) b = trans (cong suc (+-comm a b)) (sym (+-suc b a))

  le-split : ∀ a b → T (a <ℕ suc b) → Σ Nat λ i → b ≡ i + a
  le-split zero    b       p = b , sym (+-zero b)
  le-split (suc a) zero    ()
  le-split (suc a) (suc b) p with le-split a b p
  ... | i , e = i , trans (cong suc e) (sym (+-suc i a))

nf-det : ∀ k k' Γ t a b → nf k Γ t ≡ just a → nf k' Γ t ≡ just b → a ≡ b
nf-det k k' Γ t a b ea eb =
  just-inj (trans (sym (nf-+ k' k Γ t a ea)) (trans (cong (λ n → nf n Γ t) (+-comm k' k)) (nf-+ k k' Γ t b eb)))

nf-≥ : ∀ k k' Γ t a → nf k Γ t ≡ just a → T (k <ℕ suc k') → nf k' Γ t ≡ just a
nf-≥ k k' Γ t a e p with le-split k k' p
... | i , q rewrite q = nf-+ i k Γ t a e

------------------------------------------------------------------------
-- Depth.

private
  ≤-maxl : ∀ a b → T (a <ℕ suc (max a b))
  ≤-maxl zero    b       = tt
  ≤-maxl (suc a) zero    = ≤-refl a
    where
    ≤-refl : ∀ a → T (a <ℕ suc a)
    ≤-refl zero    = tt
    ≤-refl (suc a) = ≤-refl a
  ≤-maxl (suc a) (suc b) = ≤-maxl a b

  ≤-maxr : ∀ a b → T (b <ℕ suc (max a b))
  ≤-maxr zero    b       = ≤-refl b
    where
    ≤-refl : ∀ a → T (a <ℕ suc a)
    ≤-refl zero    = tt
    ≤-refl (suc a) = ≤-refl a
  ≤-maxr (suc a) zero    = tt
  ≤-maxr (suc a) (suc b) = ≤-maxr a b

  ≤-trans : ∀ a b c → T (a <ℕ suc b) → T (b <ℕ suc c) → T (a <ℕ suc c)
  ≤-trans zero    b       c       p q = tt
  ≤-trans (suc a) zero    c       () q
  ≤-trans (suc a) (suc b) zero    p ()
  ≤-trans (suc a) (suc b) (suc c) p q = ≤-trans a b c p q

depth-look : ∀ σ y → T (depthTm (lookupₛ σ y) <ℕ suc (depthSub σ))
depth-look ⟨⟩       y = tt
depth-look (σ ,ₛ t) y with y ==ℕ lenₛ σ
... | true  = ≤-maxr (depthSub σ) (depthTm t)
... | false = ≤-trans (depthTm (lookupₛ σ y)) (depthSub σ) (max (depthSub σ) (depthTm t))
                (depth-look σ y) (≤-maxl (depthSub σ) (depthTm t))

------------------------------------------------------------------------
-- Substitution and typing.

dim-sub : ∀ A σ → dim (A [ σ ]ty) ≡ dim A
dim-sub ⋆           σ = refl
dim-sub (arr A t u) σ = cong suc (dim-sub A σ)

sub-len : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → lenₛ σ ≡ len Δ
sub-len (⟨⟩-wf _)  = refl
sub-len (,-wf d _) = cong suc (sub-len d)

private
  <-suc : ∀ a → T (a <ℕ suc a)
  <-suc zero    = tt
  <-suc (suc a) = <-suc a

  <-weak : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  <-weak zero    b       p = tt
  <-weak (suc a) zero    ()
  <-weak (suc a) (suc b) p = <-weak a b p

  <-ne : ∀ a b → T (a <ℕ b) → (a ==ℕ b) ≡ false
  <-ne zero    zero    ()
  <-ne zero    (suc b) p = refl
  <-ne (suc a) zero    ()
  <-ne (suc a) (suc b) p = <-ne a b p

  lookup-lt : ∀ Γ y A → lookup Γ y ≡ just A → T (y <ℕ len Γ)
  lookup-lt ε       y A ()
  lookup-lt (Γ ▸ C) y A e with y ==ℕ len Γ in eq
  ... | true rewrite ==ℕ-sound y (len Γ) (≡-T eq) = <-suc (len Γ)
  ... | false = <-weak y (len Γ) (lookup-lt Γ y A e)

mutual
  tm-weak : ∀ {Δ t B} → Δ ⊢tm t ∶ B → ∀ σ s → lenₛ σ ≡ len Δ → t [ σ ,ₛ s ]tm ≡ t [ σ ]tm
  tm-weak {Δ} (var-wf {i = i} _ e) σ s l
    rewrite l | <-ne i (len Δ) (lookup-lt Δ i _ e) = refl
  tm-weak (coh-wf _ _ _ _ dτ) σ s l = cong (coh _ _) (sub-weak dτ σ s l)
  tm-weak (cst-wf {k = ()} _ _) σ s l

  sub-weak : ∀ {Δ τ Θ} → Δ ⊢sub τ ∶ Θ → ∀ σ s → lenₛ σ ≡ len Δ → (τ ∘ (σ ,ₛ s)) ≡ (τ ∘ σ)
  sub-weak (⟨⟩-wf _)    σ s l = refl
  sub-weak (,-wf dτ dt) σ s l = cong₂ _,ₛ_ (sub-weak dτ σ s l) (tm-weak dt σ s l)

------------------------------------------------------------------------
-- Scoping: the variables of a typed term and of its type are in scope.

open import CaTTExp.GlobularTotal.Uniq using (memL)
open import CaTTExp.GlobularTotal.Labels using (anyL)
open import CaTTExp.GlobularTotal.FvSub using (fv-tm; fv-ty; memL-++)

Bnd : Nat → List Nat → Set
Bnd n xs = ∀ y → memL y xs ≡ true → T (y <ℕ n)

private
  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  ∨-split : ∀ a b → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
  ∨-split true  b e = inl refl
  ∨-split false b e = inr e

  bnd-++ : ∀ n xs ys → Bnd n xs → Bnd n ys → Bnd n (xs ++ ys)
  bnd-++ n xs ys bx by y m with ∨-split (memL y xs) (memL y ys) (trans (sym (memL-++ y xs ys)) m)
  ... | inl mx = bx y mx
  ... | inr my = by y my

  bnd-l : ∀ n xs ys → Bnd n (xs ++ ys) → Bnd n xs
  bnd-l n xs ys b y m = b y (trans (memL-++ y xs ys) (∨-inl m))
    where
    ∨-inl : ∀ {a b} → a ≡ true → (a ∨ b) ≡ true
    ∨-inl refl = refl

  bnd-r : ∀ n xs ys → Bnd n (xs ++ ys) → Bnd n ys
  bnd-r n xs ys b y m = b y (trans (memL-++ y xs ys) (∨-inr (memL y xs) m))
    where
    ∨-inr : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
    ∨-inr true  e = refl
    ∨-inr false e = e

  bnd-weak : ∀ n xs → Bnd n xs → Bnd (suc n) xs
  bnd-weak n xs b y m = <-weak y n (b y m)

  anyL-elim : ∀ f xs → anyL f xs ≡ true → Σ Nat λ w → (memL w xs ≡ true) × (f w ≡ true)
  anyL-elim f []       ()
  anyL-elim f (x ∷ xs) e with f x in fx
  ... | true  = x , ==-self x , fx
    where
    T-≡' : ∀ {b} → T b → b ≡ true
    T-≡' {true} _ = refl
    ==-self : ∀ x → memL x (x ∷ xs) ≡ true
    ==-self x rewrite T-≡' (==ℕ-refl x) = refl
  ... | false with anyL-elim f xs e
  ...   | w , m , fw = w , ∨-inr' (w ==ℕ x) m , fw
    where
    ∨-inr' : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
    ∨-inr' true  e = refl
    ∨-inr' false e = e

mutual
  ctx-scope : ∀ {Γ} → Γ ⊢ctx → ∀ y B → lookup Γ y ≡ just B → Bnd (len Γ) (fvTy B)
  ctx-scope ε-wf y B ()
  ctx-scope (▸-wf {Γ} {A} dΓ dA) y B e with y ==ℕ len Γ
  ... | true rewrite just-inj (sym e) = bnd-weak (len Γ) (fvTy A) (ty-scope dA)
  ... | false = bnd-weak (len Γ) (fvTy B) (ctx-scope dΓ y B e)

  ty-scope : ∀ {Γ A} → Γ ⊢ty A → Bnd (len Γ) (fvTy A)
  ty-scope (⋆-wf _) y ()
  ty-scope {Γ} (arr-wf {A} {t} {u} dt du) =
    bnd-++ (len Γ) (fvTy A) (fvTm t ++ fvTm u) (snd (tm-scope dt))
      (bnd-++ (len Γ) (fvTm t) (fvTm u) (fst (tm-scope dt)) (fst (tm-scope du)))

  tm-scope : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Bnd (len Γ) (fvTm t) × Bnd (len Γ) (fvTy A)
  tm-scope {Γ} (var-wf {i} {A} dΓ e) =
    (λ y m → var-bnd y m) , ctx-scope dΓ i A e
    where
    var-bnd : ∀ y → memL y (i ∷ []) ≡ true → T (y <ℕ len Γ)
    var-bnd y m with y ==ℕ i in eq
    ... | true rewrite ==ℕ-sound y i (≡-T eq) = lookup-lt Γ i A e
    var-bnd y () | false
  tm-scope {Γ} (coh-wf {Δ} {A} {t} {u} {σ} _ _ dA _ dσ) =
    sub-scope dσ , ty-bnd
    where
    ty-bnd : Bnd (len Γ) (fvTy ((arr A t u) [ σ ]ty))
    ty-bnd z m with anyL-elim _ (fvTy (arr A t u)) (trans (sym (fv-ty z σ (arr A t u))) m)
    ... | w , mw , mz =
      sub-comp dσ w (subst (λ n → T (w <ℕ n)) (sym (sub-len dσ)) (ty-scope dA w mw)) z mz
  tm-scope (cst-wf {k = ()} _ _)

  sub-comp : ∀ {Γ τ Θ} → Γ ⊢sub τ ∶ Θ → ∀ y → T (y <ℕ lenₛ τ) → Bnd (len Γ) (fvTm (lookupₛ τ y))
  sub-comp (⟨⟩-wf _) y ()
  sub-comp (,-wf {σ = σ} dτ dt) y p with y ==ℕ lenₛ σ in eq
  ... | true  = fst (tm-scope dt)
  ... | false = sub-comp dτ y (lt-ne y (lenₛ σ) p eq)
    where
    lt-ne : ∀ y n → T (y <ℕ suc n) → (y ==ℕ n) ≡ false → T (y <ℕ n)
    lt-ne zero    zero    p ()
    lt-ne zero    (suc n) p e = tt
    lt-ne (suc y) zero    () e
    lt-ne (suc y) (suc n) p e = lt-ne y n p e

  sub-scope : ∀ {Γ τ Θ} → Γ ⊢sub τ ∶ Θ → Bnd (len Γ) (fvSub τ)
  sub-scope (⟨⟩-wf _) y ()
  sub-scope {Γ} (,-wf {σ} {Δ} {t} dτ dt) =
    bnd-++ (len Γ) (fvSub σ) (fvTm t) (sub-scope dτ) (fst (tm-scope dt))
