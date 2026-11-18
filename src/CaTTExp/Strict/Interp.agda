------------------------------------------------------------------------
-- Interpretation of CaTT terms as towers of chains (ledger item A3a).
--
-- An environment gives one tower per variable. A constant k is
-- interpreted by a fixed tower M k. A coh is interpreted by
--
--   ⟦coh Δ (t →_A u) σ⟧ρ = step ⟦t⟧ρ′ ⟦u⟧ρ′ c,   ρ′ = ⟦σ⟧ρ,
--
-- where the top chain c is
--   * Σ_{w ∈ Δ of dimension dim Δ} top(ρ′ w)   when dim A + 1 = dim Δ
--     (an operation: the composite of the pasting diagram), and
--   * 0 otherwise (a coherence, or a degenerate operation: an
--     identity on its source).
-- Nothing here depends on the chain complex: the definitions only
-- move chains around. Soundness (CaTTExp.Strict.CaTT) says that the
-- result is a cell of ν(K) whenever the term is well typed and the
-- environment consists of cells.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Strict.Cell using (Tower; base; step; top; _≈w_)

module CaTTExp.Strict.Interp (𝕊 : Signature) (M : Signature.K 𝕊 → Tower) where

open Signature 𝕊
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.ConstFree 𝕊 public
open import CaTTExp.Strict.PsFacts 𝕊 using (tup; Wb; ==-refl; ==→≡; <→≢; <-suc; n<suc)
import CaTTExp.Typing
import CaTTExp.Subst 𝕊 (CaTTExp.Typing.cattSide 𝕊) as Sb
open Sb using (ScTy; ScTm; ScSub)

------------------------------------------------------------------------
-- Environments.

infixl 5 _,ₑ_
data Env : Set where
  []ₑ  : Env
  _,ₑ_ : Env → Tower → Env

lenₑ : Env → Nat
lenₑ []ₑ      = 0
lenₑ (ρ ,ₑ _) = suc (lenₑ ρ)

lookupₑ : Env → Nat → Tower
lookupₑ []ₑ      i = base []
lookupₑ (ρ ,ₑ X) i = if i ==ℕ lenₑ ρ then X else lookupₑ ρ i

-- The chain map of an environment on basis elements of λΔ.
Fv : Env → Tuple → Bag
Fv ρ (v ∷ []) = top (lookupₑ ρ v)
Fv ρ _        = []

cohTop : Ctx → Ty → Env → Bag
cohTop Δ A ρ = if suc (dim A) ==ℕ dimCtx Δ then cm (Fv ρ) (Wb Δ (dimCtx Δ)) else []

mutual
  ⟦_⟧ : Tm → Env → Tower
  ⟦ var i ⟧               ρ = lookupₑ ρ i
  ⟦ coh Δ ⋆ σ ⟧           ρ = base []
  ⟦ coh Δ (arr A t u) σ ⟧ ρ = step (⟦ t ⟧ (⟦ σ ⟧ₛ ρ)) (⟦ u ⟧ (⟦ σ ⟧ₛ ρ)) (cohTop Δ A (⟦ σ ⟧ₛ ρ))
  ⟦ cst k ⟧               ρ = M k

  ⟦_⟧ₛ : Sub → Env → Env
  ⟦ ⟨⟩ ⟧ₛ     ρ = []ₑ
  ⟦ σ ,ₛ t ⟧ₛ ρ = ⟦ σ ⟧ₛ ρ ,ₑ ⟦ t ⟧ ρ

-- A tower has the boundary prescribed by a type.
Bd : Tower → Ty → Env → Set
Bd (base _)     ⋆           ρ = ⊤
Bd (step S U _) (arr A t u) ρ = (S ≈w ⟦ t ⟧ ρ) × (U ≈w ⟦ u ⟧ ρ)
Bd _            _           ρ = ⊥

------------------------------------------------------------------------
-- Lookup.

lenₑ-⟦⟧ₛ : ∀ σ ρ → lenₑ (⟦ σ ⟧ₛ ρ) ≡ lenₛ σ
lenₑ-⟦⟧ₛ ⟨⟩       ρ = refl
lenₑ-⟦⟧ₛ (σ ,ₛ t) ρ = cong suc (lenₑ-⟦⟧ₛ σ ρ)

lookup-⟦⟧ₛ : ∀ σ ρ i → T (i <ℕ lenₛ σ) → lookupₑ (⟦ σ ⟧ₛ ρ) i ≡ ⟦ lookupₛ σ i ⟧ ρ
lookup-⟦⟧ₛ (σ ,ₛ t) ρ i p rewrite lenₑ-⟦⟧ₛ σ ρ with i ==ℕ lenₛ σ in e
... | true  = refl
... | false = lookup-⟦⟧ₛ σ ρ i (<suc-≢′ i (lenₛ σ) p e)
  where
  <suc-≢′ : ∀ a b → T (a <ℕ suc b) → (a ==ℕ b) ≡ false → T (a <ℕ b)
  <suc-≢′ zero    zero    _ ()
  <suc-≢′ zero    (suc b) _ _ = tt
  <suc-≢′ (suc a) zero    p _ = ⊥-elim (z a p)
    where
    z : ∀ a → T (suc a <ℕ 1) → ⊥
    z zero    ()
    z (suc a) ()
  <suc-≢′ (suc a) (suc b) p q = <suc-≢′ a b p q

private
  ne : ∀ a b → (a <ℕ suc b) ≡ false → (a ==ℕ b) ≡ false
  ne zero    zero    ()
  ne zero    (suc b) ()
  ne (suc a) zero    _ = refl
  ne (suc a) (suc b) p = ne a b p

  down : ∀ a b → (a <ℕ suc b) ≡ false → (a <ℕ b) ≡ false
  down zero    zero    ()
  down zero    (suc b) ()
  down (suc a) zero    _ = refl
  down (suc a) (suc b) p = down a b p

  n<suc-true : ∀ n → (n <ℕ suc n) ≡ true
  n<suc-true zero    = refl
  n<suc-true (suc n) = n<suc-true n

  same : ∀ a b → (a ==ℕ b) ≡ false → (a <ℕ suc b) ≡ (a <ℕ b)
  same zero    zero    ()
  same zero    (suc b) _ = refl
  same (suc a) zero    _ = refl
  same (suc a) (suc b) p = same a b p

lookupₑ-out : ∀ ρ i → (i <ℕ lenₑ ρ) ≡ false → lookupₑ ρ i ≡ base []
lookupₑ-out []ₑ      i _ = refl
lookupₑ-out (ρ ,ₑ X) i p rewrite ne i (lenₑ ρ) p = lookupₑ-out ρ i (down i (lenₑ ρ) p)

------------------------------------------------------------------------
-- Substitution: ⟦t[σ]⟧ρ = ⟦t⟧(⟦σ⟧ρ).

-- A coh only depends on the environment it builds.
coh-env : ∀ Δ A σ ρ σ′ ρ′ → ⟦ σ ⟧ₛ ρ ≡ ⟦ σ′ ⟧ₛ ρ′ → ⟦ coh Δ A σ ⟧ ρ ≡ ⟦ coh Δ A σ′ ⟧ ρ′
coh-env Δ ⋆           σ ρ σ′ ρ′ p = refl
coh-env Δ (arr A t u) σ ρ σ′ ρ′ p rewrite p = refl

mutual
  ⟦⟧-[] : ∀ t σ ρ → ScTm (lenₛ σ) t → ⟦ t [ σ ]tm ⟧ ρ ≡ ⟦ t ⟧ (⟦ σ ⟧ₛ ρ)
  ⟦⟧-[] (var i)     σ ρ p = sym (lookup-⟦⟧ₛ σ ρ i p)
  ⟦⟧-[] (coh Δ A τ) σ ρ p = coh-env Δ A (τ ∘ σ) ρ τ (⟦ σ ⟧ₛ ρ) (⟦⟧ₛ-∘ τ σ ρ p)
  ⟦⟧-[] (cst k)     σ ρ _ = refl

  ⟦⟧ₛ-∘ : ∀ τ σ ρ → ScSub (lenₛ σ) τ → ⟦ τ ∘ σ ⟧ₛ ρ ≡ ⟦ τ ⟧ₛ (⟦ σ ⟧ₛ ρ)
  ⟦⟧ₛ-∘ ⟨⟩       σ ρ _       = refl
  ⟦⟧ₛ-∘ (τ ,ₛ t) σ ρ (p , q) = cong₂ _,ₑ_ (⟦⟧ₛ-∘ τ σ ρ p) (⟦⟧-[] t σ ρ q)

Bd-[]→ : ∀ X A σ ρ → ScTy (lenₛ σ) A → Bd X (A [ σ ]ty) ρ → Bd X A (⟦ σ ⟧ₛ ρ)
Bd-[]→ (base _)     ⋆           σ ρ _ b = b
Bd-[]→ (step S U _) (arr A t u) σ ρ (_ , p , q) (b₁ , b₂)
  rewrite ⟦⟧-[] t σ ρ p | ⟦⟧-[] u σ ρ q = b₁ , b₂

Bd-[]← : ∀ X A σ ρ → ScTy (lenₛ σ) A → Bd X A (⟦ σ ⟧ₛ ρ) → Bd X (A [ σ ]ty) ρ
Bd-[]← (base _)     ⋆           σ ρ _ b = b
Bd-[]← (step S U _) (arr A t u) σ ρ (_ , p , q) (b₁ , b₂)
  rewrite ⟦⟧-[] t σ ρ p | ⟦⟧-[] u σ ρ q = b₁ , b₂

------------------------------------------------------------------------
-- Extending the environment does not change scoped terms.

mutual
  ⟦⟧-wk : ∀ t ρ X → ScTm (lenₑ ρ) t → ⟦ t ⟧ (ρ ,ₑ X) ≡ ⟦ t ⟧ ρ
  ⟦⟧-wk (var i)     ρ X p rewrite <→≢ i (lenₑ ρ) p = refl
  ⟦⟧-wk (coh Δ A σ) ρ X p = coh-env Δ A σ (ρ ,ₑ X) σ ρ (⟦⟧ₛ-wk σ ρ X p)
  ⟦⟧-wk (cst k)     ρ X _ = refl

  ⟦⟧ₛ-wk : ∀ σ ρ X → ScSub (lenₑ ρ) σ → ⟦ σ ⟧ₛ (ρ ,ₑ X) ≡ ⟦ σ ⟧ₛ ρ
  ⟦⟧ₛ-wk ⟨⟩       ρ X _       = refl
  ⟦⟧ₛ-wk (σ ,ₛ t) ρ X (p , q) = cong₂ _,ₑ_ (⟦⟧ₛ-wk σ ρ X p) (⟦⟧-wk t ρ X q)

Bd-wk : ∀ Y A ρ X → ScTy (lenₑ ρ) A → Bd Y A ρ → Bd Y A (ρ ,ₑ X)
Bd-wk (base _)     ⋆           ρ X _ b = b
Bd-wk (step S U _) (arr A t u) ρ X (_ , p , q) (b₁ , b₂)
  rewrite ⟦⟧-wk t ρ X p | ⟦⟧-wk u ρ X q = b₁ , b₂

------------------------------------------------------------------------
-- Naturality: on constant-free terms, top chains are carried along any
-- map G of chains that carries the environments' top chains.

TopNat : (Tuple → Bag) → Env → Env → Set
TopNat G ρ₁ ρ₂ = ∀ v → top (lookupₑ ρ₂ v) ≈ cm G (top (lookupₑ ρ₁ v))

mutual
  nat-tm : ∀ G ρ₁ ρ₂ t → CFTm t → TopNat G ρ₁ ρ₂ → top (⟦ t ⟧ ρ₂) ≈ cm G (top (⟦ t ⟧ ρ₁))
  nat-tm G ρ₁ ρ₂ (var i)               _       h = h i
  nat-tm G ρ₁ ρ₂ (coh Δ ⋆ σ)           _       h = ≈-refl
  nat-tm G ρ₁ ρ₂ (coh Δ (arr A t u) σ) (_ , c) h with suc (dim A) ==ℕ dimCtx Δ
  ... | false = ≈-refl
  ... | true  =
    ≈-trans (cm-ext' (Fv (⟦ σ ⟧ₛ ρ₂)) (λ w → cm G (Fv (⟦ σ ⟧ₛ ρ₁) w)) W pt)
            (≡→≈ (sym (cm-fuse G (Fv (⟦ σ ⟧ₛ ρ₁)) W)))
    where
    W = Wb Δ (dimCtx Δ)
    hσ = nat-sub G ρ₁ ρ₂ σ c h
    pt : ∀ w → Fv (⟦ σ ⟧ₛ ρ₂) w ≈ cm G (Fv (⟦ σ ⟧ₛ ρ₁) w)
    pt []           = ≈-refl
    pt (v ∷ [])     = hσ v
    pt (v ∷ _ ∷ _)  = ≈-refl

  nat-sub : ∀ G ρ₁ ρ₂ σ → CFSub σ → TopNat G ρ₁ ρ₂ → TopNat G (⟦ σ ⟧ₛ ρ₁) (⟦ σ ⟧ₛ ρ₂)
  nat-sub G ρ₁ ρ₂ ⟨⟩       _       h v = ≈-refl
  nat-sub G ρ₁ ρ₂ (σ ,ₛ t) (c , d) h v
    rewrite lenₑ-⟦⟧ₛ σ ρ₁ | lenₑ-⟦⟧ₛ σ ρ₂ with v ==ℕ lenₛ σ
  ... | true  = nat-tm G ρ₁ ρ₂ t d h
  ... | false = nat-sub G ρ₁ ρ₂ σ c h v

------------------------------------------------------------------------
-- The generic environment of a context: each variable is its own
-- basis element, with boundary given by its type.

gen : Nat → Ty → Env → Tower
gen v ⋆           ρ = base (tup v ∷ [])
gen v (arr A s u) ρ = step (⟦ s ⟧ ρ) (⟦ u ⟧ ρ) (tup v ∷ [])

η : Ctx → Env
η ε       = []ₑ
η (Γ ▸ A) = η Γ ,ₑ gen (len Γ) A (η Γ)

lenₑ-η : ∀ Γ → lenₑ (η Γ) ≡ len Γ
lenₑ-η ε       = refl
lenₑ-η (Γ ▸ A) = cong suc (lenₑ-η Γ)

top-gen : ∀ v A ρ → top (gen v A ρ) ≡ tup v ∷ []
top-gen v ⋆           ρ = refl
top-gen v (arr A s u) ρ = refl

η-top : ∀ Γ v → top (lookupₑ (η Γ) v) ≡ (if v <ℕ len Γ then tup v ∷ [] else [])
η-top ε       v = refl
η-top (Γ ▸ A) v rewrite lenₑ-η Γ with v ==ℕ len Γ in e
... | true  rewrite ==→≡ v (len Γ) e | top-gen (len Γ) A (η Γ) | n<suc-true (len Γ) = refl
... | false rewrite same v (len Γ) e = η-top Γ v

-- Any environment of the right length is the image of η under its own
-- chain map.
η-nat : ∀ Γ ρ → lenₑ ρ ≡ len Γ → TopNat (Fv ρ) (η Γ) ρ
η-nat Γ ρ l v rewrite η-top Γ v with v <ℕ len Γ in e
... | true  = ≡→≈ (sym (++-[]L (top (lookupₑ ρ v))))
... | false rewrite lookupₑ-out ρ v (trans (cong (v <ℕ_) l) e) = ≈-refl
