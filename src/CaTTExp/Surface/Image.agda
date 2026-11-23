------------------------------------------------------------------------
-- Images of terms in a strict model, as towers of top chains.
--
-- A term is interpreted, in an environment of towers, by the tower of
-- the top chains of the term and of all its iterated boundaries:
--
--   ⟦var i⟧ρ               = ρ(i)
--   ⟦coh Δ (t →_A u) σ⟧ρ   = step ⟦t⟧ρ′ ⟦u⟧ρ′ (cohT Δ A t u ρ′),  ρ′ = ⟦σ⟧ρ
--
-- This is CaTTExp.Strict.Interp with the top chain of a coherence left
-- as a parameter `cohT`, so that one development serves plain CaTT
-- (cohT = the composite of the top-dimensional variables, the strict
-- model ν(λΓ), Surface.ImageCatt) and two-tier L (cohT = the image of the
-- top tuples of K(Δ), the strict model 𝔉, Surface.ImageGray). Nothing here depends on cohT: only that
-- the top chain of a coh is a function of the environment it builds.
--
-- Contents: substitution (⟦t[σ]⟧ρ = ⟦t⟧(⟦σ⟧ρ), t scoped), weakening,
-- the generic environment η Γ (each variable its own generator, with
-- the boundary its type prescribes), and the boundary half of
-- soundness: a well-typed t : A has the boundary A prescribes, in any
-- environment whose entries have the boundaries their types prescribe
-- (`Bd-sound`, `Bd-sub`, `BdEnv-η`). The cell half (CaTTExp.Strict.Sound)
-- is not needed for the unit law.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Pure using (∅)
open import CaTTExp.Signature
open Signature ∅
import CaTTExp.Subst as SubstM
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Cell using (Tower; base; step; top; _≈w_; ≈w-refl; ≈w-sym; ≈w-trans)
open import CaTTExp.Strict.Interp ∅ (λ ()) using (Env; []ₑ; _,ₑ_; lenₑ; lookupₑ) public

module CaTTExp.Surface.Image
  (side : Ctx → Ty → Tm → Tm → Bool)
  (closedS : SubstM.Closed ∅ side)
  (cohT : Ctx → Ty → Tm → Tm → Env → Bag)
  where

open import CaTTExp.TypingWith ∅ side
import CaTTExp.Subst ∅ side as Sb
open Sb using (ScTy; ScTm; ScSub)

------------------------------------------------------------------------
-- Arithmetic.

private
  ==-refl : ∀ n → (n ==ℕ n) ≡ true
  ==-refl zero    = refl
  ==-refl (suc n) = ==-refl n

  ==→≡ : ∀ a b → (a ==ℕ b) ≡ true → a ≡ b
  ==→≡ a b p = ==ℕ-sound a b (subst T (sym p) tt)

  <→≢ : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
  <→≢ zero    (suc n) _ = refl
  <→≢ (suc i) (suc n) p = <→≢ i n p

  <suc-≢ : ∀ a b → T (a <ℕ suc b) → (a ==ℕ b) ≡ false → T (a <ℕ b)
  <suc-≢ zero    zero    _ ()
  <suc-≢ zero    (suc b) _ _ = tt
  <suc-≢ (suc a) zero    p _ = ⊥-elim (z a p)
    where
    z : ∀ a → T (suc a <ℕ 1) → ⊥
    z zero    ()
    z (suc a) ()
  <suc-≢ (suc a) (suc b) p q = <suc-≢ a b p q

  just-inj : ∀ {x y : Ty} → just x ≡ just y → x ≡ y
  just-inj refl = refl

------------------------------------------------------------------------
-- The interpretation.

mutual
  ⟦_⟧ : Tm → Env → Tower
  ⟦ var i ⟧               ρ = lookupₑ ρ i
  ⟦ coh Δ ⋆ σ ⟧           ρ = base []
  ⟦ coh Δ (arr A t u) σ ⟧ ρ = step (⟦ t ⟧ (⟦ σ ⟧ₛ ρ)) (⟦ u ⟧ (⟦ σ ⟧ₛ ρ)) (cohT Δ A t u (⟦ σ ⟧ₛ ρ))
  ⟦ cst () ⟧              ρ

  ⟦_⟧ₛ : Sub → Env → Env
  ⟦ ⟨⟩ ⟧ₛ     ρ = []ₑ
  ⟦ σ ,ₛ t ⟧ₛ ρ = ⟦ σ ⟧ₛ ρ ,ₑ ⟦ t ⟧ ρ

-- A tower has the boundary prescribed by a type.
Bd : Tower → Ty → Env → Set
Bd (base _)     ⋆           ρ = ⊤
Bd (step S U _) (arr A t u) ρ = (S ≈w ⟦ t ⟧ ρ) × (U ≈w ⟦ u ⟧ ρ)
Bd _            _           ρ = ⊥

------------------------------------------------------------------------
-- Lookup and substitution.

lenₑ-⟦⟧ₛ : ∀ σ ρ → lenₑ (⟦ σ ⟧ₛ ρ) ≡ lenₛ σ
lenₑ-⟦⟧ₛ ⟨⟩       ρ = refl
lenₑ-⟦⟧ₛ (σ ,ₛ t) ρ = cong suc (lenₑ-⟦⟧ₛ σ ρ)

lookup-⟦⟧ₛ : ∀ σ ρ i → T (i <ℕ lenₛ σ) → lookupₑ (⟦ σ ⟧ₛ ρ) i ≡ ⟦ lookupₛ σ i ⟧ ρ
lookup-⟦⟧ₛ (σ ,ₛ t) ρ i p rewrite lenₑ-⟦⟧ₛ σ ρ with i ==ℕ lenₛ σ in e
... | true  = refl
... | false = lookup-⟦⟧ₛ σ ρ i (<suc-≢ i (lenₛ σ) p e)

coh-env : ∀ Δ A σ ρ σ′ ρ′ → ⟦ σ ⟧ₛ ρ ≡ ⟦ σ′ ⟧ₛ ρ′ → ⟦ coh Δ A σ ⟧ ρ ≡ ⟦ coh Δ A σ′ ⟧ ρ′
coh-env Δ ⋆           σ ρ σ′ ρ′ p = refl
coh-env Δ (arr A t u) σ ρ σ′ ρ′ p rewrite p = refl

mutual
  ⟦⟧-[] : ∀ t σ ρ → ScTm (lenₛ σ) t → ⟦ t [ σ ]tm ⟧ ρ ≡ ⟦ t ⟧ (⟦ σ ⟧ₛ ρ)
  ⟦⟧-[] (var i)     σ ρ p = sym (lookup-⟦⟧ₛ σ ρ i p)
  ⟦⟧-[] (coh Δ A τ) σ ρ p = coh-env Δ A (τ ∘ σ) ρ τ (⟦ σ ⟧ₛ ρ) (⟦⟧ₛ-∘ τ σ ρ p)
  ⟦⟧-[] (cst ())    σ ρ _

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
-- Weakening.

mutual
  ⟦⟧-wk : ∀ t ρ X → ScTm (lenₑ ρ) t → ⟦ t ⟧ (ρ ,ₑ X) ≡ ⟦ t ⟧ ρ
  ⟦⟧-wk (var i)     ρ X p rewrite <→≢ i (lenₑ ρ) p = refl
  ⟦⟧-wk (coh Δ A σ) ρ X p = coh-env Δ A σ (ρ ,ₑ X) σ ρ (⟦⟧ₛ-wk σ ρ X p)
  ⟦⟧-wk (cst ())    ρ X _

  ⟦⟧ₛ-wk : ∀ σ ρ X → ScSub (lenₑ ρ) σ → ⟦ σ ⟧ₛ (ρ ,ₑ X) ≡ ⟦ σ ⟧ₛ ρ
  ⟦⟧ₛ-wk ⟨⟩       ρ X _       = refl
  ⟦⟧ₛ-wk (σ ,ₛ t) ρ X (p , q) = cong₂ _,ₑ_ (⟦⟧ₛ-wk σ ρ X p) (⟦⟧-wk t ρ X q)

Bd-wk : ∀ Y A ρ X → ScTy (lenₑ ρ) A → Bd Y A ρ → Bd Y A (ρ ,ₑ X)
Bd-wk (base _)     ⋆           ρ X _ b = b
Bd-wk (step S U _) (arr A t u) ρ X (_ , p , q) (b₁ , b₂)
  rewrite ⟦⟧-wk t ρ X p | ⟦⟧-wk u ρ X q = b₁ , b₂

------------------------------------------------------------------------
-- The generic environment.

gen : Nat → Ty → Env → Tower
gen v ⋆           ρ = base ((v ∷ []) ∷ [])
gen v (arr A s u) ρ = step (⟦ s ⟧ ρ) (⟦ u ⟧ ρ) ((v ∷ []) ∷ [])

η : Ctx → Env
η ε       = []ₑ
η (Γ ▸ A) = η Γ ,ₑ gen (len Γ) A (η Γ)

lenₑ-η : ∀ Γ → lenₑ (η Γ) ≡ len Γ
lenₑ-η ε       = refl
lenₑ-η (Γ ▸ A) = cong suc (lenₑ-η Γ)

Bd-gen : ∀ v A ρ → Bd (gen v A ρ) A ρ
Bd-gen v ⋆           ρ = tt
Bd-gen v (arr A s u) ρ = ≈w-refl _ , ≈w-refl _

------------------------------------------------------------------------
-- Soundness for boundaries.

BdEnv : Env → Ctx → Set
BdEnv ρ Γ = ∀ v A → lookup Γ v ≡ just A → Bd (lookupₑ ρ v) A ρ

private
  lookupₑ-top : ∀ ρ X n → lenₑ ρ ≡ n → lookupₑ (ρ ,ₑ X) n ≡ X
  lookupₑ-top ρ X n refl rewrite ==-refl (lenₑ ρ) = refl

  lookupₑ-skip : ∀ ρ X v → (v ==ℕ lenₑ ρ) ≡ false → lookupₑ (ρ ,ₑ X) v ≡ lookupₑ ρ v
  lookupₑ-skip ρ X v e rewrite e = refl

  lookup-skip : ∀ Δ B v → (v ==ℕ len Δ) ≡ false → lookup (Δ ▸ B) v ≡ lookup Δ v
  lookup-skip Δ B v e rewrite e = refl

  lookup-top : ∀ Δ B → lookup (Δ ▸ B) (len Δ) ≡ just B
  lookup-top Δ B rewrite ==-refl (len Δ) = refl

-- Extending a context's environment by a tower with the right boundary.
BdEnv-▸ : ∀ {Δ B ρ X} → Δ ⊢ctx → Δ ⊢ty B → lenₑ ρ ≡ len Δ →
          BdEnv ρ Δ → Bd X B ρ → BdEnv (ρ ,ₑ X) (Δ ▸ B)
BdEnv-▸ {Δ} {B} {ρ} {X} wΔ bB lρ IH bX v A eq = split (v ==ℕ len Δ) refl
  where
  split : ∀ b → (v ==ℕ len Δ) ≡ b → Bd (lookupₑ (ρ ,ₑ X) v) A (ρ ,ₑ X)
  split true e with ==→≡ v (len Δ) e
  ... | refl with just-inj (trans (sym eq) (lookup-top Δ B))
  ...   | refl =
    subst (λ Y → Bd Y B (ρ ,ₑ X)) (sym (lookupₑ-top ρ X (len Δ) lρ))
      (Bd-wk X B ρ X (subst (λ m → ScTy m B) (sym lρ) (Sb.ty-sc closedS bB)) bX)
  split false e =
    let eqΔ = trans (sym (lookup-skip Δ B v e)) eq
        (_ , sc) = Sb.ctx-lookup closedS wΔ eqΔ
    in subst (λ Y → Bd Y A (ρ ,ₑ X))
         (sym (lookupₑ-skip ρ X v (trans (cong (v ==ℕ_) lρ) e)))
         (Bd-wk (lookupₑ ρ v) A ρ X (subst (λ m → ScTy m A) (sym lρ) sc) (IH v A eqΔ))

BdEnv-η : ∀ {Γ} → Γ ⊢ctx → BdEnv (η Γ) Γ
BdEnv-η ε-wf v A ()
BdEnv-η {Γ ▸ B} (▸-wf w b) =
  BdEnv-▸ w b (lenₑ-η Γ) (BdEnv-η w) (Bd-gen (len Γ) B (η Γ))

mutual
  Bd-sound : ∀ {Γ t A ρ} → Γ ⊢tm t ∶ A → BdEnv ρ Γ → Bd (⟦ t ⟧ ρ) A ρ
  Bd-sound (var-wf {i} w eq) bρ = bρ i _ eq
  Bd-sound {ρ = ρ} (coh-wf {Δ = Θ} {A = B} {t = s} {u = u} {σ = σ} _ _ (arr-wf ds du) _ sσ) bρ =
    Bd-[]← (⟦ coh Θ (arr B s u) σ ⟧ ρ) (arr B s u) σ ρ scC (≈w-refl _ , ≈w-refl _)
    where
    lσ : lenₛ σ ≡ len Θ
    lσ = snd (Sb.sub-sc closedS sσ)
    scC : ScTy (lenₛ σ) (arr B s u)
    scC = subst (λ n → ScTy n (arr B s u)) (sym lσ) (Sb.ty-sc closedS (arr-wf ds du))
  Bd-sound (cst-wf {()} _ _) _

  Bd-sub : ∀ {Γ σ Δ ρ} → Γ ⊢sub σ ∶ Δ → BdEnv ρ Γ → Δ ⊢ctx → BdEnv (⟦ σ ⟧ₛ ρ) Δ
  Bd-sub (⟨⟩-wf _) bρ _ v A ()
  Bd-sub {ρ = ρ} (,-wf {σ = σ} {Δ = Δ} {t = t} {A = B} sσ dt) bρ (▸-wf wΔ bB) =
    BdEnv-▸ wΔ bB lσ (Bd-sub sσ bρ wΔ)
      (Bd-[]→ (⟦ t ⟧ ρ) B σ ρ (subst (λ m → ScTy m B) (sym lσ′) (Sb.ty-sc closedS bB)) (Bd-sound dt bρ))
    where
    lσ′ : lenₛ σ ≡ len Δ
    lσ′ = snd (Sb.sub-sc closedS sσ)
    lσ : lenₑ (⟦ σ ⟧ₛ ρ) ≡ len Δ
    lσ = trans (lenₑ-⟦⟧ₛ σ ρ) lσ′
