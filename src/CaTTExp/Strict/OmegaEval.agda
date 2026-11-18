------------------------------------------------------------------------
-- Interpretation of CaTT terms in a strict ω-category (ledger item A3a,
-- general case).
--
-- 𝒞 is any strict ω-category (CaTTExp.Strict.Omega) and Mk says which
-- cells a constant may denote. Composition in 𝒞 is partial, so the
-- interpretation is a relation `Ev ρ t c`:
--
--   * a variable denotes its entry in the environment;
--   * coh Θ A σ denotes the composite of the tree of Θ
--     (CaTTExp.Strict.PsTree) labelled by the environment ⟦σ⟧ρ, the
--     same cell whether the coh is a composite or a coherence (an
--     identity is the same element of the single set);
--   * a constant denotes any cell Mk allows.
--
-- The relation is deterministic when Mk is (`ev-det`). Proved here:
-- weakening, the substitution lemma in both directions, and the
-- matching facts for boundaries prescribed by types.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Strict.Omega

module CaTTExp.Strict.OmegaEval
  (𝕊 : Signature) (𝒞 : ωCat) (Mk : Signature.K 𝕊 → ωCat.C 𝒞 → Set)
  where

open Signature 𝕊
open ωCat 𝒞
open Basics 𝒞
open import CaTTExp.Strict.Trees
open import CaTTExp.Strict.OmegaPasting 𝒞
open import CaTTExp.Strict.PsTree 𝕊 using (tr)
open import CaTTExp.Strict.PsFacts 𝕊 using (<→≢; ==→≡)
import CaTTExp.Typing
import CaTTExp.Subst 𝕊 (CaTTExp.Typing.cattSide 𝕊) as Sb
open Sb using (ScTy; ScTm; ScSub)

------------------------------------------------------------------------
-- Environments.

infixl 5 _,ₑ_
data Env : Set where
  []ₑ  : Env
  _,ₑ_ : Env → C → Env

lenₑ : Env → Nat
lenₑ []ₑ      = 0
lenₑ (ρ ,ₑ _) = suc (lenₑ ρ)

lookE : Env → Nat → Maybe C
lookE []ₑ      i = nothing
lookE (ρ ,ₑ X) i = if i ==ℕ lenₑ ρ then just X else lookE ρ i

-- Lookup with a default, used to label trees.
lkd : Env → C → Nat → C
lkd []ₑ      d i = d
lkd (ρ ,ₑ X) d i = if i ==ℕ lenₑ ρ then X else lkd ρ d i

------------------------------------------------------------------------
-- The interpretation.

mutual
  data Ev (ρ : Env) : Tm → C → Set where
    ev-var : ∀ {i c} → lookE ρ i ≡ just c → Ev ρ (var i) c
    ev-coh : ∀ {Θ A σ ρ′ X c} → EvS ρ σ (ρ′ ,ₑ X) →
             Cp 0 (mapLT (lkd (ρ′ ,ₑ X) X) (tr Θ)) c → Ev ρ (coh Θ A σ) c
    ev-cst : ∀ {k c} → Mk k c → Ev ρ (cst k) c

  data EvS (ρ : Env) : Sub → Env → Set where
    evs-nil  : EvS ρ ⟨⟩ []ₑ
    evs-cons : ∀ {σ ρ′ t c} → EvS ρ σ ρ′ → Ev ρ t c → EvS ρ (σ ,ₛ t) (ρ′ ,ₑ c)

------------------------------------------------------------------------
-- Determinism.

Mk-det : Set
Mk-det = ∀ {k c c′} → Mk k c → Mk k c′ → c ≡ c′

private
  just-inj : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
  just-inj refl = refl

module _ (mdet : Mk-det) where
  mutual
    ev-det : ∀ {ρ t c c′} → Ev ρ t c → Ev ρ t c′ → c ≡ c′
    ev-det (ev-var p) (ev-var q) = just-inj (trans (sym p) q)
    ev-det (ev-coh s u) (ev-coh s′ u′) with evs-det s s′
    ... | refl = cp-det u u′
    ev-det (ev-cst m) (ev-cst m′) = mdet m m′

    evs-det : ∀ {ρ σ ρ₁ ρ₂} → EvS ρ σ ρ₁ → EvS ρ σ ρ₂ → ρ₁ ≡ ρ₂
    evs-det evs-nil evs-nil = refl
    evs-det (evs-cons s e) (evs-cons s′ e′) = cong₂ _,ₑ_ (evs-det s s′) (ev-det e e′)

------------------------------------------------------------------------
-- Lengths and lookup.

private
  lookE-< : ∀ ρ i {c} → lookE ρ i ≡ just c → T (i <ℕ lenₑ ρ)
  lookE-< []ₑ      i ()
  lookE-< (ρ ,ₑ X) i p with i ==ℕ lenₑ ρ in e
  ... | true  rewrite ==→≡ i (lenₑ ρ) e = n<s (lenₑ ρ)
    where
    n<s : ∀ n → T (n <ℕ suc n)
    n<s zero    = tt
    n<s (suc n) = n<s n
  ... | false = <s i (lenₑ ρ) (lookE-< ρ i p)
    where
    <s : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
    <s zero    (suc n) _ = tt
    <s (suc i) (suc n) q = <s i n q

lenₑ-EvS : ∀ {ρ σ ρ′} → EvS ρ σ ρ′ → lenₑ ρ′ ≡ lenₛ σ
lenₑ-EvS evs-nil        = refl
lenₑ-EvS (evs-cons s _) = cong suc (lenₑ-EvS s)

lookE-wk : ∀ ρ X i {c} → lookE ρ i ≡ just c → lookE (ρ ,ₑ X) i ≡ just c
lookE-wk ρ X i p rewrite <→≢ i (lenₑ ρ) (lookE-< ρ i p) = p

------------------------------------------------------------------------
-- Weakening: extending the environment keeps every interpretation.

mutual
  ev-wk : ∀ {ρ t c} X → Ev ρ t c → Ev (ρ ,ₑ X) t c
  ev-wk {ρ} X (ev-var {i} p) = ev-var (lookE-wk ρ X i p)
  ev-wk X (ev-coh s u)       = ev-coh (evs-wk X s) u
  ev-wk X (ev-cst m)         = ev-cst m

  evs-wk : ∀ {ρ σ ρ′} X → EvS ρ σ ρ′ → EvS (ρ ,ₑ X) σ ρ′
  evs-wk X evs-nil        = evs-nil
  evs-wk X (evs-cons s e) = evs-cons (evs-wk X s) (ev-wk X e)

------------------------------------------------------------------------
-- Substitution: ⟦t[σ]⟧ρ = ⟦t⟧(⟦σ⟧ρ).

private
  lookE-EvS← : ∀ {ρ σ ρ′} → EvS ρ σ ρ′ → ∀ i {c} → lookE ρ′ i ≡ just c → Ev ρ (lookupₛ σ i) c
  lookE-EvS← evs-nil i ()
  lookE-EvS← {ρ} (evs-cons {σ} {ρ′} {t} s e) i p rewrite lenₑ-EvS s with i ==ℕ lenₛ σ
  ... | true  = subst (Ev ρ t) (just-inj p) e
  ... | false = lookE-EvS← s i p

  lookE-EvS→ : (mdet : Mk-det) → ∀ {ρ σ ρ′} → EvS ρ σ ρ′ → ∀ i {c} → T (i <ℕ lenₛ σ) →
               Ev ρ (lookupₛ σ i) c → lookE ρ′ i ≡ just c
  lookE-EvS→ mdet evs-nil i () _
  lookE-EvS→ mdet (evs-cons {σ} {ρ′} {t} s e) i l q rewrite lenₑ-EvS s with i ==ℕ lenₛ σ in eq
  ... | true  = cong just (ev-det mdet e q)
  ... | false = lookE-EvS→ mdet s i (down i (lenₛ σ) l eq) q
    where
    down : ∀ a b → T (a <ℕ suc b) → (a ==ℕ b) ≡ false → T (a <ℕ b)
    down zero    zero    _ ()
    down zero    (suc b) _ _ = tt
    down (suc a) zero    p _ = ⊥-elim (z a p)
      where
      z : ∀ a → T (suc a <ℕ 1) → ⊥
      z zero    ()
      z (suc a) ()
    down (suc a) (suc b) p q = down a b p q

mutual
  ev-[]← : ∀ {ρ σ ρ′ t c} → EvS ρ σ ρ′ → Ev ρ′ t c → Ev ρ (t [ σ ]tm) c
  ev-[]← s (ev-var {i} p) = lookE-EvS← s i p
  ev-[]← s (ev-coh s′ u)  = ev-coh (evs-∘← s s′) u
  ev-[]← s (ev-cst m)     = ev-cst m

  evs-∘← : ∀ {ρ σ ρ′ τ ρ″} → EvS ρ σ ρ′ → EvS ρ′ τ ρ″ → EvS ρ (τ ∘ σ) ρ″
  evs-∘← s evs-nil         = evs-nil
  evs-∘← s (evs-cons s′ e) = evs-cons (evs-∘← s s′) (ev-[]← s e)

module _ (mdet : Mk-det) where
  mutual
    ev-[]→ : ∀ {ρ σ ρ′ t c} → EvS ρ σ ρ′ → ScTm (lenₛ σ) t → Ev ρ (t [ σ ]tm) c → Ev ρ′ t c
    ev-[]→ {t = var i}     s sc e = ev-var (lookE-EvS→ mdet s i sc e)
    ev-[]→ {t = coh Θ A τ} s sc (ev-coh s′ u) = ev-coh (evs-∘→ s sc s′) u
    ev-[]→ {t = cst k}     s sc (ev-cst m) = ev-cst m

    evs-∘→ : ∀ {ρ σ ρ′ τ ρ″} → EvS ρ σ ρ′ → ScSub (lenₛ σ) τ → EvS ρ (τ ∘ σ) ρ″ → EvS ρ′ τ ρ″
    evs-∘→ {τ = ⟨⟩}     s sc       evs-nil         = evs-nil
    evs-∘→ {τ = τ ,ₛ t} s (sc , st) (evs-cons s′ e) = evs-cons (evs-∘→ s sc s′) (ev-[]→ s st e)

------------------------------------------------------------------------
-- Boundaries prescribed by a type, and valid environments.

Bd : C → Ty → Env → Set
Bd c ⋆           ρ = ⊤
Bd c (arr B s u) ρ = Ev ρ s (src (dim B) c) × Ev ρ u (tgt (dim B) c)

VE : C → Ty → Env → Set
VE c A ρ = Dim≤ (dim A) c × Bd c A ρ

ValidEnv : Env → Ctx → Set
ValidEnv ρ Γ = ∀ i A → lookup Γ i ≡ just A → Σ C λ c → (lookE ρ i ≡ just c) × VE c A ρ

dim-[] : ∀ A σ → dim (A [ σ ]ty) ≡ dim A
dim-[] ⋆           σ = refl
dim-[] (arr A _ _) σ = cong suc (dim-[] A σ)

Bd-wk : ∀ c A ρ X → Bd c A ρ → Bd c A (ρ ,ₑ X)
Bd-wk c ⋆           ρ X b       = tt
Bd-wk c (arr B s u) ρ X (p , q) = ev-wk X p , ev-wk X q

Bd-[]← : ∀ c A {ρ σ ρ′} → EvS ρ σ ρ′ → Bd c A ρ′ → Bd c (A [ σ ]ty) ρ
Bd-[]← c ⋆           s b       = tt
Bd-[]← c (arr B t u) {σ = σ} s (p , q) rewrite dim-[] B σ = ev-[]← s p , ev-[]← s q

Bd-[]→ : Mk-det → ∀ c A {ρ σ ρ′} → EvS ρ σ ρ′ → ScTy (lenₛ σ) A → Bd c (A [ σ ]ty) ρ → Bd c A ρ′
Bd-[]→ mdet c ⋆           s _ b = tt
Bd-[]→ mdet c (arr B t u) {σ = σ} s (_ , st , su) (p , q) rewrite dim-[] B σ =
  ev-[]→ mdet s st p , ev-[]→ mdet s su q
