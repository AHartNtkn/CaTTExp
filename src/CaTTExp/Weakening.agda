------------------------------------------------------------------------
-- Weakening and context extension along a substitution, for every
-- side condition.
--
-- With de Bruijn levels, weakening leaves the syntax unchanged:
--
--   Γ ⊢tm t ∶ A  and  Γ ▸ B ⊢ctx  imply  Γ ▸ B ⊢tm t ∶ A.
--
-- Context extension: given Δ ⊢sub γ ∶ Γ₀ and a well-formed Γ₀ ⧺ Ξ,
-- `ext Δ γ Ξ` appends Ξ[γ] to Δ and extends γ by the new variables:
--
--   Δ ⧺ Ξ[γ] ⊢ctx   and   Δ ⧺ Ξ[γ] ⊢sub γ⁺ ∶ Γ₀ ⧺ Ξ.
--
-- Hypothesis: the signature's constants have closed types (as for
-- substitution, CaTTExp.Subst).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Weakening
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.TypingWith 𝕊 side
import CaTTExp.Subst 𝕊 side as Sb

private
  ≡→T : ∀ {b} → b ≡ true → T b
  ≡→T refl = tt

  <-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc zero    (suc n) _ = tt
  <-suc (suc i) (suc n) p = <-suc i n p

  <→≢ : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
  <→≢ zero    (suc n) _ = refl
  <→≢ (suc i) (suc n) p = <→≢ i n p

  <-suc-self : ∀ n → T (n <ℕ suc n)
  <-suc-self zero    = tt
  <-suc-self (suc n) = <-suc-self n

  ==→≡ : ∀ i n → (i ==ℕ n) ≡ true → i ≡ n
  ==→≡ i n p = ==ℕ-sound i n (≡→T p)

  ==-refl : ∀ n → (n ==ℕ n) ≡ true
  ==-refl zero    = refl
  ==-refl (suc n) = ==-refl n

  lookup-< : ∀ Γ i {A} → lookup Γ i ≡ just A → T (i <ℕ len Γ)
  lookup-< (Γ ▸ B) i eq with i ==ℕ len Γ in e
  ... | true  rewrite ==→≡ i (len Γ) e = <-suc-self (len Γ)
  ... | false = <-suc i (len Γ) (lookup-< Γ i eq)

lookup-top : ∀ Γ A → lookup (Γ ▸ A) (len Γ) ≡ just A
lookup-top Γ A rewrite ==-refl (len Γ) = refl

lookup-wk : ∀ Γ i {A} B → lookup Γ i ≡ just A → lookup (Γ ▸ B) i ≡ just A
lookup-wk Γ i B eq rewrite <→≢ i (len Γ) (lookup-< Γ i eq) = eq

------------------------------------------------------------------------
-- Weakening.

mutual
  wk-tm : ∀ {Γ B t A} → Γ ⊢tm t ∶ A → (Γ ▸ B) ⊢ctx → (Γ ▸ B) ⊢tm t ∶ A
  wk-tm {Γ} {B} (var-wf {i} _ eq) w = var-wf w (lookup-wk Γ i B eq)
  wk-tm (coh-wf p wΔ a ok s) w = coh-wf p wΔ a ok (wk-sub s w)
  wk-tm (cst-wf _ v) w = cst-wf w v

  wk-sub : ∀ {Γ B σ Δ} → Γ ⊢sub σ ∶ Δ → (Γ ▸ B) ⊢ctx → (Γ ▸ B) ⊢sub σ ∶ Δ
  wk-sub (⟨⟩-wf _) w = ⟨⟩-wf w
  wk-sub (,-wf s d) w = ,-wf (wk-sub s w) (wk-tm d w)

wk-ty : ∀ {Γ B A} → Γ ⊢ty A → (Γ ▸ B) ⊢ctx → (Γ ▸ B) ⊢ty A
wk-ty (⋆-wf _) w = ⋆-wf w
wk-ty (arr-wf d e) w = arr-wf (wk-tm d w) (wk-tm e w)

------------------------------------------------------------------------
-- Context extension along a substitution.

infixl 6 _⧺_
_⧺_ : Ctx → Ctx → Ctx
Γ ⧺ ε       = Γ
Γ ⧺ (Ξ ▸ A) = (Γ ⧺ Ξ) ▸ A

ext : Ctx → Sub → Ctx → Ctx × Sub
ext Δ γ ε       = Δ , γ
ext Δ γ (Ξ ▸ A) =
  let (Δ′ , γ′) = ext Δ γ Ξ in (Δ′ ▸ A [ γ′ ]ty) , (γ′ ,ₛ var (len Δ′))

module _ (closed : Sb.Closed) where

  ext-wf : ∀ {Δ γ Γ₀} Ξ → Δ ⊢ctx → Δ ⊢sub γ ∶ Γ₀ → (Γ₀ ⧺ Ξ) ⊢ctx →
           (fst (ext Δ γ Ξ) ⊢ctx) × (fst (ext Δ γ Ξ) ⊢sub snd (ext Δ γ Ξ) ∶ Γ₀ ⧺ Ξ)
  ext-wf ε       w s _ = w , s
  ext-wf {Δ} {γ} (Ξ ▸ A) w s (▸-wf wΞ a) =
    let (w′ , s′) = ext-wf Ξ w s wΞ
        w″ = ▸-wf w′ (Sb.ty[] closed a s′)
    in w″ , ,-wf (wk-sub s′ w″) (var-wf w″ (lookup-top (fst (ext Δ γ Ξ)) _))
