------------------------------------------------------------------------
-- Lemma E part (2): the exchange cell of a context Γ (ledger S20 (i),
-- stage 3e; notes/relative-coherence.md §2).
------------------------------------------------------------------------
module CaTTExp.RCProc.ExchangeGamma where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as S
open import CaTTExp.Derived using (tm-ctx; lk-ext; lk-top)
open import CaTTExp.Weakening ∅ cattSide using (lookup-top; lookup-wk)
open import CaTTExp.GraphFillerTotal using (path; pathCh; ∣_∣; Walk; wgo; wsub; walk-end; endOf; wgo-keep)
open import CaTTExp.GraphFillerTotal.Chains using (T→<)
open import CaTTExp.RCProc.Edges using (bd; lt-bd; edgesAt; edgesAt-keep; wgo-edges; wgo-len)
open import CaTTExp.PsRaise using (Raised)
open import CaTTExp.RCProc.Column using (chainFrom; endFrom; C₀; e₀; colCtx; colEnd)
open import CaTTExp.RCProc.ColSub using (appCh; colSub; raised-wf; end-lt)
open import CaTTExp.RCProc.Walk using (wgoF-ty; wgoF-end)
open import CaTTExp.RCProc.LemmaGSub using (lk4-0)
open import CaTTExp.RCProc.Exchange
open import CaTTExp.RCProc.ExchangeSub

private
  self : ∀ n → T (n <ℕ suc n)
  self zero    = tt
  self (suc n) = self n

  <-suc′ : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc′ zero    (suc n) _ = tt
  <-suc′ (suc i) (suc n) p = <-suc′ i n p

  lk-star : ∀ Δ x → lookup (Raised Δ x ⋆) (len Δ) ≡ just ⋆
  lk-star Δ x = lookup-wk (Δ ▸ ⋆ ▸ F ▸ F) (len Δ) Z (lookup-wk (Δ ▸ ⋆ ▸ F) (len Δ) F (lookup-wk (Δ ▸ ⋆) (len Δ) F (lookup-top Δ ⋆)))
    where
    F = arr ⋆ (var x) (var (len Δ))
    Z = arr F (var (suc (len Δ))) (var (suc (suc (len Δ))))

  len-sub : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → lenₛ σ ≡ len Δ
  len-sub s = snd (S.sub-sc closed s)

------------------------------------------------------------------------
-- Agreement of substitutions below a length.

Agr : Sub → Sub → Set
Agr σ τ = ∀ i → T (i <ℕ lenₛ σ) → T (i <ℕ lenₛ τ) × (lookupₛ τ i ≡ lookupₛ σ i)

agr-trans : ∀ {σ τ ρ} → Agr σ τ → Agr τ ρ → Agr σ ρ
agr-trans e f i p = fst (f i (fst (e i p))) , trans (snd (f i (fst (e i p)))) (snd (e i p))

agr-snoc : ∀ σ t → Agr σ (σ ,ₛ t)
agr-snoc σ t i p = <-suc′ i (lenₛ σ) p , lk-ext σ t i p

agr-wgo : ∀ Γ σ x p → Agr σ (wgo Γ σ x p)
agr-wgo Γ σ x p i q =
  subst (λ N → T (i <ℕ N)) (sym (wgo-len Γ σ x p)) (lt-bd i (lenₛ σ) ∣ p ∣ q) ,
  wgo-keep σ x p i (T→< i (lenₛ σ) q)

agr-4 : ∀ σ a b c d → Agr σ (σ ,ₛ a ,ₛ b ,ₛ c ,ₛ d)
agr-4 σ a b c d =
  agr-trans {σ} {σ ,ₛ a} {σ ,ₛ a ,ₛ b ,ₛ c ,ₛ d} (agr-snoc σ a)
    (agr-trans {σ ,ₛ a} {σ ,ₛ a ,ₛ b} {σ ,ₛ a ,ₛ b ,ₛ c ,ₛ d} (agr-snoc (σ ,ₛ a) b)
      (agr-trans {σ ,ₛ a ,ₛ b} {σ ,ₛ a ,ₛ b ,ₛ c} {σ ,ₛ a ,ₛ b ,ₛ c ,ₛ d} (agr-snoc (σ ,ₛ a ,ₛ b) c) (agr-snoc (σ ,ₛ a ,ₛ b ,ₛ c) d)))

-- The four entries of a 2-disc block.
module Blk (σ : Sub) (a b c d : Tm) where
  private
    N  = lenₛ σ
    σ₄ = σ ,ₛ a ,ₛ b ,ₛ c ,ₛ d
  lk-0 : lookupₛ σ₄ N ≡ a
  lk-0 = lk4-0 σ a b c d
  lk-1 : lookupₛ σ₄ (suc N) ≡ b
  lk-1 = trans (lk-ext (σ ,ₛ a ,ₛ b ,ₛ c) d (suc N) (<-suc′ (suc N) (suc (suc N)) (self (suc N))))
               (trans (lk-ext (σ ,ₛ a ,ₛ b) c (suc N) (self (suc N))) (lk-top (σ ,ₛ a) b))
  lk-2 : lookupₛ σ₄ (suc (suc N)) ≡ c
  lk-2 = trans (lk-ext (σ ,ₛ a ,ₛ b ,ₛ c) d (suc (suc N)) (self (suc (suc N)))) (lk-top (σ ,ₛ a ,ₛ b) c)
  lk-3 : lookupₛ σ₄ (suc (suc (suc N))) ≡ d
  lk-3 = lk-top (σ ,ₛ a ,ₛ b ,ₛ c) d

disc-lk : ∀ {τ} σ a b c d → Agr (σ ,ₛ a ,ₛ b ,ₛ c ,ₛ d) τ →
          (lookupₛ τ (lenₛ σ) ≡ a) × (lookupₛ τ (suc (lenₛ σ)) ≡ b) × (lookupₛ τ (suc (suc (lenₛ σ))) ≡ c)
          × (lookupₛ τ (suc (suc (suc (lenₛ σ)))) ≡ d)
disc-lk σ a b c d ag =
  trans (snd (ag N (<-suc′ N (suc (suc (suc N))) (<-suc′ N (suc (suc N)) (<-suc′ N (suc N) (self N)))))) lk-0 ,
  trans (snd (ag (suc N) (<-suc′ (suc N) (suc (suc (suc N))) (<-suc′ (suc N) (suc (suc N)) (self (suc N)))))) lk-1 ,
  trans (snd (ag (suc (suc N)) (<-suc′ (suc (suc N)) (suc (suc (suc N))) (self (suc (suc N)))))) lk-2 ,
  trans (snd (ag (suc (suc (suc N))) (self (suc (suc (suc N)))))) lk-3
  where
  N = lenₛ σ
  open Blk σ a b c d

module Setup {Γ a v₁ w₁ s₁ t₁ α v₂ w₂ s₂ t₂ β b} {λΓ μΓ ρΓ : List Nat}
             (da : Γ ⊢tm var a ∶ ⋆) (wλ : Walk Γ a λΓ v₁)
             (lα : lookup Γ α ≡ just (arr (arr ⋆ (var v₁) (var w₁)) s₁ t₁)) (wμ : Walk Γ w₁ μΓ v₂)
             (lβ : lookup Γ β ≡ just (arr (arr ⋆ (var v₂) (var w₂)) s₂ t₂)) (wρ : Walk Γ w₂ ρΓ b) where

  m k n : Nat
  m = ∣ λΓ ∣
  k = ∣ μΓ ∣
  n = ∣ ρΓ ∣

  open TwoDisc m k n public renaming (b to bE)

  wΓ = tm-ctx da

  -- The substitution θ_E : Γ → E.
  θ₁ θD₁ θ₂ θD₂ θE : Sub
  θ₁  = wsub Γ a λΓ
  θD₁ = θ₁ ,ₛ var w₁ ,ₛ s₁ ,ₛ t₁ ,ₛ var α
  θ₂  = wgo Γ θD₁ w₁ μΓ
  θD₂ = θ₂ ,ₛ var w₂ ,ₛ s₂ ,ₛ t₂ ,ₛ var β
  θE  = wgo Γ θD₂ w₂ ρΓ

  s-θ₁ : Γ ⊢sub θ₁ ∶ C₁
  s-θ₁ = wgoF-ty (,-wf (⟨⟩-wf wΓ) da) refl refl wλ

  l₁ : lenₛ θ₁ ≡ L₁
  l₁ = len-sub s-θ₁

  lk-e₀ : lookupₛ θ₁ (e₀ m) ≡ var v₁
  lk-e₀ = trans (wgoF-end Γ (ε ▸ ⋆) (⟨⟩ ,ₛ var a) 0 a λΓ refl refl) (cong var (walk-end wλ))

  s-θD₁ : Γ ⊢sub θD₁ ∶ D₁
  s-θD₁ = raised-wf s-θ₁ (end-lt (ε ▸ ⋆) 0 m tt) lk-e₀ (var-wf wΓ lα)

  lk-L₁ : lookupₛ θD₁ L₁ ≡ var w₁
  lk-L₁ = subst (λ N → lookupₛ θD₁ N ≡ var w₁) l₁ (lk4-0 θ₁ (var w₁) s₁ t₁ (var α))

  s-θ₂ : Γ ⊢sub θ₂ ∶ C₂
  s-θ₂ = wgoF-ty s-θD₁ (lk-star C₁ (e₀ m)) lk-L₁ wμ

  lk-cE : lookupₛ θ₂ (colEnd m k) ≡ var v₂
  lk-cE = trans (wgoF-end Γ D₁ θD₁ L₁ w₁ μΓ (len-sub s-θD₁) lk-L₁) (cong var (walk-end wμ))

  s-θD₂ : Γ ⊢sub θD₂ ∶ D₂
  s-θD₂ = raised-wf s-θ₂ (end-lt D₁ L₁ k (<-suc′ L₁ _ (<-suc′ L₁ _ (<-suc′ L₁ _ (self L₁))))) lk-cE (var-wf wΓ lβ)

  l₂ : lenₛ θ₂ ≡ L₂
  l₂ = len-sub s-θ₂

  lk-L₂ : lookupₛ θD₂ L₂ ≡ var w₂
  lk-L₂ = subst (λ N → lookupₛ θD₂ N ≡ var w₂) l₂ (lk4-0 θ₂ (var w₂) s₂ t₂ (var β))

  s-θE : Γ ⊢sub θE ∶ E
  s-θE = wgoF-ty s-θD₂ (lk-star C₂ (colEnd m k)) lk-L₂ wρ

  lk-b : lookupₛ θE bE ≡ var b
  lk-b = trans (wgoF-end Γ D₂ θD₂ L₂ w₂ ρΓ (len-sub s-θD₂) lk-L₂) (cong var (walk-end wρ))

  ----------------------------------------------------------------------
  -- θ_E on the variables of E.

  ag₁ : Agr θD₁ θE
  ag₁ = agr-trans {θD₁} {θ₂} {θE} (agr-wgo Γ θD₁ w₁ μΓ) (agr-trans {θ₂} {θD₂} {θE} (agr-4 θ₂ (var w₂) s₂ t₂ (var β)) (agr-wgo Γ θD₂ w₂ ρΓ))

  ag₀ : Agr θ₁ θE
  ag₀ = agr-trans {θ₁} {θD₁} {θE} (agr-4 θ₁ (var w₁) s₁ t₁ (var α)) ag₁

  ag₂ : Agr θD₂ θE
  ag₂ = agr-wgo Γ θD₂ w₂ ρΓ

  -- The disc entries of θ_E, at L₁ … L₁+3 and L₂ … L₂+3.
  d₁ : (lookupₛ θE L₁ ≡ var w₁) × (lookupₛ θE f₁ ≡ s₁) × (lookupₛ θE f₁′ ≡ t₁) × (lookupₛ θE Z₁ ≡ var α)
  d₁ = subst (λ N → (lookupₛ θE N ≡ var w₁) × (lookupₛ θE (suc N) ≡ s₁) × (lookupₛ θE (suc (suc N)) ≡ t₁)
                   × (lookupₛ θE (suc (suc (suc N))) ≡ var α)) l₁ (disc-lk {θE} θ₁ (var w₁) s₁ t₁ (var α) ag₁)

  d₂ : (lookupₛ θE L₂ ≡ var w₂) × (lookupₛ θE f₂ ≡ s₂) × (lookupₛ θE f₂′ ≡ t₂) × (lookupₛ θE Z₂ ≡ var β)
  d₂ = subst (λ N → (lookupₛ θE N ≡ var w₂) × (lookupₛ θE (suc N) ≡ s₂) × (lookupₛ θE (suc (suc N)) ≡ t₂)
                   × (lookupₛ θE (suc (suc (suc N))) ≡ var β)) l₂ (disc-lk {θE} θ₂ (var w₂) s₂ t₂ (var β) ag₂)

  lk-0 : lookupₛ θE 0 ≡ var a
  lk-0 = trans (snd (ag₀ 0 (subst (λ N → T (0 <ℕ N)) (sym (wgo-len Γ (⟨⟩ ,ₛ var a) a λΓ)) (lt-bd 0 1 m tt)))) (wgo-keep (⟨⟩ ,ₛ var a) a λΓ 0 (T→< 0 1 tt))

  ----------------------------------------------------------------------
  -- The paths θ_E puts on the edges of E.

  pm-λ : pmap θE λ′ ≡ λΓ
  pm-λ = trans (pmap-chEdges θE 1 m)
           (trans (edgesAt-keep θ₁ θE 1 m (λ i p → snd (ag₀ i (subst (λ N → T (i <ℕ N)) (sym (wgo-len Γ (⟨⟩ ,ₛ var a) a λΓ)) p))))
                  (wgo-edges Γ (⟨⟩ ,ₛ var a) a λΓ))

  pm-μ : pmap θE μ ≡ μΓ
  pm-μ = trans (pmap-chEdges θE (len D₁) k)
           (trans (cong (λ N → edgesAt θE (suc (suc (suc (suc N)))) k) (sym l₁))
             (trans (edgesAt-keep θ₂ θE (lenₛ θD₁) k
                       (λ i p → snd (agr-trans {θ₂} {θD₂} {θE} (agr-4 θ₂ (var w₂) s₂ t₂ (var β)) ag₂ i
                                       (subst (λ N → T (i <ℕ N)) (sym (wgo-len Γ θD₁ w₁ μΓ)) p))))
                    (wgo-edges Γ θD₁ w₁ μΓ)))

  pm-ρ : pmap θE ρ ≡ ρΓ
  pm-ρ = trans (pmap-chEdges θE (len D₂) n)
           (trans (cong (λ N → edgesAt θE (suc (suc (suc (suc N)))) n) (sym l₂))
                  (wgo-edges Γ θD₂ w₂ ρΓ))
