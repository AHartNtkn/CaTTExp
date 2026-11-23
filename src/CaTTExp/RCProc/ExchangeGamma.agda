------------------------------------------------------------------------
-- Lemma E part (2): the exchange cell of a context Γ (ledger S20 (i),
-- stage 3e; notes/relative-coherence.md §2).
--
-- Data: a context Γ with key and boundary lists p∓ satisfying
-- Term.BdOK, a point a, 2-variables α : s₁ ⇒ t₁ (over v₁ → w₁) and
-- β : s₂ ⇒ t₂ (over v₂ → w₂), and walks λ : a ⇝ v₁, μ : w₁ ⇝ v₂,
-- ρ : w₂ ⇝ b. The two orders of an exchange step,
--
--   P = (λ, α, μ ++ p⁻β ++ ρ) ; (λ ++ p⁺α ++ μ, β, ρ)
--   Q = (λ ++ p⁻α ++ μ, β, ρ) ; (λ, α, μ ++ p⁺β ++ ρ),
--
-- give 2-path terms connected by 3-cells both ways
-- (`Setup.Main.exchange`).
--
-- Proof. With m, k, n the lengths of λ, μ, ρ, the two-disc context
-- E = TwoDisc m k n maps to Γ by θ_E (Z₁ ↦ α, Z₂ ↦ β, its chains to
-- the walks; `s-θE`). Each of the four whiskered generators of E,
-- pulled back along θ_E, forms a square with the matching generator
-- of Γ (RCProc.ExchangeSq, via Lemma G). Pasting the squares of each
-- order (Glue3Eqv.paste) and the exchange cell of part (1) between
-- them gives K₀ ∗ term P ⇄ K₀ ∗ term Q for a chain filler K₀, and
-- K₀ is removed by Glue3Eqv.stripE.
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
open import CaTTExp.GraphFillerTotal using (fill₁; walk-++; cons)
open import CaTTExp.RCProc.Path1 using (B)
open import CaTTExp.RCProc.Eg using (eg; vcomp)
open import CaTTExp.RCProc.TwoPath using (assoc4)
open import CaTTExp.RCProc.TwoPathCtx using (Key2Ctx)
open import CaTTExp.RCProc.TwoPathFacts using (srcVar-eq; tgtVar-eq)
open import CaTTExp.RCProc.TwoPathTerm using (module Term)
open import CaTTExp.RCProc.ExchangeSq using (module Sq; vcomp-sub)
open import CaTTExp.RCProc.Glue3 using (low-coh; graph-chain)
open import CaTTExp.RCProc.Glue3Eqv

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

  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

-- A 2-path generator's term, at a 2-variable of known type.
module EgWEq (Γ : Ctx) (key : Nat → Nat) (p⁻ p⁺ : Nat → List Nat) where
  open Term Γ key p⁻ p⁺

  egW-eq : ∀ a b l α r {v w s t} → lookup Γ α ≡ just (arr (arr ⋆ (var v) (var w)) s t) →
           egW a b (wg l α r) ≡ eg Γ a l w s t α r b (p⁻ α) (p⁺ α)
  egW-eq a b l α r e rewrite e = refl

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

  ----------------------------------------------------------------------
  -- θ_E at the start points of the two discs.

  private
    ag₁′ : Agr θ₂ θE
    ag₁′ = agr-trans {θ₂} {θD₂} {θE} (agr-4 θ₂ (var w₂) s₂ t₂ (var β)) ag₂

  lv₁ : lookupₛ θE (e₀ m) ≡ var v₁
  lv₁ = trans (snd (ag₀ (e₀ m) (subst (λ N → T (e₀ m <ℕ N)) (sym l₁) (end-lt (ε ▸ ⋆) 0 m tt)))) lk-e₀

  lv₂ : lookupₛ θE (colEnd m k) ≡ var v₂
  lv₂ = trans (snd (ag₁′ (colEnd m k)
                  (subst (λ N → T (colEnd m k <ℕ N)) (sym l₂)
                         (end-lt D₁ L₁ k (<-suc′ L₁ _ (<-suc′ L₁ _ (<-suc′ L₁ _ (self L₁))))))))
              lk-cE

  ----------------------------------------------------------------------
  -- The exchange in Γ.

  module Main (key : Nat → Nat) (pm pp : Nat → List Nat) (okΓ : Term.BdOK Γ key pm pp) where
    private
      module TΓ = Term Γ key pm pp
      open Key2Ctx KE using () renaming (key to keyE; p⁻ to pE⁻; p⁺ to pE⁺)
      module TE = Term E keyE pE⁻ pE⁺

      AΓ : Ty
      AΓ = arr ⋆ (var a) (var b)

      vc : Tm → Tm → Tm → Tm → Tm → Tm
      vc = vcomp AΓ

      bα = okΓ α lα
      bβ = okΓ β lβ

      lf₁ = fst (snd d₁)
      lf₁′ = fst (snd (snd d₁))
      lf₂ = fst (snd d₂)
      lf₂′ = fst (snd (snd d₂))

      pα⁻ : path (lookupₛ θE f₁) ≡ pm α
      pα⁻ = trans (cong path lf₁) (fst bα)
      pα⁺ : path (lookupₛ θE f₁′) ≡ pp α
      pα⁺ = trans (cong path lf₁′) (fst (snd bα))
      pβ⁻ : path (lookupₛ θE f₂) ≡ pm β
      pβ⁻ = trans (cong path lf₂) (fst bβ)
      pβ⁺ : path (lookupₛ θE f₂′) ≡ pp β
      pβ⁺ = trans (cong path lf₂′) (fst (snd bβ))

      pm3 : ∀ X u Y → pmap θE (X ++ u ∷ Y) ≡ pmap θE X ++ (path (lookupₛ θE u) ++ pmap θE Y)
      pm3 X u Y = pmap-++ θE X (u ∷ Y)

      dZ₁ : E ⊢tm var Z₁ ∶ arr F₁ (var f₁) (var f₁′)
      dZ₁ = var-wf E-wf lkZ₁
      dZ₂ : E ⊢tm var Z₂ ∶ arr F₂ (var f₂) (var f₂′)
      dZ₂ = var-wf E-wf lkZ₂

      sZ₁ : pE⁻ Z₁ ≡ f₁ ∷ []
      sZ₁ = srcVar-eq lkZ₁
      tZ₁ : pE⁺ Z₁ ≡ f₁′ ∷ []
      tZ₁ = tgtVar-eq lkZ₁
      sZ₂ : pE⁻ Z₂ ≡ f₂ ∷ []
      sZ₂ = srcVar-eq lkZ₂
      tZ₂ : pE⁺ Z₂ ≡ f₂′ ∷ []
      tZ₂ = tgtVar-eq lkZ₂

      wrP : Walk E L₁ (μ ++ f₂ ∷ ρ) bE
      wrP = walk-++ wkμ (cons (x₅ lk-f₂) wkρ)
      wrQ : Walk E L₁ (μ ++ f₂′ ∷ ρ) bE
      wrQ = walk-++ wkμ (cons (x₅ lk-f₂′) wkρ)
      wlP : Walk E 0 (λ′ ++ f₁′ ∷ μ) (colEnd m k)
      wlP = walk-++ wkλ (cons (x₃ lk-f₁′) wkμ)
      wlQ : Walk E 0 (λ′ ++ f₁ ∷ μ) (colEnd m k)
      wlQ = walk-++ wkλ (cons (x₃ lk-f₁) wkμ)

      -- The four generators of E, pulled back.
      module P1 = Sq d0 wkλ dZ₁ wrP s-θE lk-0 lk-b lv₁
                     (fst d₁) lf₁ lf₁′ (snd (snd (snd d₁))) (fst bα) (fst (snd bα))
      module P2 = Sq d0 wlP dZ₂ wkρ s-θE lk-0 lk-b lv₂
                     (fst d₂) lf₂ lf₂′ (snd (snd (snd d₂))) (fst bβ) (fst (snd bβ))
      module Q1 = Sq d0 wlQ dZ₂ wkρ s-θE lk-0 lk-b lv₂
                     (fst d₂) lf₂ lf₂′ (snd (snd (snd d₂))) (fst bβ) (fst (snd bβ))
      module Q2 = Sq d0 wkλ dZ₁ wrQ s-θE lk-0 lk-b lv₁
                     (fst d₁) lf₁ lf₁′ (snd (snd (snd d₁))) (fst bα) (fst (snd bα))

      module P1a = P1.At (P1.at (trans P1.eλ pm-λ)
                                (trans P1.eρ (trans (pm3 μ f₂ ρ) (cong₃ (λ X Y Z → X ++ (Y ++ Z)) pm-μ pβ⁻ pm-ρ))))
      module P2a = P2.At (P2.at (trans P2.eλ (trans (pm3 λ′ f₁′ μ) (cong₃ (λ X Y Z → X ++ (Y ++ Z)) pm-λ pα⁺ pm-μ)))
                                (trans P2.eρ pm-ρ))
      module Q1a = Q1.At (Q1.at (trans Q1.eλ (trans (pm3 λ′ f₁ μ) (cong₃ (λ X Y Z → X ++ (Y ++ Z)) pm-λ pα⁻ pm-μ)))
                                (trans Q1.eρ pm-ρ))
      module Q2a = Q2.At (Q2.at (trans Q2.eλ pm-λ)
                                (trans Q2.eρ (trans (pm3 μ f₂′ ρ) (cong₃ (λ X Y Z → X ++ (Y ++ Z)) pm-μ pβ⁺ pm-ρ))))

    -- The two orders, in Γ.
    PΓ QΓ : List TΓ.WG
    PΓ = TΓ.wg λΓ α (μΓ ++ pm β ++ ρΓ) ∷ TΓ.wg (λΓ ++ pp α ++ μΓ) β ρΓ ∷ []
    QΓ = TΓ.wg (λΓ ++ pm α ++ μΓ) β ρΓ ∷ TΓ.wg λΓ α (μΓ ++ pp β ++ ρΓ) ∷ []

    SΓ TΓ′ : List Nat
    SΓ  = λΓ ++ pm α ++ μΓ ++ pm β ++ ρΓ
    TΓ′ = (λΓ ++ pp α ++ μΓ) ++ pp β ++ ρΓ

    private
      g₁ g₂ h₁ h₂ : Tm
      g₁ = eg Γ a λΓ w₁ s₁ t₁ α (μΓ ++ pm β ++ ρΓ) b (pm α) (pp α)
      g₂ = eg Γ a (λΓ ++ pp α ++ μΓ) w₂ s₂ t₂ β ρΓ b (pm β) (pp β)
      h₁ = eg Γ a (λΓ ++ pm α ++ μΓ) w₂ s₂ t₂ β ρΓ b (pm β) (pp β)
      h₂ = eg Γ a λΓ w₁ s₁ t₁ α (μΓ ++ pp β ++ ρΓ) b (pm α) (pp α)

      BS BM BT BSq BMq BTq : Tm
      BS  = B Γ a SΓ
      BM  = B Γ a (λΓ ++ pp α ++ μΓ ++ pm β ++ ρΓ)
      BT  = B Γ a TΓ′
      BSq = B Γ a ((λΓ ++ pm α ++ μΓ) ++ pm β ++ ρΓ)
      BMq = B Γ a ((λΓ ++ pm α ++ μΓ) ++ pp β ++ ρΓ)
      BTq = B Γ a (λΓ ++ pp α ++ μΓ ++ pp β ++ ρΓ)

      termP-eq : TΓ.term a b PΓ ≡ vc BS BM BT g₁ g₂
      termP-eq = cong₂ (vc BS BM BT) (EgWEq.egW-eq Γ key pm pp a b λΓ α (μΓ ++ pm β ++ ρΓ) lα)
                                     (EgWEq.egW-eq Γ key pm pp a b (λΓ ++ pp α ++ μΓ) β ρΓ lβ)

      termQ-eq : TΓ.term a b QΓ ≡ vc BSq BMq BTq h₁ h₂
      termQ-eq = cong₂ (vc BSq BMq BTq) (EgWEq.egW-eq Γ key pm pp a b (λΓ ++ pm α ++ μΓ) β ρΓ lβ)
                                        (EgWEq.egW-eq Γ key pm pp a b λΓ α (μΓ ++ pp β ++ ρΓ) lα)

      -- The pulled-back boundaries.
      XS XT : Tm
      XS = P1.X⁻
      XT = Q2.X⁺

      BE : List Nat → Tm
      BE p = B E 0 p [ θE ]tm

      eXM : P2.X⁻ ≡ P1.X⁺
      eXM = cong BE (++-assoc λ′ (f₁′ ∷ μ) (f₂ ∷ ρ))
      eXMq : Q2.X⁻ ≡ Q1.X⁺
      eXMq = sym (cong BE (++-assoc λ′ (f₁ ∷ μ) (f₂′ ∷ ρ)))
      eXS : Q1.X⁻ ≡ XS
      eXS = cong BE (++-assoc λ′ (f₁ ∷ μ) (f₂ ∷ ρ))
      eXT : P2.X⁺ ≡ XT
      eXT = cong BE (++-assoc λ′ (f₁′ ∷ μ) (f₂′ ∷ ρ))

      eBM : B Γ a ((λΓ ++ pp α ++ μΓ) ++ pm β ++ ρΓ) ≡ BM
      eBM = cong (B Γ a) (assoc4 λΓ (pp α) μΓ (pm β ++ ρΓ))
      eBMq : B Γ a (λΓ ++ pm α ++ μΓ ++ pp β ++ ρΓ) ≡ BMq
      eBMq = sym (cong (B Γ a) (assoc4 λΓ (pm α) μΓ (pp β ++ ρΓ)))
      eBS : BSq ≡ BS
      eBS = cong (B Γ a) (assoc4 λΓ (pm α) μΓ (pm β ++ ρΓ))
      eBT : BTq ≡ BT
      eBT = sym (cong (B Γ a) (assoc4 λΓ (pp α) μΓ (pp β ++ ρΓ)))

      -- Moving the source corner of a square.
      align : ∀ {X X′ Bs Bs′ Bt XT′ g e K} → X ≡ X′ → Bs ≡ Bs′ →
              Eqv Γ (arr AΓ X Bt) (vc X Bs Bt (fill₁ Γ X Bs AΓ) g) (vc X XT′ Bt e K) →
              Eqv Γ (arr AΓ X′ Bt) (vc X′ Bs′ Bt (fill₁ Γ X′ Bs′ AΓ) g) (vc X′ XT′ Bt e K)
      align refl refl q = q

      tyB : ∀ {u X Y X′ Y′} → X ≡ X′ → Y ≡ Y′ → Γ ⊢tm u ∶ arr AΓ X Y → Γ ⊢tm u ∶ arr AΓ X′ Y′
      tyB refl refl d = d

      -- Order P: K₀ ∗ (g₁ ∗ g₂) ⇄ (e₁ ∗ e₂) ∗ K₂.
      pasteP : Eqv Γ (arr AΓ XS BT) (vc XS BS BT (fill₁ Γ XS BS AΓ) (vc BS BM BT g₁ g₂))
                                    (vc XS P2.X⁺ BT (vc XS P1.X⁺ P2.X⁺ P1.e P2.e) (fill₁ Γ P2.X⁺ BT AΓ))
      pasteP = paste P1a.dK⁻* P1a.dg* (tyB eBM refl P2a.dg*) P1.de (tyB eXM refl P2.de) P1a.dK⁺* P2a.dK⁺*
                     P1a.sq* (align eXM eBM P2a.sq*)

      -- Order Q.
      pasteQ : Eqv Γ (arr AΓ Q1.X⁻ BTq) (vc Q1.X⁻ BSq BTq (fill₁ Γ Q1.X⁻ BSq AΓ) (vc BSq BMq BTq h₁ h₂))
                                        (vc Q1.X⁻ XT BTq (vc Q1.X⁻ Q1.X⁺ XT Q1.e Q2.e) (fill₁ Γ XT BTq AΓ))
      pasteQ = paste Q1a.dK⁻* Q1a.dg* (tyB eBMq refl Q2a.dg*) Q1.de (tyB eXMq refl Q2.de) Q1a.dK⁺* Q2a.dK⁺*
                     Q1a.sq* (align eXMq eBMq Q2a.sq*)

      -- The exchange cell of E, pulled back.
      Lin Rin : Tm
      Lin = vc XS P1.X⁺ P2.X⁺ P1.e P2.e
      Rin = vc Q1.X⁻ Q1.X⁺ XT Q1.e Q2.e

      eA₀ : A₀ [ θE ]ty ≡ AΓ
      eA₀ = cong₂ (arr ⋆) lk-0 lk-b

      Lθ : Lt [ θE ]tm ≡ Lin
      Lθ = trans (vcomp-sub (var 0) (var bE) tL sL uL cL hL θE)
             (trans (cong₂ (λ x y → vcomp (arr ⋆ x y) (tL [ θE ]tm) (sL [ θE ]tm) (uL [ θE ]tm) (cL [ θE ]tm) (hL [ θE ]tm)) lk-0 lk-b)
               (cong₃ (λ X Y Z → vc X Y Z (TE.egW 0 bE (TE.wg λ′ Z₁ (μ ++ f₂ ∷ ρ)) [ θE ]tm)
                                         (TE.egW 0 bE (TE.wg (λ′ ++ f₁′ ∷ μ) Z₂ ρ) [ θE ]tm))
                      (cong (λ X → BE (λ′ ++ X ++ μ ++ f₂ ∷ ρ)) sZ₁)
                      (cong (λ X → BE (λ′ ++ X ++ μ ++ f₂ ∷ ρ)) tZ₁)
                      (cong (λ X → BE ((λ′ ++ f₁′ ∷ μ) ++ X ++ ρ)) tZ₂)
                ∙ cong₂ (vc XS P1.X⁺ P2.X⁺)
                    (cong (_[ θE ]tm) (trans (EgWEq.egW-eq E keyE pE⁻ pE⁺ 0 bE λ′ Z₁ (μ ++ f₂ ∷ ρ) lkZ₁)
                                             (cong₂ (eg E 0 λ′ L₁ (var f₁) (var f₁′) Z₁ (μ ++ f₂ ∷ ρ) bE) sZ₁ tZ₁)))
                    (cong (_[ θE ]tm) (trans (EgWEq.egW-eq E keyE pE⁻ pE⁺ 0 bE (λ′ ++ f₁′ ∷ μ) Z₂ ρ lkZ₂)
                                             (cong₂ (eg E 0 (λ′ ++ f₁′ ∷ μ) L₂ (var f₂) (var f₂′) Z₂ ρ bE) sZ₂ tZ₂)))))
        where
        _∙_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
        _∙_ = trans
        tL = B E 0 (λ′ ++ pE⁻ Z₁ ++ μ ++ f₂ ∷ ρ)
        sL = B E 0 (λ′ ++ pE⁺ Z₁ ++ μ ++ f₂ ∷ ρ)
        uL = B E 0 ((λ′ ++ f₁′ ∷ μ) ++ pE⁺ Z₂ ++ ρ)
        cL = TE.egW 0 bE (TE.wg λ′ Z₁ (μ ++ f₂ ∷ ρ))
        hL = TE.egW 0 bE (TE.wg (λ′ ++ f₁′ ∷ μ) Z₂ ρ)

      Rθ : Rt [ θE ]tm ≡ Rin
      Rθ = trans (vcomp-sub (var 0) (var bE) tR sR uR cR hR θE)
             (trans (cong₂ (λ x y → vcomp (arr ⋆ x y) (tR [ θE ]tm) (sR [ θE ]tm) (uR [ θE ]tm) (cR [ θE ]tm) (hR [ θE ]tm)) lk-0 lk-b)
               (trans (cong₃ (λ X Y Z → vc X Y Z (TE.egW 0 bE (TE.wg (λ′ ++ f₁ ∷ μ) Z₂ ρ) [ θE ]tm)
                                               (TE.egW 0 bE (TE.wg λ′ Z₁ (μ ++ f₂′ ∷ ρ)) [ θE ]tm))
                             (cong (λ X → BE ((λ′ ++ f₁ ∷ μ) ++ X ++ ρ)) sZ₂)
                             (cong (λ X → BE ((λ′ ++ f₁ ∷ μ) ++ X ++ ρ)) tZ₂)
                             (cong (λ X → BE (λ′ ++ X ++ μ ++ f₂′ ∷ ρ)) tZ₁))
                      (cong₂ (vc Q1.X⁻ Q1.X⁺ XT)
                        (cong (_[ θE ]tm) (trans (EgWEq.egW-eq E keyE pE⁻ pE⁺ 0 bE (λ′ ++ f₁ ∷ μ) Z₂ ρ lkZ₂)
                                                 (cong₂ (eg E 0 (λ′ ++ f₁ ∷ μ) L₂ (var f₂) (var f₂′) Z₂ ρ bE) sZ₂ tZ₂)))
                        (cong (_[ θE ]tm) (trans (EgWEq.egW-eq E keyE pE⁻ pE⁺ 0 bE λ′ Z₁ (μ ++ f₂′ ∷ ρ) lkZ₁)
                                                 (cong₂ (eg E 0 λ′ L₁ (var f₁) (var f₁′) Z₁ (μ ++ f₂′ ∷ ρ) bE) sZ₁ tZ₁))))))
        where
        tR = B E 0 ((λ′ ++ f₁ ∷ μ) ++ pE⁻ Z₂ ++ ρ)
        sR = B E 0 ((λ′ ++ f₁ ∷ μ) ++ pE⁺ Z₂ ++ ρ)
        uR = B E 0 (λ′ ++ pE⁺ Z₁ ++ μ ++ f₂′ ∷ ρ)
        cR = TE.egW 0 bE (TE.wg (λ′ ++ f₁ ∷ μ) Z₂ ρ)
        hR = TE.egW 0 bE (TE.wg λ′ Z₁ (μ ++ f₂′ ∷ ρ))

      xchΓ : Eqv Γ (arr AΓ XS XT) Lin Rin
      xchΓ = substE3 (cong (λ X → arr X XS XT) eA₀) Lθ Rθ
               ((coh E (arr AE Lt Rt) θE , xch-wf s-θE) , (coh E (arr AE Rt Lt) θE , xch-wf′ s-θE))

      K₀ K₂ J : Tm
      K₀ = fill₁ Γ XS BS AΓ
      K₂ = fill₁ Γ XT BT AΓ
      J  = fill₁ Γ BS XS AΓ

      dK₂ : Γ ⊢tm K₂ ∶ arr AΓ XT BT
      dK₂ = subst (λ X → Γ ⊢tm fill₁ Γ X BT AΓ ∶ arr AΓ X BT) eXT P2a.dK⁺*

      PP : Eqv Γ (arr AΓ XS BT) (vc XS BS BT K₀ (TΓ.term a b PΓ)) (vc XS XT BT Lin K₂)
      PP = substE (cong (vc XS BS BT K₀) (sym termP-eq))
                  (cong (λ X → vc XS X BT Lin (fill₁ Γ X BT AΓ)) eXT) pasteP

      QQ : Eqv Γ (arr AΓ XS BT) (vc XS BS BT K₀ (TΓ.term a b QΓ)) (vc XS XT BT Rin K₂)
      QQ = substE3 (cong₂ (arr AΓ) eXS eBT)
                   (trans (cong₃ (λ X Bs Bt → vc X Bs Bt (fill₁ Γ X Bs AΓ) (vc BSq BMq BTq h₁ h₂)) eXS eBS eBT)
                          (cong (vc XS BS BT K₀) (sym termQ-eq)))
                   (cong₂ (λ X Bt → vc X XT Bt Rin (fill₁ Γ XT Bt AΓ)) eXS eBT)
                   pasteQ

      dtP : Γ ⊢tm TΓ.term a b PΓ ∶ arr AΓ BS BT
      dtP = subst (λ X → Γ ⊢tm X ∶ arr AΓ BS BT) (sym termP-eq) (vc-wf P1a.dg* (tyB eBM refl P2a.dg*))

      dtQ : Γ ⊢tm TΓ.term a b QΓ ∶ arr AΓ BS BT
      dtQ = subst (λ X → Γ ⊢tm X ∶ arr AΓ BS BT) (sym termQ-eq)
              (tyB eBS eBT (vc-wf Q1a.dg* (tyB eBMq refl Q2a.dg*)))

    -- Lemma E (2): the two orders of an exchange step of Γ are
    -- connected by 3-cells, both ways.
    exchange : Eqv Γ (arr AΓ (B Γ a SΓ) (B Γ a TΓ′)) (TΓ.term a b PΓ) (TΓ.term a b QΓ)
    exchange =
      stripE P1a.dK⁻* P1a.dJ* (low-coh P1a.dK⁻* (graph-chain ∣ path XS ∣)) (low-coh P1a.dJ* (graph-chain ∣ path BS ∣))
             dtP dtQ (PP ⊙ congLE dK₂ xchΓ ⊙ symE QQ)
