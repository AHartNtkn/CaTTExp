------------------------------------------------------------------------
-- The strict image of a 1-cell is its path (ledger S20 (i), stage 3c;
-- the strict-image lemma of Theorem A, 1-dimensional part).
--
-- For every well-typed 1-cell u : a → b in any context Γ,
--
--   top (⟦ u ⟧ (η Γ)) ≈ tups (path u)          (`top-path`)
--
-- i.e. the top chain of u's strict image is the bag of the edges of its
-- path (GraphFillerTotal.path), one singleton tuple per edge. Proof by
-- the same mutual recursion as GraphFillerTotal.walk: a variable is
-- its own generator, and a composite over chainC k has top chain the
-- sum of the tops of its edge arguments (Strict.Interp.cohTop, the
-- k edges of chainC k being its 1-dimensional variables, `Wb-suc`).
------------------------------------------------------------------------
module CaTTExp.RCProc.StrictPath where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Weakening ∅ cattSide using (lookup-top; lookup-wk)
open import CaTTExp.Derived using (lk-top)
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Cell using (top)
open import CaTTExp.Strict.Interp ∅ (λ ()) using (⟦_⟧; ⟦_⟧ₛ; η; η-top; Fv; cohTop; lookupₑ; lookup-⟦⟧ₛ)
open import CaTTExp.Strict.PsFacts ∅ using (Wb; tup; sel-hit; sel-miss; sel-ext; Below-suc; Below-downFrom; dimv; dimM)
open import CaTTExp.GraphFillerTotal using (path; pathCh; coh-view; CohV; cohV; sub-len; lookupₛ-there₂)
open import CaTTExp.GraphFillerTotal.Chains using (chainC; vtx; T→<)
open import CaTTExp.RCProc.Path1 using (dim-chain)
open import CaTTExp.RCProc.TwoPathCtx using (tups)

tups-++ : ∀ p q → tups (p ++ q) ≡ tups p ++ tups q
tups-++ []      q = refl
tups-++ (x ∷ p) q = cong ((x ∷ []) ∷_) (tups-++ p q)

private
  self : ∀ n → T (n <ℕ suc n)
  self zero    = tt
  self (suc n) = self n

  <-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc zero    (suc n) _ = tt
  <-suc (suc i) (suc n) p = <-suc i n p

  ==-self : ∀ n → (n ==ℕ n) ≡ true
  ==-self zero    = refl
  ==-self (suc n) = ==-self n

  lookup-lt : ∀ Γ i {A} → lookup Γ i ≡ just A → T (i <ℕ len Γ)
  lookup-lt ε       i ()
  lookup-lt (Γ ▸ B) i eq with i ==ℕ len Γ in e
  ... | true  = subst (λ j → T (j <ℕ suc (len Γ))) (sym (==ℕ-sound i (len Γ) (subst T (sym e) tt))) (self (len Γ))
  ... | false = <-suc i (len Γ) (lookup-lt Γ i eq)

  -- The 1-dimensional variables of chainC (suc k): its last edge, then
  -- those of chainC k.
  Wb-suc : ∀ k → Wb (chainC (suc k)) 1 ≡ tup (suc (len (chainC k))) ∷ Wb (chainC k) 1
  Wb-suc k =
    trans (sel-hit Γ₂ 1 (suc L) (L ∷ downFrom L) (cong dimM (lookup-top Γ₁ F)))
    (cong (tup (suc L) ∷_)
      (trans (sel-miss Γ₂ 1 L (downFrom L) (cong (_==ℕ 1) (cong dimM (lookup-wk Γ₁ L F (lookup-top (chainC k) ⋆)))))
      (trans (sel-ext Γ₁ F 1 (downFrom L) (Below-suc L (downFrom L) (Below-downFrom L)))
             (sel-ext (chainC k) ⋆ 1 (downFrom L) (Below-downFrom L)))))
    where
    L  = len (chainC k)
    Γ₁ = chainC k ▸ ⋆
    F  = arr ⋆ (var (vtx k)) (var (vtx (suc k)))
    Γ₂ = Γ₁ ▸ F

  -- The sum over the edges of chainC k reads only entries below its length.
  cm-agree : ∀ k ρ ρ′ → (∀ i → T (i <ℕ len (chainC k)) → lookupₑ ρ i ≡ lookupₑ ρ′ i) →
             cm (Fv ρ) (Wb (chainC k) 1) ≡ cm (Fv ρ′) (Wb (chainC k) 1)
  cm-agree zero    ρ ρ′ h = refl
  cm-agree (suc k) ρ ρ′ h rewrite Wb-suc k =
    cong₂ _++_ (cong top (h (suc L) (self (suc L))))
               (cm-agree k ρ ρ′ λ i p → h i (<-suc i (suc L) (<-suc i L p)))
    where L = len (chainC k)

  T-true : ∀ {b} → T b → b ≡ true
  T-true {true} _ = refl

  top-var : ∀ Γ e → T (e <ℕ len Γ) → top (lookupₑ (η Γ) e) ≈ tups (e ∷ [])
  top-var Γ e p rewrite η-top Γ e | T-true p = ≈-refl

mutual
  top-path : ∀ {Γ u B a b} → Γ ⊢tm u ∶ B → B ≡ arr ⋆ a b → top (⟦ u ⟧ (η Γ)) ≈ tups (path u)
  top-path {Γ} (var-wf {i = e} _ le) _ = top-var Γ e (lookup-lt Γ e le)
  top-path (coh-wf p w a ok s) eq with coh-view (coh-wf p w a ok s) eq
  ... | cohV k _ _ _ _ sτ _ _ = topCh k _ sτ
  top-path (cst-wf {()} _ _) _

  topCh : ∀ {Γ} k τ → Γ ⊢sub τ ∶ chainC k → cohTop (chainC k) ⋆ (⟦ τ ⟧ₛ (η Γ)) ≈ tups (pathCh τ)
  topCh zero    (⟨⟩ ,ₛ x₀)     _ = ≈-refl
  topCh zero    (_ ,ₛ _ ,ₛ _) (,-wf () _)
  topCh (suc k) τ s rewrite dim-chain k = cmCh (suc k) τ s

  cmCh : ∀ {Γ} k τ → Γ ⊢sub τ ∶ chainC k → cm (Fv (⟦ τ ⟧ₛ (η Γ))) (Wb (chainC k) 1) ≈ tups (pathCh τ)
  cmCh zero    (⟨⟩ ,ₛ x₀)     _ = ≈-refl
  cmCh zero    (_ ,ₛ _ ,ₛ _) (,-wf () _)
  cmCh {Γ} (suc k) (τ ,ₛ x ,ₛ e) (,-wf (,-wf sτ dx) de) rewrite Wb-suc k =
    ≈-trans (++-cong (≡→≈ (cong top lkE)) (≡→≈ (cm-agree k ρ ρ′ agree)))
    (≈-trans (++-cong (top-path de refl) (cmCh k τ sτ))
    (≈-trans (++-comm (tups (path e)) (tups (pathCh τ)))
             (≡→≈ (sym (tups-++ (pathCh τ) (path e))))))
    where
    L  = len (chainC k)
    ρ  = ⟦ τ ,ₛ x ,ₛ e ⟧ₛ (η Γ)
    ρ′ = ⟦ τ ⟧ₛ (η Γ)
    lτ : lenₛ τ ≡ L
    lτ = trans (sub-len sτ) (sym (CaTTExp.GraphFillerTotal.Chains.len-chain k))
    lkE : lookupₑ ρ (suc L) ≡ ⟦ e ⟧ (η Γ)
    lkE = trans (lookup-⟦⟧ₛ (τ ,ₛ x ,ₛ e) (η Γ) (suc L)
                   (subst (λ n → T (suc L <ℕ suc (suc n))) (sym lτ) (self (suc L))))
                (cong (λ t → ⟦ t ⟧ (η Γ)) (subst (λ n → lookupₛ (τ ,ₛ x ,ₛ e) (suc n) ≡ e) lτ (lk-top (τ ,ₛ x) e)))
    agree : ∀ i → T (i <ℕ L) → lookupₑ ρ i ≡ lookupₑ ρ′ i
    agree i p =
      trans (lookup-⟦⟧ₛ (τ ,ₛ x ,ₛ e) (η Γ) i (<-suc i _ (<-suc i _ iτ)))
      (trans (cong (λ t → ⟦ t ⟧ (η Γ)) (lookupₛ-there₂ τ x e i (T→< i (lenₛ τ) iτ)))
             (sym (lookup-⟦⟧ₛ τ (η Γ) i iτ)))
      where
      iτ : T (i <ℕ lenₛ τ)
      iτ = subst (λ n → T (i <ℕ n)) (sym lτ) p
