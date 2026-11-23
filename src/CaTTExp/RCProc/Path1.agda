------------------------------------------------------------------------
-- The fixed composite of a 1-path (ledger S20 (i), stage 3c of
-- Theorem A; notes/relative-coherence.md §2 Step 3, B_w).
--
-- For a walk p of 1-variables from the object a, B Γ a p is the single
-- composition coherence over the chain context with ∣p∣ edges, applied
-- to the walk: the n-ary composite of p (the identity on a when p is
-- empty). `B-wf` types it, Γ ⊢tm B Γ a p ∶ a → y, for every walk.
------------------------------------------------------------------------
module CaTTExp.RCProc.Path1 where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GraphFillerTotal.Chains
open import CaTTExp.GraphFillerTotal
  using (∣_∣; Walk; nil; cons; wsub; wgo-ty; wgo-seg; seg-head; seg-end; walk-end; Seg; tm-ctx)
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as S

B : Ctx → Nat → List Nat → Tm
B Γ a p = coh (chainC ∣ p ∣) (arr ⋆ (var 0) (var (vtx ∣ p ∣))) (wsub Γ a p)

------------------------------------------------------------------------
-- The chain context: dimension and boundaries.

dim-chain : ∀ k → dimCtx (chainC (suc k)) ≡ 1
dim-chain zero    = refl
dim-chain (suc k) rewrite dim-chain k = refl

private
  src0 : ∀ k → srcVars 0 (chainC k) ≡ 0 ∷ []
  src0 zero    = refl
  src0 (suc k) = src0 k

  tgt0 : ∀ k → tgtVars 0 (chainC k) ≡ vtx k ∷ []
  tgt0 zero    = refl
  tgt0 (suc k) rewrite tgt0 k = cong (_∷ []) (len-chain k)

∂⁻-chain : ∀ k → ∂⁻ (chainC k) ≡ 0 ∷ []
∂⁻-chain zero    = refl
∂⁻-chain (suc k) rewrite dim-chain k = src0 (suc k)

∂⁺-chain : ∀ k → ∂⁺ (chainC k) ≡ vtx k ∷ []
∂⁺-chain zero    = refl
∂⁺-chain (suc k) rewrite dim-chain k = tgt0 (suc k)

private
  ∧-in′ : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-in′ {true} _ q = q

  ≈1 : ∀ x → T (≈? (x ∷ []) (x ∷ []))
  ≈1 x = ∧-in′ (∧-in′ (or-l (==ℕ-refl x)) tt) (∧-in′ (or-l (==ℕ-refl x)) tt)
    where
    or-l : ∀ {a b} → T a → T (a ∨ b)
    or-l {true} _ = tt

  ∨-inr′ : ∀ a {b} → T b → T (a ∨ b)
  ∨-inr′ true  _ = tt
  ∨-inr′ false p = p

-- The composite is an operation (a degenerate one, the identity, when
-- the walk is empty).
B-op : ∀ k → T (isOp (chainC k) ⋆ (var 0) (var (vtx k)))
B-op k = ∧-in′ (subst (λ L → T (≈? (0 ∷ []) L)) (sym (∂⁻-chain k)) (≈1 0))
               (subst (λ L → T (≈? (vtx k ∷ []) L)) (sym (∂⁺-chain k)) (≈1 (vtx k)))

B-side : ∀ k → T (cattSide (chainC k) ⋆ (var 0) (var (vtx k)))
B-side k = ∨-inr′ (isCoh (chainC k) ⋆ (var 0) (var (vtx k))) (B-op k)

B-ty : ∀ k → chainC k ⊢ty arr ⋆ (var 0) (var (vtx k))
B-ty k = arr-wf (var-wf (chainC-wf k) (lookup-vtx k 0 z≤n)) (var-wf (chainC-wf k) (lookup-vtx k k ≤-refl))

-- The composite of a walk from a to y is a 1-cell a → y.
B-wf : ∀ {Γ a p y} → Γ ⊢tm var a ∶ ⋆ → Walk Γ a p y → Γ ⊢tm B Γ a p ∶ arr ⋆ (var a) (var y)
B-wf {Γ} {a} {p} {y} da wk =
  subst (Γ ⊢tm B Γ a p ∶_) tyEq
    (coh-wf (ps (chainC-ps k)) (chainC-wf k) (B-ty k) (B-side k) sσ)
  where
  k = ∣ p ∣
  σ = wsub Γ a p
  sσ : Γ ⊢sub σ ∶ chainC k
  sσ = subst (λ n → Γ ⊢sub σ ∶ chainC n) (+-zero k)
             (wgo-ty (,-wf (⟨⟩-wf (tm-ctx da)) da) refl wk)
  sg : Seg Γ σ 0 a p
  sg = wgo-seg p refl refl
  tyEq : arr ⋆ (var 0) (var (vtx k)) [ σ ]ty ≡ arr ⋆ (var a) (var y)
  tyEq = cong₂ (arr ⋆) (seg-head p sg)
    (trans (cong (λ n → lookupₛ σ (vtx n)) (sym (+-zero k)))
      (trans (seg-end p sg) (cong var (walk-end wk))))
