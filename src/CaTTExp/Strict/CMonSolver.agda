------------------------------------------------------------------------
-- Equations in a commutative monoid, and linear consequences of
-- equations in a cancellative one.
--
--   solve e₁ e₂ ρ tt : ⟦ e₁ ⟧ ρ ≡ ⟦ e₂ ⟧ ρ
-- when e₁ and e₂ have the same variables with the same multiplicities
-- (checked by evaluation: both are flattened and sorted).
--
--   by-lin cancel hs l r p : l ≡ r
-- from equations hs = (a₁ ≡ b₁) ∷ … and p : l ⊕ Σbᵢ ≡ r ⊕ Σaᵢ, by
-- cancelling Σaᵢ = Σbᵢ.
------------------------------------------------------------------------
module CaTTExp.Strict.CMonSolver where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Tables using (CMon)

module Solver (𝕄 : CMon) where
  open CMon 𝕄

  infixl 6 _⊞_
  data Ex : Set where
    `_  : Nat → Ex
    _⊞_ : Ex → Ex → Ex
    ∅   : Ex

  ⟦_⟧ : Ex → (Nat → M) → M
  ⟦ ` i ⟧   ρ = ρ i
  ⟦ a ⊞ b ⟧ ρ = ⟦ a ⟧ ρ ⊕ ⟦ b ⟧ ρ
  ⟦ ∅ ⟧     ρ = ε

  -- Environments as lists.
  lk : List M → Nat → M
  lk []       i       = ε
  lk (x ∷ xs) zero    = x
  lk (x ∷ xs) (suc i) = lk xs i

  sumL : List Nat → (Nat → M) → M
  sumL []       ρ = ε
  sumL (i ∷ is) ρ = ρ i ⊕ sumL is ρ

  flat : Ex → List Nat → List Nat
  flat (` i)   acc = i ∷ acc
  flat (a ⊞ b) acc = flat a (flat b acc)
  flat ∅       acc = acc

  ins : Nat → List Nat → List Nat
  ins i []       = i ∷ []
  ins i (j ∷ js) = if i <ℕ j then (i ∷ (j ∷ js)) else (j ∷ ins i js)

  srt : List Nat → List Nat
  srt []       = []
  srt (i ∷ is) = ins i (srt is)

  eqL : List Nat → List Nat → Bool
  eqL []       []       = true
  eqL (i ∷ is) (j ∷ js) = (i ==ℕ j) ∧ eqL is js
  eqL _        _        = false

  private
    ⊕-idr : ∀ a → a ⊕ ε ≡ a
    ⊕-idr a = trans (⊕-comm a ε) (⊕-id a)

    swap12 : ∀ a b c → a ⊕ (b ⊕ c) ≡ b ⊕ (a ⊕ c)
    swap12 a b c = trans (sym (⊕-assoc a b c)) (trans (cong (_⊕ c) (⊕-comm a b)) (⊕-assoc b a c))

  flat-ok : ∀ e acc ρ → ⟦ e ⟧ ρ ⊕ sumL acc ρ ≡ sumL (flat e acc) ρ
  flat-ok (` i)   acc ρ = refl
  flat-ok (a ⊞ b) acc ρ =
    trans (⊕-assoc (⟦ a ⟧ ρ) (⟦ b ⟧ ρ) (sumL acc ρ))
      (trans (cong (⟦ a ⟧ ρ ⊕_) (flat-ok b acc ρ)) (flat-ok a (flat b acc) ρ))
  flat-ok ∅       acc ρ = ⊕-id (sumL acc ρ)

  ins-ok : ∀ i is ρ → sumL (ins i is) ρ ≡ ρ i ⊕ sumL is ρ
  ins-ok i []       ρ = refl
  ins-ok i (j ∷ js) ρ with i <ℕ j
  ... | true  = refl
  ... | false = trans (cong (ρ j ⊕_) (ins-ok i js ρ)) (swap12 (ρ j) (ρ i) (sumL js ρ))

  srt-ok : ∀ is ρ → sumL (srt is) ρ ≡ sumL is ρ
  srt-ok []       ρ = refl
  srt-ok (i ∷ is) ρ = trans (ins-ok i (srt is) ρ) (cong (ρ i ⊕_) (srt-ok is ρ))

  eqL-ok : ∀ is js → T (eqL is js) → is ≡ js
  eqL-ok []       []       _ = refl
  eqL-ok (i ∷ is) (j ∷ js) p = cong₂ _∷_ (==ℕ-sound i j (∧-fst p)) (eqL-ok is js (∧-snd {i ==ℕ j} p))

  norm : Ex → List Nat
  norm e = srt (flat e [])

  norm-ok : ∀ e ρ → ⟦ e ⟧ ρ ≡ sumL (norm e) ρ
  norm-ok e ρ = trans (sym (⊕-idr (⟦ e ⟧ ρ))) (trans (flat-ok e [] ρ) (sym (srt-ok (flat e []) ρ)))

  solve : ∀ e₁ e₂ ρ → T (eqL (norm e₁) (norm e₂)) → ⟦ e₁ ⟧ ρ ≡ ⟦ e₂ ⟧ ρ
  solve e₁ e₂ ρ p =
    trans (norm-ok e₁ ρ) (trans (cong (λ l → sumL l ρ) (eqL-ok (norm e₁) (norm e₂) p)) (sym (norm-ok e₂ ρ)))

  ----------------------------------------------------------------------
  -- Linear consequences.

  infixr 5 _∷ʰ_
  data Hyps : Set where
    []ʰ  : Hyps
    _∷ʰ_ : ∀ {a b : M} → a ≡ b → Hyps → Hyps

  lhsΣ rhsΣ : Hyps → M
  lhsΣ []ʰ                  = ε
  lhsΣ (_∷ʰ_ {a} {b} h hs) = a ⊕ lhsΣ hs
  rhsΣ []ʰ                  = ε
  rhsΣ (_∷ʰ_ {a} {b} h hs) = b ⊕ rhsΣ hs

  Σ-eq : ∀ hs → lhsΣ hs ≡ rhsΣ hs
  Σ-eq []ʰ        = refl
  Σ-eq (h ∷ʰ hs) = cong₂ _⊕_ h (Σ-eq hs)

  by-lin : (∀ a b c → a ⊕ c ≡ b ⊕ c → a ≡ b) →
           ∀ hs l r → l ⊕ rhsΣ hs ≡ r ⊕ lhsΣ hs → l ≡ r
  by-lin cancel hs l r p = cancel l r (lhsΣ hs) (trans (cong (l ⊕_) (Σ-eq hs)) p)
