------------------------------------------------------------------------
-- The edges read off a chain-shaped substitution (ledger S20 (i),
-- stage 3c).
--
-- `edgesAt σ L k` reads the paths of the entries L+1, L+3, …, L+2k−1
-- of σ: the edges of the k chain steps placed after position L. The
-- path of a walk substitution (`wgo`) is its walk (`wgo-edges`,
-- `pathCh-wgo`), and `edgesAt` depends only on the entries below
-- `bd L k` = L + 2k (`edgesAt-keep`).
------------------------------------------------------------------------
module CaTTExp.RCProc.Edges where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (++-assoc)
open import CaTTExp.GraphFillerTotal using (path; pathCh; ∣_∣; wgo; tgtOf; wgo-keep)
open import CaTTExp.GraphFillerTotal.Chains using (T→<)

bd : Nat → Nat → Nat
bd L zero    = L
bd L (suc k) = bd (suc (suc L)) k

edgesAt : Sub → Nat → Nat → List Nat
edgesAt σ L zero    = []
edgesAt σ L (suc k) = path (lookupₛ σ (suc L)) ++ edgesAt σ (suc (suc L)) k

++-[] : ∀ (xs : List Nat) → xs ++ [] ≡ xs
++-[] []       = refl
++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

private
  <-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc zero    (suc n) _ = tt
  <-suc (suc i) (suc n) p = <-suc i n p

  self : ∀ n → T (n <ℕ suc n)
  self zero    = tt
  self (suc n) = self n

  ==-refl : ∀ n → (n ==ℕ n) ≡ true
  ==-refl zero    = refl
  ==-refl (suc n) = ==-refl n

lt-bd : ∀ i L k → T (i <ℕ L) → T (i <ℕ bd L k)
lt-bd i L zero    p = p
lt-bd i L (suc k) p = lt-bd i (suc (suc L)) k (<-suc i (suc L) (<-suc i L p))

-- The length of a walk substitution.
wgo-len : ∀ Γ σ x p → lenₛ (wgo Γ σ x p) ≡ bd (lenₛ σ) ∣ p ∣
wgo-len Γ σ x []      = refl
wgo-len Γ σ x (e ∷ p) = wgo-len Γ (σ ,ₛ var (tgtOf Γ e) ,ₛ var e) (tgtOf Γ e) p

-- edgesAt only reads entries below bd L k.
edgesAt-keep : ∀ σ τ L k → (∀ i → T (i <ℕ bd L k) → lookupₛ τ i ≡ lookupₛ σ i) →
               edgesAt τ L k ≡ edgesAt σ L k
edgesAt-keep σ τ L zero    h = refl
edgesAt-keep σ τ L (suc k) h =
  cong₂ _++_ (cong path (h (suc L) (lt-bd (suc L) (suc (suc L)) k (self (suc L)))))
             (edgesAt-keep σ τ (suc (suc L)) k h)

-- The edges of a walk substitution are its walk.
wgo-edges : ∀ Γ σ x p → edgesAt (wgo Γ σ x p) (lenₛ σ) ∣ p ∣ ≡ p
wgo-edges Γ σ x []      = refl
wgo-edges Γ σ x (e ∷ p) =
  cong₂ _++_ (cong path (trans (wgo-keep σ₁ y p (suc (lenₛ σ)) (T→< _ _ (self (suc (lenₛ σ))))) top))
             (wgo-edges Γ σ₁ y p)
  where
  y  = tgtOf Γ e
  σ₁ = σ ,ₛ var y ,ₛ var e
  top : lookupₛ σ₁ (suc (lenₛ σ)) ≡ var e
  top rewrite ==-refl (lenₛ σ) = refl

-- The path of a walk substitution from a single point is its walk.
pathCh-wgo : ∀ Γ σ x p → pathCh (wgo Γ σ x p) ≡ pathCh σ ++ p
pathCh-wgo Γ σ x []      = sym (++-[] (pathCh σ))
pathCh-wgo Γ σ x (e ∷ p) =
  trans (pathCh-wgo Γ (σ ,ₛ var (tgtOf Γ e) ,ₛ var e) (tgtOf Γ e) p)
        (++-assoc (pathCh σ) (e ∷ []) p)
