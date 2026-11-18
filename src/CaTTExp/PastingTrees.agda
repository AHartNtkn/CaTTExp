------------------------------------------------------------------------
-- Pasting contexts from rooted plane trees (Batanin trees).
--
-- A tree with children t₁ … tₖ describes k composable cells in a row,
-- where tᵢ is the pasting diagram living in the hom between the i-th
-- pair of adjacent cells. `psOf` turns a tree into a context together
-- with a derivation of Γ ⊢ps, by running the pse/psd rules. `treeOf`
-- goes back, so the checker can decide Γ ⊢ps by a round trip.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.PastingTrees (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊

data Tree : Set where
  node : List Tree → Tree

-- Handy names.
leaf : Tree
leaf = node []

mutual
  build : Tree → ∀ {Γ x A} → Γ ⊢ps x ∶ A → Σ Ctx (λ Γ' → Σ Nat (λ x' → Γ' ⊢ps x' ∶ A))
  build (node ts) d = buildList ts d

  buildList : List Tree → ∀ {Γ x A} → Γ ⊢ps x ∶ A → Σ Ctx (λ Γ' → Σ Nat (λ x' → Γ' ⊢ps x' ∶ A))
  buildList []       {Γ} {x} d = Γ , x , d
  buildList (t ∷ ts) d with build t (pse d)
  ... | Γ₂ , _ , d₂ = buildList ts (psd d₂)

psOf : Tree → Σ Ctx _⊢ps
psOf t with build t pss
... | Γ , _ , d = Γ , ps d

ctxOf : Tree → Ctx
ctxOf t = fst (psOf t)

------------------------------------------------------------------------
-- From a context back to a tree.

private
  -- The edge depths of the (y, f) pairs following the first object.
  pairDepths : Ctx → Maybe (List Nat)
  pairDepths ε                 = nothing
  pairDepths (ε ▸ ⋆)           = just []
  pairDepths (ε ▸ arr _ _ _)   = nothing
  pairDepths (ε ▸ _ ▸ _)       = nothing
  pairDepths (Γ ▸ X ▸ A ▸ B)   =
    pairDepths (Γ ▸ X) >>= λ ds → just (ds ++ (suc (dim A) ∷ []))

  length : ∀ {a} {A : Set a} → List A → Nat
  length []       = 0
  length (_ ∷ xs) = suc (length xs)

  -- Parse a forest at depth `lvl` from a depth sequence (fuel-bounded).
  forest : Nat → Nat → List Nat → Maybe (List Tree × List Nat)
  forest zero    lvl ds = just ([] , ds)
  forest (suc n) lvl [] = just ([] , [])
  forest (suc n) lvl (d ∷ ds) =
    if d ==ℕ lvl then
      (forest n (suc lvl) ds >>= λ { (cs , rest) →
       forest n lvl rest     >>= λ { (ts , rest') →
       just (node cs ∷ ts , rest') } })
    else if d <ℕ lvl then just ([] , d ∷ ds)
    else nothing

treeOf : Ctx → Maybe Tree
treeOf Γ =
  pairDepths Γ >>= λ ds →
  forest (suc (length ds)) 1 ds >>= λ where
    (ts , []) → just (node ts)
    (_ , _ ∷ _) → nothing

-- Decide Γ ⊢ps: rebuild the canonical context of Γ's tree and compare.
checkPs : (Γ : Ctx) → Maybe (Γ ⊢ps)
checkPs Γ = treeOf Γ >>= λ t → go t (fst (psOf t) ==Ctx Γ) (λ p → ==Ctx-sound _ _ p)
  where
  go : (t : Tree) (b : Bool) → (T b → fst (psOf t) ≡ Γ) → Maybe (Γ ⊢ps)
  go t true  eq = just (subst _⊢ps (eq tt) (snd (psOf t)))
  go t false _  = nothing
