------------------------------------------------------------------------
-- The derived whiskering rules of CaTTExp.Derived are the terms the
-- elaborator builds: for k + j ≤ 5 (all pairs), the pasting context
-- BK k j / LK k j is the elaborator's tree, and its whisker of the
-- generic cells is coh (BK k j) (wK k j) id / coh (LK k j) (lK k j) id.
-- So the typing theorems `rwhisk`, `lwhisk` (all k, j) cover every
-- whisker and binary composite the Gray-cylinder elaborator emits.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Checks.WhiskerAgree where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Natural using (dbl)
open import CaTTExp.Derived

private
  eqM : Maybe Tm → Tm → Bool
  eqM (just t) u = t ==Tm u
  eqM nothing  u = false

  pairs : Nat → List (Nat × Nat)
  pairs zero    = (0 , 0) ∷ []
  pairs (suc n) = go (suc n) zero ++ pairs n
    where
    go : Nat → Nat → List (Nat × Nat)
    go zero    k = (k , 0) ∷ []
    go (suc j) k = (k , suc j) ∷ go j (suc k)

-- c ▹ₖ h with c the generic n-cell and h the generic (k+1)-cell.
agreeR : Nat → Nat → Bool
agreeR k j =
  (ctxOf (wrap k (node (chain j ∷ leaf ∷ []))) ==Ctx BK k j) ∧
  eqM (rw F (BK k j) (var (dbl (nB k j))) (var (suc (zK k j))))
      (coh (BK k j) (wK k j) (idₛ (BK k j)))

-- h ◃ₖ c.
agreeL : Nat → Nat → Bool
agreeL k j =
  (ctxOf (wrap k (node (leaf ∷ chain j ∷ []))) ==Ctx LK k j) ∧
  eqM (lw F (LK k j) (var (suc (suc (dbl k)))) (var (tL k j)))
      (coh (LK k j) (lK k j) (idₛ (LK k j)))

-- Every (k, j) with k + j ≤ 5.
whiskers-agree : T (all (λ kj → agreeR (fst kj) (snd kj) ∧ agreeL (fst kj) (snd kj)) (pairs 5))
whiskers-agree = tt

pairs-count : T (length (pairs 5) ==ℕ 21)
pairs-count = tt
