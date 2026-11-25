------------------------------------------------------------------------
-- The descent as a fuel-bounded procedure (ledger S20 (i), stage 4e;
-- notes/rc-generator.md §1, stage 4 plan; tools/rc_descent.py `descend`).
--
--   rcD : (fuel : ℕ) → PlanO → Γ ⊢tm t ∶ A → Γ ⊢tm u ∶ A → Maybe (Ans Γ A t u)
--
-- A query is answered by rcS (the globular and graph procedures on the
-- support) if it can, else by the single-piece step (Descent.Piece) on
-- the plan that the plan oracle gives for it.  Every recursive call of
-- the step (the comparison in W, the bridges, the strips' inverses and
-- cancellations, and the fillers of Descent.Fill and Descent.LiftOp) is
-- rcD with one less fuel.  The plan oracle is untrusted (the Python
-- computes plans from steiner.Sd); every answer is typed by proof
-- whatever it returns.  Fuel bounds the recursion, so no termination
-- argument is needed for soundness; totality is stage 4f.
------------------------------------------------------------------------
module CaTTExp.RCProc.Descent.RcD where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.RCProc using (rcS; Ans)
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.TypedOps using (ansT)
open import CaTTExp.RCProc.Descent.LiftOp using (fillDirectOp)
open import CaTTExp.RCProc.Descent.Fill using (RecAll; fillC)
open import CaTTExp.RCProc.Descent.Piece using (Plan; piece)

-- A plan oracle.
PlanO : Set
PlanO = ∀ {Γ} → Γ ⊢ctx → TTm Γ → TTm Γ → Maybe (Plan Γ)

private
  orElse : ∀ {a} {X : Set a} → Maybe X → Maybe X → Maybe X
  orElse (just x) _ = just x
  orElse nothing  m = m

  rcST : ∀ {Γ} → TTm Γ → TTm Γ → Maybe (TTm Γ)
  rcST {Γ} a b = decTy (ty b) (ty a) >>= λ e →
                 rcS (der a) (subst (Γ ⊢tm tm b ∶_) e (der b)) >>= λ r → just (ansT r)

-- The descent on typed terms (its answers' types are not yet decided).
rcDT : Nat → PlanO → RecAll
rcDT zero    P w a b = nothing
rcDT (suc f) P w a b =
  orElse (rcST a b) (P w a b >>= λ pl → piece w r F (fillDirectOp F r) pl a b)
  where
  r = rcDT f P
  F = fillC f r

-- The descent, its answer typed t ⇛ u.
rcD : ∀ {Γ A t u} → Nat → PlanO → Γ ⊢ctx → Γ ⊢tm t ∶ A → Γ ⊢tm u ∶ A → Maybe (Ans Γ A t u)
rcD {Γ} {A} {t} {u} f P w dt du =
  rcDT f P w tt[ t ∶ A , dt ] tt[ u ∶ A , du ] >>= λ x →
  decTy (ty x) (arr A t u) >>= λ e →
  just (tm x , subst (Γ ⊢tm tm x ∶_) e (der x))
