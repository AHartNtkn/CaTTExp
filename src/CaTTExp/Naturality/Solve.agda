------------------------------------------------------------------------
-- The gap solver used by the naturality fillers (ledger C1d): run the
-- certified checker on the two sides of a query, then the
-- relative-coherence procedure rcS on the derivations it returns.
-- `solve-ok`: the answer is well typed whenever rcS answers (`RCAt`).
------------------------------------------------------------------------
module CaTTExp.Naturality.Solve where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Completeness ∅ cattSide (λ ()) (λ ()) as Ch
open Ch using (Dec; yes; no)
open import CaTTExp.Derived using (tm-ctx)
open import CaTTExp.RCProc using (rcS; Ans)
open import CaTTExp.Naturality.Raw using (junk)

------------------------------------------------------------------------
-- The solver: run the certified checker on the two sides of a query,
-- then rcS on the derivations it returns.

private
  fromAns : ∀ {Γ X a b} → Maybe (Ans Γ X a b) → Tm
  fromAns (just (w , _)) = w
  fromAns nothing        = junk

  solveD : ∀ Γ X a b → Dec (Γ ⊢tm a ∶ X) → Dec (Γ ⊢tm b ∶ X) → Tm
  solveD Γ X a b (yes da) (yes db) = fromAns (rcS da db)
  solveD Γ X a b _        _        = junk

  solveW : ∀ Γ X a b → Dec (Γ ⊢ctx) → Tm
  solveW Γ X a b (yes w) = solveD Γ X a b (Ch.dec-tm Γ w a X) (Ch.dec-tm Γ w b X)
  solveW Γ X a b (no _)  = junk

solve : Ctx → Ty → Tm → Tm → Tm
solve Γ X a b = solveW Γ X a b (Ch.dec-ctx Γ)

solveTy : Ctx → Ty → Tm
solveTy Γ ⋆           = junk
solveTy Γ (arr X a b) = solve Γ X a b

-- The hypothesis under which the solver answers: rcS answers the query
-- for every pair of derivations of its sides.
RCAt : Ctx → Ty → Set
RCAt Γ ⋆           = ⊤
RCAt Γ (arr X a b) = (da : Γ ⊢tm a ∶ X) (db : Γ ⊢tm b ∶ X) → T (is-just (rcS da db))

solve-ok : ∀ {Γ X a b} → Γ ⊢tm a ∶ X → Γ ⊢tm b ∶ X → RCAt Γ (arr X a b) → Γ ⊢tm solve Γ X a b ∶ arr X a b
solve-ok {Γ} {X} {a} {b} da db rc = goW (Ch.dec-ctx Γ)
  where
  goA : (m : Maybe (Ans Γ X a b)) → T (is-just m) → Γ ⊢tm fromAns m ∶ arr X a b
  goA (just (w , dw)) _ = dw

  goD : (p : Dec (Γ ⊢tm a ∶ X)) (q : Dec (Γ ⊢tm b ∶ X)) → Γ ⊢tm solveD Γ X a b p q ∶ arr X a b
  goD (yes da') (yes db') = goA (rcS da' db') (rc da' db')
  goD (yes _)   (no nb)   = ⊥-elim (nb db)
  goD (no na)   _         = ⊥-elim (na da)

  goW : (p : Dec (Γ ⊢ctx)) → Γ ⊢tm solveW Γ X a b p ∶ arr X a b
  goW (yes w) = goD (Ch.dec-tm Γ w a X) (Ch.dec-tm Γ w b X)
  goW (no nw) = ⊥-elim (nw (tm-ctx da))

