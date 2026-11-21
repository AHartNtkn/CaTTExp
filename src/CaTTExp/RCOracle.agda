------------------------------------------------------------------------
-- Relative-coherence oracles.
--
-- An oracle answers: given Γ, A and terms t, u of type A, a term
-- w : t →_A u, or nothing. Oracles are untrusted: `certify` re-checks
-- every answer with the certified checker, so a certified answer is a
-- genuine CaTT derivation whatever the oracle did.
--
-- The answers themselves are produced by the untrusted generator
-- tools/rc_oracle.py (RC(1), Theorem A, and the r9 Response 15 descent
-- as it is implemented), which writes them as a table
-- (CaTTExp.Generated.RC*). `fromTable` turns a table into an oracle.
-- Totality of the generator on strong-Steiner contexts is a separate
-- theorem; nothing here depends on it.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Pure

module CaTTExp.RCOracle where

Oracle : Set
Oracle = Ctx → Ty → Tm → Tm → Maybe Tm

-- A query: the arguments of one oracle call. A consumer module exposes
-- the calls it makes as a closed `List Query`; tools/agda_bridge.py
-- normalizes that list and hands it to the generator.
record Query : Set where
  constructor query
  field
    qctx : Ctx
    qty  : Ty
    qsrc : Tm
    qtgt : Tm

-- A query, with the oracle's answer.
record Entry : Set where
  constructor entry
  field
    ctx : Ctx
    ty  : Ty
    src : Tm
    tgt : Tm
    ans : Tm

open Entry public

matches : Entry → Ctx → Ty → Tm → Tm → Bool
matches e Γ A t u =
  (ctx e ==Ctx Γ) ∧ (ty e ==Ty A) ∧ (src e ==Tm t) ∧ (tgt e ==Tm u)

fromTable : List Entry → Oracle
fromTable []       Γ A t u = nothing
fromTable (e ∷ es) Γ A t u =
  if matches e Γ A t u then just (ans e) else fromTable es Γ A t u

-- Oracles combine left-biased.
_orElse_ : Oracle → Oracle → Oracle
(o₁ orElse o₂) Γ A t u with o₁ Γ A t u
... | just w  = just w
... | nothing = o₂ Γ A t u

-- Re-check an answer with the certified checker.
certify : Oracle → (Γ : Ctx) (A : Ty) (t u : Tm) →
          Maybe (Σ Tm (λ w → Γ ⊢tm w ∶ arr A t u))
certify rc Γ A t u =
  rc Γ A t u >>= λ w →
  infer Γ w >>= λ where
    (B , d) → guard (B ==Ty arr A t u) λ p →
      just (w , subst (Γ ⊢tm w ∶_) (==Ty-sound B (arr A t u) p) d)

-- Every entry of a table is certified: the checker accepts its answer at
-- exactly the queried type. Generated tables prove `AllCertified` by
-- `tt`-style evaluation (see `certified?`).
entryOK : Entry → Bool
entryOK e with infer (ctx e) (ans e)
... | nothing      = false
... | just (B , _) = B ==Ty arr (ty e) (src e) (tgt e)

certified? : List Entry → Bool
certified? = all entryOK
