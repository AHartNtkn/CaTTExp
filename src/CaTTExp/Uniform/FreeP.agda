------------------------------------------------------------------------
-- The free algebra of a presentation in SigP's format, as a
-- specification (ledger S3a).
--
-- SigP fixes the raw syntax of P: operations with guards and
-- boundaries, and equation schemas. The theory is essentially
-- algebraic: an operation is defined on its arguments only when its
-- guards (equations between faces) hold. So the free algebra on a set
-- of generators is given by two mutually inductive judgments on raw
-- terms:
--
--   Typed x     x is a defined cell;
--   x ≐ y       x and y are equal cells.
--
-- An application of an operation is typed when its arguments are
-- typed with the declared dimensions and its guards are derivable.
-- Equality is the least congruence containing every instance of the
-- equation schemas whose guards hold, the boundary of every operation,
-- and the faces of the generators.
--
-- This is the object that a ground computation (such as
-- scripts/e6/interchange_free.py, which completes operation tables
-- dimension by dimension) must be proved to compute. Everything is
-- parametric in the operations, schemas and generators, so the same
-- definition serves P through degree four (SigP.operationsUpTo,
-- SigP.equationsUpTo) and any extension in the same format.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Finite using (_∈L_; here; there)
open import Agda.Builtin.String using (String)
open import CaTTExp.Uniform.SigP

module CaTTExp.Uniform.FreeP where

------------------------------------------------------------------------
-- Substitution of the schema variables (the names of `v` leaves).

Sub : Set
Sub = String → Tm

sub : Sub → Tm → Tm
sub σ (v _ x)       = σ x
sub σ (sF n x)      = sF n (sub σ x)
sub σ (tF n x)      = tF n (sub σ x)
sub σ (idT n x)     = idT n (sub σ x)
sub σ (comp n x y)  = comp n (sub σ x) (sub σ y)
sub σ (lft k n x y) = lft k n (sub σ x) (sub σ y)
sub σ (rgt k n x y) = rgt k n (sub σ x) (sub σ y)
sub σ (cmp o x y)   = cmp o (sub σ x) (sub σ y)

varName : Tm → String
varName (v _ x) = x
varName _       = ""

-- The selectors s_n and t_n are handled by their own rules; their
-- OpSpec entries carry no boundary.
isSelector : OpSpec → Bool
isSelector o = sel (OpSpec.applied o)
  where sel : Tm → Bool
        sel (sF _ _) = true
        sel (tF _ _) = true
        sel _        = false

------------------------------------------------------------------------
-- Generators of a pasting diagram.

record Gen : Set where
  constructor gen
  field
    gname : String
    gdim  : Nat
    gsrc  : String     -- unused when gdim = 0
    gtgt  : String
open Gen

------------------------------------------------------------------------
-- The two judgments.

module Free (ops : List OpSpec) (eqs : List Schema) (gens : List Gen) where

  data Typed : Tm → Set
  data _≐_   : Tm → Tm → Set
  infix 3 _≐_

  -- σ sends each declared variable to a typed term of its dimension.
  ArgsOK : Sub → List Tm → Set
  ArgsOK σ as = ∀ {a} → a ∈L as → Typed (σ (varName a)) × (dim (σ (varName a)) ≡ dim a)

  -- Every guard holds under σ.
  GuardsOK : Sub → List Guard → Set
  GuardsOK σ gs = ∀ {g} → g ∈L gs → sub σ (fst g) ≐ sub σ (snd g)

  data Typed where
    t-gen : ∀ {g} → g ∈L gens → Typed (v (gdim g) (gname g))
    t-s   : ∀ {n x} → Typed x → dim x ≡ suc n → Typed (sF (suc n) x)
    t-t   : ∀ {n x} → Typed x → dim x ≡ suc n → Typed (tF (suc n) x)
    t-op  : ∀ {o σ} → o ∈L ops → isSelector o ≡ false →
            ArgsOK σ (OpSpec.args o) → GuardsOK σ (OpSpec.guardsO o) →
            Typed (sub σ (OpSpec.applied o))

  data _≐_ where
    ≐-refl  : ∀ {x} → Typed x → x ≐ x
    ≐-sym   : ∀ {x y} → x ≐ y → y ≐ x
    ≐-trans : ∀ {x y z} → x ≐ y → y ≐ z → x ≐ z
    -- congruence
    ≐-s     : ∀ {n x y} → x ≐ y → sF n x ≐ sF n y
    ≐-t     : ∀ {n x y} → x ≐ y → tF n x ≐ tF n y
    ≐-op    : ∀ {o σ τ} → o ∈L ops → isSelector o ≡ false →
              ArgsOK σ (OpSpec.args o) → GuardsOK σ (OpSpec.guardsO o) →
              ArgsOK τ (OpSpec.args o) → GuardsOK τ (OpSpec.guardsO o) →
              (∀ {a} → a ∈L OpSpec.args o → σ (varName a) ≐ τ (varName a)) →
              sub σ (OpSpec.applied o) ≐ sub τ (OpSpec.applied o)
    -- equation schemas
    ≐-eq    : ∀ {e σ} → e ∈L eqs →
              ArgsOK σ (Schema.vars e) → GuardsOK σ (Schema.guards e) →
              sub σ (Schema.lhs e) ≐ sub σ (Schema.rhs e)
    -- boundaries of operations
    ≐-src   : ∀ {o σ} → o ∈L ops → isSelector o ≡ false →
              ArgsOK σ (OpSpec.args o) → GuardsOK σ (OpSpec.guardsO o) →
              sF (dim (OpSpec.applied o)) (sub σ (OpSpec.applied o)) ≐ sub σ (OpSpec.srcO o)
    ≐-tgt   : ∀ {o σ} → o ∈L ops → isSelector o ≡ false →
              ArgsOK σ (OpSpec.args o) → GuardsOK σ (OpSpec.guardsO o) →
              tF (dim (OpSpec.applied o)) (sub σ (OpSpec.applied o)) ≐ sub σ (OpSpec.tgtO o)
    -- faces of generators
    ≐-gsrc  : ∀ {g n} → g ∈L gens → gdim g ≡ suc n →
              sF (suc n) (v (gdim g) (gname g)) ≐ v n (gsrc g)
    ≐-gtgt  : ∀ {g n} → g ∈L gens → gdim g ≡ suc n →
              tF (suc n) (v (gdim g) (gname g)) ≐ v n (gtgt g)

------------------------------------------------------------------------
-- P through degree four on a pasting diagram.

private
  dropSel : List OpSpec → List OpSpec
  dropSel []       = []
  dropSel (o ∷ os) = if isSelector o then dropSel os else (o ∷ dropSel os)

opsP : List OpSpec
opsP = dropSel (operationsUpTo 4)

module FreeP (gens : List Gen) = Free opsP (equationsUpTo 4) gens

------------------------------------------------------------------------
-- Smoke test: on the pasting diagram a --f--> b --g--> c the composite
-- of f and g is a cell, and its source is a.

module Example where
  open import Agda.Builtin.String using (primStringEquality)

  gs : List Gen
  gs = gen "a" 0 "" "" ∷ gen "b" 0 "" "" ∷ gen "c" 0 "" "" ∷
       gen "f" 1 "a" "b" ∷ gen "g" 1 "b" "c" ∷ []

  open FreeP gs

  f g : Tm
  f = v 1 "f" ; g = v 1 "g"

  σ : Sub
  σ s = if primStringEquality s "x0" then f else g

  f∈ : gen "f" 1 "a" "b" ∈L gs
  f∈ = there (there (there here))
  g∈ : gen "g" 1 "b" "c" ∈L gs
  g∈ = there (there (there (there here)))

  args-ok : ArgsOK σ (v 1 "x0" ∷ v 1 "x1" ∷ [])
  args-ok here         = t-gen f∈ , refl
  args-ok (there here) = t-gen g∈ , refl

  guards-ok : GuardsOK σ ((tF 1 (v 1 "x0") , sF 1 (v 1 "x1")) ∷ [])
  guards-ok here = ≐-trans (≐-gtgt f∈ refl) (≐-sym (≐-gsrc g∈ refl))

  fg-typed : Typed (comp 1 f g)
  fg-typed = t-op {σ = σ} (there here) refl args-ok guards-ok

  fg-src : sF 1 (comp 1 f g) ≐ v 0 "a"
  fg-src = ≐-trans (≐-src {σ = σ} (there here) refl args-ok guards-ok) (≐-gsrc f∈ refl)
