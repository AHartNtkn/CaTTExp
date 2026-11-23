------------------------------------------------------------------------
-- Naturality cylinders in binder syntax (ledger S26b (b), port of
-- CaTTExp.Naturality.Raw).
--
-- The construction of CaTTExp.Naturality.Raw, over the syntax of any
-- signature with binders. The variables a cylinder datum selects are
-- the bound variables of one binder, bvar 0 i (the entries of a
-- telescope, as in INIT's arrow context): for a term t of the
-- telescope,
--
--   t⁻ = opTm 0 mm t,   t⁺ = opTm 0 mp t,
--   cyl D (bvar 0 i)    = th i,
--   cyl D (coh Q B γ)   = K Q B Y' [ γ↑ ]     (Q, B pure; K embedded),
--
-- and the boundary cells a_t, b_t and the type cylTy D t A of t↑ are
-- Raw's, with the typed whiskers of CaTTExp.DerivedBoundary read in
-- binder syntax (their pasting contexts and types are pure, embedded).
-- A factor w↑ with w untouched is omitted, as in Raw. Free variables
-- (the ambient context), constants and binder terms are never
-- selected; a touched term that is not a variable or a coherence over
-- pure Q, B has no cylinder here (`junk`), and `cylOK?` rejects it.
--
-- K is a pure filler family (Raw.Filler), e.g. CaTTExp.Naturality.
-- DimOne.K₁ for the coherences of dimension 1.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Pure as P
import CaTTExp.Derived as Dv
open import CaTTExp.Naturality.Raw using (Sel; ◇; _◂_; Filler; anyL)

module CaTTExp.Binder.Cyl (𝕊 : Signature) (KF : Filler) where

open Signature 𝕊
open import CaTTExp.Binder.Pasting 𝕊 using (embTy; embTm; embCtx; toPure; toPureTy)

------------------------------------------------------------------------
-- The bound variables of the binder at depth d that a term mentions.

mutual
  occTy : Nat → Ty → List Nat
  occTy d ⋆           = []
  occTy d (arr A t u) = occTy d A ++ (occTm d t ++ occTm d u)

  occTm : Nat → Tm → List Nat
  occTm d (var _)       = []
  occTm d (bvar e j)    = if e ==ℕ d then j ∷ [] else []
  occTm d (coh _ _ σ)   = occSub d σ
  occTm d (cst _)       = []
  occTm d (bnd _ _ Δ σ) = occTel (suc d) Δ ++ occSub d σ

  occTel : Nat → Ctx → List Nat
  occTel d ε             = []
  occTel d (Δ ▸[ _ ] A) = occTel d Δ ++ occTy d A

  occSub : Nat → Sub → List Nat
  occSub d ⟨⟩       = []
  occSub d (σ ,ₛ t) = occSub d σ ++ occTm d t

------------------------------------------------------------------------
-- Cylinder data.

record Datum : Set where
  constructor datum
  field
    mm mp : Sub
    sel   : Nat → Bool
    th    : Nat → Tm
open Datum public

------------------------------------------------------------------------
-- The typed whiskers of CaTTExp.DerivedBoundary, in binder syntax.

sphSub : Ty → Sub
sphSub ⋆           = ⟨⟩
sphSub (arr A s t) = sphSub A ,ₛ s ,ₛ t

dskSub : Tm → Ty → Sub
dskSub c C = sphSub C ,ₛ c

σR : Tm → Ty → Tm → Tm → Sub
σR c C z h = dskSub c C ,ₛ z ,ₛ h

rwT : Nat → Nat → Tm → Ty → Tm → Tm → Tm
rwT k j c C z h = coh (embCtx (Dv.BK k j)) (embTy (Dv.wK k j)) (σR c C z h)

junk : Tm
junk = coh ε ⋆ ⟨⟩

------------------------------------------------------------------------
-- Iterated boundaries read off a type (as Raw; out of range, junk).

baseAt : Nat → Ty → Ty
baseAt k ⋆           = ⋆
baseAt k (arr A s u) = if k ==ℕ suc (dim A) then arr A s u else baseAt k A

tgtAt srcAt : Nat → Ty → Tm
tgtAt k ⋆           = junk
tgtAt k (arr A s u) = if k ==ℕ dim A then u else tgtAt k A
srcAt k ⋆           = junk
srcAt k (arr A s u) = if k ==ℕ dim A then s else srcAt k A

-- DerivedBoundary's tyK, tgtK, srcK (aL k and positions of the sphere,
-- substituted by sphSub C), read off C directly: they agree for
-- k < dim C, and commute with substitution in every case.
tyK : Nat → Ty → Ty
tyK = baseAt

tgtK srcK : Nat → Ty → Tm
tgtK = tgtAt
srcK = srcAt

hL : Nat → Tm → Ty → Ty
hL k x C = arr (tyK k C) x (srcK k C)

σLp : Nat → Nat → Tm → Tm → Ty → Sub
σLp k zero    h x C            = dskSub h (hL k x C) ,ₛ tgtK k C
σLp k (suc j) h x ⋆            = ⟨⟩
σLp k (suc j) h x (arr C' s t) = σLp k j h x C' ,ₛ s ,ₛ t

σL : Nat → Nat → Tm → Tm → Tm → Ty → Sub
σL k j h x c C = σLp k j h x C ,ₛ c

lwT : Nat → Nat → Tm → Tm → Tm → Ty → Tm
lwT k j h x c C = coh (embCtx (Dv.LK k j)) (embTy (Dv.lK k j)) (σL k j h x c C)

rwI : Nat → Nat → Tm → Ty → Tm → Tm → Bool → Tm
rwI k n c C z h true  = rwT k (n ∸ suc k) c C z h
rwI k n c C z h false = c

lwI : Nat → Nat → Tm → Tm → Tm → Ty → Bool → Tm
lwI k n h x c C true  = lwT k (n ∸ suc k) h x c C
lwI k n h x c C false = c

liftOne : Sub → Tm → Tm → Tm → Bool → Sub
liftOne ρ a b c true  = ρ ,ₛ a ,ₛ b ,ₛ c
liftOne ρ a b c false = ρ ,ₛ a

-- The filler for a coherence over a pure pasting context and type.
fillK : Ctx → Ty → Sel → Tm
fillK Q B Y with toPure Q | toPureTy B
... | just Q₀ | just B₀ = embTm (KF Q₀ B₀ Y)
... | _       | _       = junk

------------------------------------------------------------------------
-- The construction.

touched : Datum → Tm → Bool
touched D t = anyL (sel D) (occTm 0 t)

mask : Datum → Sub → Sel
mask D ⟨⟩       = ◇
mask D (γ ,ₛ t) = mask D γ ◂ touched D t

mutual
  cyl : Datum → Tm → Tm
  cyl D (var _)       = junk
  cyl D (bvar e i)    = if e ==ℕ 0 then th D i else junk
  cyl D (coh Q B γ)   = fillK Q B (mask D γ) [ liftS D γ ]tm
  cyl D (cst _)       = junk
  cyl D (bnd _ _ _ _) = junk

  liftS : Datum → Sub → Sub
  liftS D ⟨⟩       = ⟨⟩
  liftS D (γ ,ₛ t) = liftOne (liftS D γ) (opTm 0 (mm D) t) (opTm 0 (mp D) t) (cyl D t) (touched D t)

module _ (D : Datum) where
  mutual
    P : Nat → Tm → Ty → Tm
    P zero    t A = opTm 0 (mm D) t
    P (suc k) t A =
      rwI k (dim A) (P k t A) (TP k A) (L k (tgtAt k A) (baseAt k A))
          (cyl D (tgtAt k A)) (touched D (tgtAt k A))

    TP : Nat → Ty → Ty
    TP zero    A           = opTy 0 (mm D) A
    TP (suc k) ⋆           = ⋆
    TP (suc k) (arr A s u) =
      if k ==ℕ dim A
      then arr (TP k A) (P k s A) (L k u A)
      else arr (TP (suc k) A) (P (suc k) s A) (P (suc k) u A)

    L : Nat → Tm → Ty → Tm
    L zero    t A = opTm 0 (mp D) t
    L (suc k) t A =
      lwI k (dim A) (cyl D (srcAt k A)) (P k (srcAt k A) (baseAt k A))
          (L k t A) (TL k A) (touched D (srcAt k A))

    TL : Nat → Ty → Ty
    TL zero    A           = opTy 0 (mp D) A
    TL (suc k) ⋆           = ⋆
    TL (suc k) (arr A s u) =
      if k ==ℕ dim A
      then arr (TP k A) (P k s A) (L k u A)
      else arr (TL (suc k) A) (L (suc k) s A) (L (suc k) u A)

  aT bT : Tm → Ty → Tm
  aT t A = P (dim A) t A
  bT t A = L (dim A) t A

  -- The type of t↑ : a_t → b_t.
  cylTy : Tm → Ty → Ty
  cylTy t A = arr (TP (dim A) A) (aT t A) (bT t A)
