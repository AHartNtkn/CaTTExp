------------------------------------------------------------------------
-- Naturality cylinders of terms (Conjecture N, ledger C1): the raw
-- construction, in every dimension.
--
-- Notation as in notes/conjectures/naturality-arbitrary-depth.md §2
-- and notes/relative-coherence.md §4. A *cylinder datum* D on a
-- context Γ, landing in a context Δ, is
--
--   mm, mp : Sub    two substitutions Δ → Γ, the copies t⁻ = t[mm]
--                   and t⁺ = t[mp];
--   sel    : the selected (up-closed) set Y of variables of Γ;
--   th     : for each selected variable x, its cylinder x↑ in Δ.
--
-- For a term t of Γ, `cyl D t` is its cylinder t↑. It is defined by
-- structural recursion on t:
--
--   cyl D (var x)       = th x
--   cyl D (coh Q B γ)   = K Q B Y' [ γ↑ ]
--
-- where Y' = { q : γ(q) uses a selected variable } (`mask`), γ↑ is the
-- substitution Q↑Y' → Δ sending q ↦ γ(q)⁻, γ(q)⁺, γ(q)↑ for q ∈ Y' and
-- q ↦ γ(q)⁻ otherwise (`liftS`), and K is a *filler family*: for every
-- pasting context Q, full type B and selection Y', a term of the
-- cylinder context Q↑Y' (`cylCtx`) of type a_c → b_c, c = coh Q B id.
-- K is a parameter. CaTTExp.Naturality.Typing proves that cyl D t has
-- type a_t → b_t whenever K is scoped and well typed (FillerOK) and D is
-- valid. A filler family for the coherences of dimension 1 is built in
-- CaTTExp.Naturality.DimOne (Proposition R of relative-coherence.md
-- §4.1, with RC(1) connectors); fillers for coherences of dimension ≥ 2
-- are not built yet (ledger C1d item (2)).
--
-- The boundary cells a_t, b_t are the nested whiskers of §2.2:
--
--   a_t = ( … ((t⁻ ∗₀ (τⁿ t)↑) ∗₁ (τⁿ⁻¹ t)↑) … ) ∗_{n−1} (τ t)↑
--   b_t = (σ t)↑ ∗_{n−1} ( … ((σⁿ⁻¹ t)↑ ∗₁ ((σⁿ t)↑ ∗₀ t⁺)) … )
--
-- built with the typed whiskers rwT, lwT of CaTTExp.DerivedBoundary.
-- A factor w↑ with w untouched by the selection is omitted, as in the
-- notes (no identity is inserted). P k t A is the right prefix through
-- dimension k − 1, L k t A the left one, TP k A the type of P k t A.
------------------------------------------------------------------------
module CaTTExp.Naturality.Raw where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (idS)
open import CaTTExp.DerivedBoundary using (rwT; lwT)

------------------------------------------------------------------------
-- Booleans over lists.

anyL : (Nat → Bool) → List Nat → Bool
anyL f []       = false
anyL f (x ∷ xs) = f x ∨ anyL f xs

------------------------------------------------------------------------
-- Selections over a context: one boolean per variable, in order.

infixl 5 _◂_
data Sel : Set where
  ◇   : Sel
  _◂_ : Sel → Bool → Sel

lenSel : Sel → Nat
lenSel ◇       = 0
lenSel (Y ◂ _) = suc (lenSel Y)

selAt : Sel → Nat → Bool
selAt ◇       i = false
selAt (Y ◂ b) i = if i ==ℕ lenSel Y then b else selAt Y i

anySel : Sel → Bool
anySel ◇       = false
anySel (Y ◂ b) = anySel Y ∨ b

-- Number of levels of the cylinder of a prefix: 3 per selected
-- variable (x⁻, x⁺, x↑), 1 per other variable.
cnt : Sel → Nat
cnt ◇           = 0
cnt (Y ◂ true)  = suc (suc (suc (cnt Y)))
cnt (Y ◂ false) = suc (cnt Y)

------------------------------------------------------------------------
-- Cylinder data and filler families.

record Datum : Set where
  constructor datum
  field
    mm mp : Sub
    sel   : Nat → Bool
    th    : Nat → Tm
open Datum public

Filler : Set
Filler = Ctx → Ty → Sel → Tm

------------------------------------------------------------------------
-- Iterated boundaries read off a type. For t : A and k < dim A,
-- tgtAt k A and srcAt k A are the k-dimensional target and source of
-- t, and baseAt k A (k ≤ dim A) is the type of the k-cells of A's
-- chain.

baseAt : Nat → Ty → Ty
baseAt k ⋆           = ⋆
baseAt k (arr A s u) = if k ==ℕ suc (dim A) then arr A s u else baseAt k A

tgtAt srcAt : Nat → Ty → Tm
tgtAt k ⋆           = var 0
tgtAt k (arr A s u) = if k ==ℕ dim A then u else tgtAt k A
srcAt k ⋆           = var 0
srcAt k (arr A s u) = if k ==ℕ dim A then s else srcAt k A

-- Whiskers that are omitted when the whiskering cell is untouched.
-- n is the dimension of c, k the whiskering dimension (k < n).
rwI : Nat → Nat → Tm → Ty → Tm → Tm → Bool → Tm
rwI k n c C z h true  = rwT k (n ∸ suc k) c C z h
rwI k n c C z h false = c

lwI : Nat → Nat → Tm → Tm → Tm → Ty → Bool → Tm
lwI k n h x c C true  = lwT k (n ∸ suc k) h x c C
lwI k n h x c C false = c

-- A closed junk term (scoped in every context).
junk : Tm
junk = coh ε ⋆ ⟨⟩

-- One entry of γ↑: three copies for a touched argument, one otherwise.
liftOne : Sub → Tm → Tm → Tm → Bool → Sub
liftOne ρ a b c true  = ρ ,ₛ a ,ₛ b ,ₛ c
liftOne ρ a b c false = ρ ,ₛ a

module Cyl (K : Filler) where

  touched : Datum → Tm → Bool
  touched D t = anyL (sel D) (fvTm t)

  mask : Datum → Sub → Sel
  mask D ⟨⟩       = ◇
  mask D (γ ,ₛ t) = mask D γ ◂ touched D t

  mutual
    cyl : Datum → Tm → Tm
    cyl D (var x)     = th D x
    cyl D (coh Q B γ) = K Q B (mask D γ) [ liftS D γ ]tm
    cyl D (cst ())

    liftS : Datum → Sub → Sub
    liftS D ⟨⟩       = ⟨⟩
    liftS D (γ ,ₛ t) = liftOne (liftS D γ) (t [ mm D ]tm) (t [ mp D ]tm) (cyl D t) (touched D t)

  --------------------------------------------------------------------
  -- Boundary cells.

  module _ (D : Datum) where
    mutual
      P : Nat → Tm → Ty → Tm
      P zero    t A = t [ mm D ]tm
      P (suc k) t A =
        rwI k (dim A) (P k t A) (TP k A) (L k (tgtAt k A) (baseAt k A))
            (cyl D (tgtAt k A)) (touched D (tgtAt k A))

      TP : Nat → Ty → Ty
      TP zero    A           = A [ mm D ]ty
      TP (suc k) ⋆           = ⋆
      TP (suc k) (arr A s u) =
        if k ==ℕ dim A
        then arr (TP k A) (P k s A) (L k u A)
        else arr (TP (suc k) A) (P (suc k) s A) (P (suc k) u A)

      L : Nat → Tm → Ty → Tm
      L zero    t A = t [ mp D ]tm
      L (suc k) t A =
        lwI k (dim A) (cyl D (srcAt k A)) (P k (srcAt k A) (baseAt k A))
            (L k t A) (TL k A) (touched D (srcAt k A))

      TL : Nat → Ty → Ty
      TL zero    A           = A [ mp D ]ty
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

  --------------------------------------------------------------------
  -- The cylinder context Q↑Y and its generic datum.

  genMm genMp genTh : Sel → Sub
  genMm ◇           = ⟨⟩
  genMm (Y ◂ b)     = genMm Y ,ₛ var (cnt Y)
  genMp ◇           = ⟨⟩
  genMp (Y ◂ true)  = genMp Y ,ₛ var (suc (cnt Y))
  genMp (Y ◂ false) = genMp Y ,ₛ var (cnt Y)
  genTh ◇           = ⟨⟩
  genTh (Y ◂ b)     = genTh Y ,ₛ var (suc (suc (cnt Y)))

  gen : Sel → Datum
  gen Y = datum (genMm Y) (genMp Y) (selAt Y) (lookupₛ (genTh Y))

  cylCtx : Ctx → Sel → Ctx
  cylCtx ε       _           = ε
  cylCtx (Q ▸ A) ◇           = ε
  cylCtx (Q ▸ A) (Y ◂ true)  =
    cylCtx Q Y ▸ A [ genMm Y ]ty ▸ A [ genMp Y ]ty ▸ cylTy (gen (Y ◂ true)) (var (len Q)) A
  cylCtx (Q ▸ A) (Y ◂ false) = cylCtx Q Y ▸ A [ genMm Y ]ty

  -- The coherence c = coh Q B id whose cylinder K Q B Y fills.
  cohId : Ctx → Ty → Tm
  cohId Q B = coh Q B (idS (len Q))
