------------------------------------------------------------------------
-- Theorem S, generic part: the Gray/Biclosed kernel is sound in every
-- model of Model.agda (notes/free-objects-proofs.md §5.4–5.5).
--
-- A term t is interpreted, given values ε of the context variables, as
-- a semantic cell ⟦t⟧ : SC — an element of the model together with its
-- arity, dimension and gap (so that composition knows where the time
-- slot of a whiskered cell is).  A cell type A is interpreted as the
-- predicate Mem A on SC: op M is "typed by M"; hom m g A s t is "a
-- (dim A + 1)-cell at gap g whose faces are ⟦s⟧ and ⟦t⟧, both in A",
-- and, for m = inv, "with ⟦s⟧ ≈ ⟦t⟧" (inv read as flat).
--
-- Soundness (Soundness.agda): if ε satisfies Γ then every t with
-- infer Γ t ≡ just A has ⟦t⟧ ∈ Mem A.
------------------------------------------------------------------------
open import CaTTExp.Gray.Biclosed.Model

module CaTTExp.Gray.Biclosed.Sem (𝔐 : Model) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Gray.Biclosed.ListLemmas
open Model 𝔐
open import CaTTExp.Gray.Biclosed.ModelFacts 𝔐
open import CaTTExp.Gray.Biclosed.RowSem 𝔐

------------------------------------------------------------------------
-- Semantic cells

record SC : Set where
  constructor sc
  field
    val : V
    ar  : Nat     -- number of inputs of the underlying operation
    dm  : Nat     -- dimension
    gp  : Nat     -- gap of the time slot
open SC public

vals : List SC → List V
vals = map val

sumAr : List SC → Nat
sumAr []       = 0
sumAr (c ∷ cs) = ar c + sumAr cs

-- dimension and gap of a composite whose outer operation is 0-dimensional:
-- those of the first higher argument
hiD : List SC → Nat
hiD []                    = 0
hiD (sc _ _ zero    _ ∷ cs) = hiD cs
hiD (sc _ _ (suc k) _ ∷ cs) = suc k

hiG : List SC → Nat
hiG []                    = 0
hiG (sc _ a zero    _ ∷ cs) = a + hiG cs
hiG (sc _ _ (suc k) g ∷ cs) = g

compS : SC → List SC → SC
compS (sc F a zero    g) cs = sc (cmpFrom F 0 (vals cs)) (sumAr cs) (hiD cs) (hiG cs)
compS (sc F a (suc k) g) cs =
  sc (whS (suc k) F (vals (take g cs)) (vals (drop g cs))) (sumAr cs) (suc k) (sumAr (take g cs))

corSC : Cor → SC
corSC c = sc (cor c) (length (corIns c)) 0 0

idSC : Fm → SC
idSC A = sc (idv A) 1 0 0

-- the row with its formulas substituted
sRow : (Nat → Fm) → Row → Row
sRow φ (pairR L U W R Z)  = pairR (sFs φ L) (sF φ U) (sF φ W) (sFs φ R) (sF φ Z)
sRow φ (probeR L Δ Θ R Z) = probeR (sFs φ L) Δ Θ (sFs φ R) (sF φ Z)
sRow φ (unitR L R Z)      = unitR (sFs φ L) (sFs φ R) (sF φ Z)
sRow φ (evLR Φ A C)       = evLR (sFs φ Φ) (sF φ A) (sF φ C)
sRow φ (evRR Φ A C)       = evRR (sFs φ Φ) (sF φ A) (sF φ C)
sRow φ (shapeR L Θ R Z)   = shapeR (sFs φ L) Θ (sFs φ R) (sF φ Z)

gapIs : Nat → CTy → Set
gapIs g (op _)            = ⊤
gapIs g (hom _ g′ _ _ _)  = g′ ≡ g

record HomMem (m : Mode) (g : Nat) (A : CTy) (MA : SC → Set) (s t c : SC) : Set where
  field
    cell : CellAt (suc (dim A)) g (baseM A) (val c)
    mAr  : ar c ≡ length (ins (baseM A))
    mDm  : dm c ≡ suc (dim A)
    mGp  : gp c ≡ g
    gapA : gapIs g A
    memS : MA s
    memT : MA t
    fS   : pc (val c) g (δ false (dim A)) ≈ val s
    fT   : pc (val c) g (δ true (dim A)) ≈ val t
    flat : m ≡ inv → val s ≈ val t
open HomMem public

------------------------------------------------------------------------
-- Interpretation, given values of the context variables

module Interp (ε : Nat → SC) where

  nthS : List SC → Nat → SC
  nthS []       i       = ε i
  nthS (c ∷ cs) zero    = c
  nthS (c ∷ cs) (suc i) = nthS cs i

  hereS : Goal → Tmpl → List Fm → List SC → SC
  hereS gc t φs cs = sc (rinvS ρ′ (gap t) (dimn t) (val b)) (length (ins (H ρ′))) (dimn t) (gap t)
    where ρ′ = sRow (nthF φs) (row t)
          b  = nthS cs (pos (dimn t) 0)
  hereS gε t φs cs =
    sc (degen (dimn t) (rgap ρ′ (gap t)) (val b)) (length (ins (B ρ′))) (suc (dimn t)) (rgap ρ′ (gap t))
    where ρ′ = sRow (nthF φs) (row t)
          b  = nthS cs (pos (dimn t) 0)

  mutual
    ⟦_⟧ : Tm → SC
    ⟦ var i ⟧          = ε i
    ⟦ mP U W ⟧         = corSC (cm U W)
    ⟦ eL A C ⟧         = sc (evL A C) 2 0 0
    ⟦ eR A C ⟧         = sc (evR A C) 2 0 0
    ⟦ pP Δ Θ ⟧         = corSC (cp Δ Θ)
    ⟦ pt ⟧             = corSC cpt
    ⟦ iP Θ ⟧           = corSC (cι Θ)
    ⟦ idt A ⟧          = idSC A
    ⟦ comp f gs ⟧      = compS ⟦ f ⟧ ⟦ gs ⟧s
    ⟦ glue a x b ⟧     = ⟦ x ⟧
    ⟦ here t e φs ts ⟧ = hereS e t φs ⟦ ts ⟧s

    ⟦_⟧s : List Tm → List SC
    ⟦ [] ⟧s     = []
    ⟦ x ∷ xs ⟧s = ⟦ x ⟧ ∷ ⟦ xs ⟧s

  Mem : CTy → SC → Set
  Mem (op M)          c = (val c ∶ M) × (ar c ≡ length (ins M)) × (dm c ≡ 0)
  Mem (hom m g A s t) c = HomMem m g A (Mem A) ⟦ s ⟧ ⟦ t ⟧ c

  Mem-≡ : ∀ A {c c′} → c ≡ c′ → Mem A c → Mem A c′
  Mem-≡ A refl p = p
