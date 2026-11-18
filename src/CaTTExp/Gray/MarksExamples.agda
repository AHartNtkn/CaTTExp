------------------------------------------------------------------------
-- The worked examples of notes/invertibility-markings.md §1.6, checked
-- by evaluating the mark judgments of CaTTExp.Gray.Marks.
------------------------------------------------------------------------
module CaTTExp.Gray.MarksExamples where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure
open import CaTTExp.Gray.Marks ∅
open import CaTTExp.Gray.Examples
  using (HComp; ich; VComp; vcomp; LW; lw; RW; rw; D₁)

v : Nat → Tm
v = var

M : Marks → Ctx → Marks × Ctx
M ms Γ = ms , Γ

------------------------------------------------------------------------
-- (a), (c): the interchanger over ΣD¹ ∨ ΣD¹.
-- Levels: x0 y1 f2 f'3 α4 z5 g6 g'7 β8. The top generator is α ⊗ β,
-- α first in execution order. Read as Example 1: α = an element arrow
-- φ of B, β = a transformation F ⇒ G.

-- unmarked: neither inv nor ps (directed; the reverse is underivable)
_ : M [] HComp ⊢ ich inv ≡ false
_ = refl
_ : M [] HComp ⊢ ich ps ≡ false
_ = refl

-- the later factor (the transformation) marked ps: PS-fac, inv
_ : M ((8 , mps) ∷ []) HComp ⊢ ich inv ≡ true
_ = refl

-- the earlier factor (the element arrow) marked inv: INV-fac, inv
_ : M ((4 , minv) ∷ []) HComp ⊢ ich inv ≡ true
_ = refl

-- the later factor marked inv: INV-fac, inv
_ : M ((8 , minv) ∷ []) HComp ⊢ ich inv ≡ true
_ = refl

-- (c) one-sidedness: only the *earlier* factor marked ps is not enough
_ : M ((4 , mps) ∷ []) HComp ⊢ ich inv ≡ false
_ = refl

-- the interchanger is then also ps (INV⇒PS, hd = 2)
_ : M ((8 , mps) ∷ []) HComp ⊢ ich ps ≡ true
_ = refl

------------------------------------------------------------------------
-- (b) composites of pseudo transformations.

-- vertical composite of two ps 2-cells (VComp: x0 y1 f2 g3 a4 h5 b6)
vc : Tm
vc = vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)

_ : M ((4 , mps) ∷ (6 , mps) ∷ []) VComp ⊢ vc ps ≡ true
_ = refl
_ : M ((4 , mps) ∷ (6 , mps) ∷ []) VComp ⊢ vc inv ≡ false
_ = refl
-- one unmarked factor: not ps
_ : M ((4 , mps) ∷ []) VComp ⊢ vc ps ≡ false
_ = refl

-- identity 2-cell on f : x → y (coherence case): inv, hence ps
idf : Tm
idf = coh D₁ (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 2)) (idₛ D₁)

_ : M [] D₁ ⊢ idf inv ≡ true
_ = refl
_ : M [] D₁ ⊢ idf ps ≡ true
_ = refl

-- whiskering α ▷ K with α ps (RW: x0 y1 f2 f'3 α4 z5 g6)
_ : M ((4 , mps) ∷ []) RW ⊢ rw (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) ps ≡ true
_ = refl
-- whiskering K ; β with β ps (LW: x0 y1 f2 z3 g4 g'5 β6)
_ : M ((6 , mps) ∷ []) LW ⊢ lw (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) ps ≡ true
_ = refl
-- unmarked whiskerings are neither
_ : M [] RW ⊢ rw (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) ps ≡ false
_ = refl

------------------------------------------------------------------------
-- (e) grpd_k objects. A 2-cell w : f ⇒ g : X → R (levels X0 R1 f2 g3
-- w4) with R marked grpd_1 is inv by OBJ-1; the 1-cells are not.

D₂ : Ctx
D₂ = ctxOf (node (node (leaf ∷ []) ∷ []))

_ : M ((1 , mgrpd 1) ∷ []) D₂ ⊢ v 4 inv ≡ true
_ = refl
_ : M ((1 , mgrpd 1) ∷ []) D₂ ⊢ v 2 inv ≡ false
_ = refl
-- grpd_2 does not make the 2-cell invertible
_ : M ((1 , mgrpd 2) ∷ []) D₂ ⊢ v 4 inv ≡ false
_ = refl

-- A naturality cell landing in a hom into a grpd_1 object is inv: the
-- interchanger with its last object z (level 5) marked grpd_1.
_ : M ((5 , mgrpd 1) ∷ []) HComp ⊢ ich inv ≡ true
_ = refl
