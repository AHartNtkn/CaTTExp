------------------------------------------------------------------------
-- Examples for the truncation rules (CaTTExp.Trunc.Typing, ledger F9,
-- notes/ordinary-math.md §2.2 and §2.5).
--
-- Each positive example is `from-just (infer Γ t)` with its type
-- stated, so it typechecks only if the certified checker accepted t
-- at exactly that type. Negatives are `is-just (infer …) ≡ false`.
-- In every context below, variable 0 is the parameter object c and
-- variable 1 is the object C (or R) that may carry a mark.
------------------------------------------------------------------------
module CaTTExp.Trunc.Examples where

open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Pure using (∅; ⟪_⟫)
open Signature ∅
open import CaTTExp.GraphFillerExamples using (vcomp; id₂)

v : Nat → Tm
v = var

open import CaTTExp.Trunc.Check ∅

-- Marks are per context. In the contexts below C = var 1 is a set
-- (m = 2), a proposition (m = 1), contractible (m = 0), or unmarked.
at1 : Nat → Marks
at1 m (suc zero) = just m
at1 m _          = nothing

-- A context with its marks shifted: the same variable index (var 1) is
-- unmarked in another context, so marks are per declaration.
at2 : Nat → Marks
at2 m (suc (suc zero)) = just m
at2 m _                = nothing

-- The rules as term formers, in pure syntax.
fill : Nat → List Tm → Tm
fill k ts = coh (TF k) (TFty k) ⟪ ts ⟫

inv : Nat → List Tm → Tm
inv j ts = coh (TI j) (TIty j) ⟪ ts ⟫

ctr : Tm → Tm → Tm
ctr c C = coh TC TCty ⟪ c ∷ C ∷ [] ⟫

------------------------------------------------------------------------
-- 1. A set C, two maps f g : c → C and two cells α β : f ⇒ g.

S : Ctx
S = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1) ▸ arr ⋆ (v 0) (v 1)
      ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3) ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)

private
  c C f g α β : Tm
  c = v 0 ; C = v 1 ; f = v 2 ; g = v 3 ; α = v 4 ; β = v 5

hom : Ty
hom = arr ⋆ c C


-- T-fill at level 1: any two parallel cells are connected, both ways.
fill-αβ : S ∣ at1 2 ⊢tm fill 1 (c ∷ C ∷ f ∷ g ∷ α ∷ β ∷ []) ∶ arr (arr hom f g) α β
fill-αβ = from-just (check S (at1 2) _ _)

fill-βα : S ∣ at1 2 ⊢tm fill 1 (c ∷ C ∷ f ∷ g ∷ β ∷ α ∷ []) ∶ arr (arr hom f g) β α
fill-βα = from-just (check S (at1 2) _ _)

-- T-inv at level 1: α has an inverse g ⇒ f.
α⁻ : Tm
α⁻ = inv 0 (c ∷ C ∷ f ∷ g ∷ α ∷ [])

inv-α : S ∣ at1 2 ⊢tm α⁻ ∶ arr hom g f
inv-α = from-just (check S (at1 2) _ _)

-- The inverse laws are T-fill instances at level 1.
αα⁻ : Tm
αα⁻ = vcomp c C f g α f α⁻

law-l : S ∣ at1 2 ⊢tm fill 1 (c ∷ C ∷ f ∷ f ∷ αα⁻ ∷ id₂ c C f ∷ []) ∶ arr (arr hom f f) αα⁻ (id₂ c C f)
law-l = from-just (check S (at1 2) _ _)

-- A level-2 filler between the two fillers α ⇛ β (T-fill at level 2).
fill₂ : S ∣ at1 2 ⊢tm fill 2 (c ∷ C ∷ f ∷ g ∷ α ∷ β ∷ fill 1 (c ∷ C ∷ f ∷ g ∷ α ∷ β ∷ [])
                        ∷ fill 1 (c ∷ C ∷ f ∷ g ∷ α ∷ β ∷ []) ∷ [])
             ∶ arr (arr (arr hom f g) α β) (fill 1 (c ∷ C ∷ f ∷ g ∷ α ∷ β ∷ []))
                                           (fill 1 (c ∷ C ∷ f ∷ g ∷ α ∷ β ∷ []))
fill₂ = from-just (check S (at1 2) _ _)

-- Negatives.
-- Level 0 is below a set's filler level: no cell f ⇒ g.
_ : is-just (check S (at1 2) (fill 0 (c ∷ C ∷ f ∷ g ∷ [])) (arr hom f g)) ≡ false
_ = refl

-- Unmarked C: nothing fills α ⇛ β.
_ : is-just (infer S none (fill 1 (c ∷ C ∷ f ∷ g ∷ α ∷ β ∷ []))) ≡ false
_ = refl

-- No contraction for a set.
_ : is-just (infer S (at1 2) (ctr c C)) ≡ false
_ = refl

------------------------------------------------------------------------
-- 2. Lower marks.

-- A proposition: any two maps f g : c → C are connected (level 0).
prop-fg : S ∣ at1 1 ⊢tm fill 0 (c ∷ C ∷ f ∷ g ∷ []) ∶ arr hom f g
prop-fg = from-just (check S (at1 1) _ _)

-- Contractible: a map c → C exists.
ctr-c : S ∣ at1 0 ⊢tm ctr c C ∶ hom
ctr-c = from-just (check S (at1 0) _ _)

------------------------------------------------------------------------
-- 3. Eckmann–Hilton for free: two endo-cells α β : f ⇒ f of a map into
-- a set commute up to a cell, by T-fill.

E : Ctx
E = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1)
      ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 2) ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 2)

private
  e₁ e₂ : Tm
  e₁ = v 3 ; e₂ = v 4

  _·_ : Tm → Tm → Tm
  a · b = vcomp c C f f a f b

swap : E ∣ at1 2 ⊢tm fill 1 (c ∷ C ∷ f ∷ f ∷ (e₁ · e₂) ∷ (e₂ · e₁) ∷ []) ∶ arr (arr hom f f) (e₁ · e₂) (e₂ · e₁)
swap = from-just (check E (at1 2) _ _)

------------------------------------------------------------------------
-- 4. The §2.5 payoff, abstracted from products. For a monoid in a set R
-- the associator α : (xy)z ⇒ x(yz) is a cell between maps R³ → R, and
-- its pentagon compares two composites of whiskered associators, which
-- are cells between the five bracketings R⁴ → R. Products only decide
-- *which* maps and cells these are; T-fill needs only that they are
-- parallel cells into R of level 1. So take c for R⁴, five maps
-- p₁ … p₅ : c → R and the five pentagon cells as variables:
--   a₁ : p₁ ⇒ p₂, a₂ : p₂ ⇒ p₃   (one side)
--   a₃ : p₁ ⇒ p₄, a₄ : p₄ ⇒ p₅, a₅ : p₅ ⇒ p₃   (other side).

Pent : Ctx
Pent = ε ▸ ⋆ ▸ ⋆ ▸ hom ▸ hom ▸ hom ▸ hom ▸ hom
         ▸ arr hom (v 2) (v 3) ▸ arr hom (v 3) (v 4)
         ▸ arr hom (v 2) (v 5) ▸ arr hom (v 5) (v 6) ▸ arr hom (v 6) (v 4)

private
  p₁ p₂ p₃ p₄ p₅ a₁ a₂ a₃ a₄ a₅ lhs rhs : Tm
  p₁ = v 2 ; p₂ = v 3 ; p₃ = v 4 ; p₄ = v 5 ; p₅ = v 6
  a₁ = v 7 ; a₂ = v 8 ; a₃ = v 9 ; a₄ = v 10 ; a₅ = v 11
  lhs = vcomp c C p₁ p₂ a₁ p₃ a₂
  rhs = vcomp c C p₁ p₅ (vcomp c C p₁ p₄ a₃ p₅ a₄) p₃ a₅

pentagon : Pent ∣ at1 2 ⊢tm fill 1 (c ∷ C ∷ p₁ ∷ p₃ ∷ lhs ∷ rhs ∷ []) ∶ arr (arr hom p₁ p₃) lhs rhs
pentagon = from-just (check Pent (at1 2) _ _)

-- Without the mark the same question has no answer from these rules.
_ : is-just (infer Pent none (fill 1 (c ∷ C ∷ p₁ ∷ p₃ ∷ lhs ∷ rhs ∷ []))) ≡ false
_ = refl

-- Marks are per declaration: marking var 2 (the map f) instead of var 1
-- does not make C a set, so the same filler is rejected.
_ : is-just (infer S (at2 2) (fill 1 (c ∷ C ∷ f ∷ g ∷ α ∷ β ∷ []))) ≡ false
_ = refl
