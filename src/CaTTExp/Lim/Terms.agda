------------------------------------------------------------------------
-- A few CaTT operations and coherences, as terms over named variables.
-- Each is `coh` over a pasting context built from a tree, applied to
-- the given arguments (listed in the pasting context's order).
------------------------------------------------------------------------
module CaTTExp.Lim.Terms where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)

private
  v : Nat → Tm
  v = var

  ⋆⇒ : Nat → Nat → Ty
  ⋆⇒ a b = arr ⋆ (v a) (v b)

------------------------------------------------------------------------
-- Pasting contexts (levels in comments).

-- x
PD₀ : Ctx
PD₀ = ctxOf leaf

-- x f y               x0 y1 f2
PD₁ : Ctx
PD₁ = ctxOf (node (leaf ∷ []))

-- x —f→ y —g→ z       x0 y1 f2 z3 g4
PComp : Ctx
PComp = ctxOf (node (leaf ∷ leaf ∷ []))

-- α : f ⇒ g          x0 y1 f2 g3 α4
PD₂ : Ctx
PD₂ = ctxOf (node (node (leaf ∷ []) ∷ []))

-- p then α           a0 b1 p2 c3 f4 g5 α6     (p ▷ α : p f ⇒ p g)
PWhL : Ctx
PWhL = ctxOf (node (leaf ∷ node (leaf ∷ []) ∷ []))

-- α then q           a0 b1 f2 g3 α4 c5 q6     (α ◁ q : f q ⇒ g q)
PWhR : Ctx
PWhR = ctxOf (node (node (leaf ∷ []) ∷ leaf ∷ []))

-- α ; β vertical     x0 y1 f2 g3 α4 h5 β6
PVComp : Ctx
PVComp = ctxOf (node (node (leaf ∷ leaf ∷ []) ∷ []))

-- Θ ; Ξ vertical 3-cells: x0 y1 f2 g3 α4 β5 Θ6 γ7 Ξ8
PVComp₃ : Ctx
PVComp₃ = ctxOf (node (node (node (leaf ∷ leaf ∷ []) ∷ []) ∷ []))

-- z then w            c0 Y1 r2 s3 a4 b5 z6 s'7 w8   (z ◁₁ w : a;w ⇛ b;w)
PWh₃ : Ctx
PWh₃ = ctxOf (node (node (node (leaf ∷ []) ∷ leaf ∷ []) ∷ []))

_ : PWhL ≡ (ε ▸ ⋆ ▸ ⋆ ▸ ⋆⇒ 0 1 ▸ ⋆ ▸ ⋆⇒ 1 3 ▸ ⋆⇒ 1 3 ▸ arr (⋆⇒ 1 3) (v 4) (v 5))
_ = refl

_ : PWhR ≡ (ε ▸ ⋆ ▸ ⋆ ▸ ⋆⇒ 0 1 ▸ ⋆⇒ 0 1 ▸ arr (⋆⇒ 0 1) (v 2) (v 3) ▸ ⋆ ▸ ⋆⇒ 1 5)
_ = refl

_ : PWh₃ ≡ (ε ▸ ⋆ ▸ ⋆ ▸ ⋆⇒ 0 1 ▸ ⋆⇒ 0 1 ▸ arr (⋆⇒ 0 1) (v 2) (v 3)
             ▸ arr (⋆⇒ 0 1) (v 2) (v 3) ▸ arr (arr (⋆⇒ 0 1) (v 2) (v 3)) (v 4) (v 5)
             ▸ ⋆⇒ 0 1 ▸ arr (⋆⇒ 0 1) (v 3) (v 7))
_ = refl

------------------------------------------------------------------------
-- Operations. Arguments are given in pasting-context order.

-- 1_x
idc : (x : Tm) → Tm
idc x = coh PD₀ (⋆⇒ 0 0) ⟪ x ∷ [] ⟫

-- f · g  (diagrammatic)
comp : (x y f z g : Tm) → Tm
comp x y f z g = coh PComp (⋆⇒ 0 3) ⟪ x ∷ y ∷ f ∷ z ∷ g ∷ [] ⟫

private
  comp₀ : (x y f z g : Nat) → Tm
  comp₀ x y f z g = comp (v x) (v y) (v f) (v z) (v g)

-- p ▷ α : p f ⇒ p g
whL : (a b p c f g α : Tm) → Tm
whL a b p c f g α =
  coh PWhL (arr (⋆⇒ 0 3) (comp₀ 0 1 2 3 4) (comp₀ 0 1 2 3 5))
    ⟪ a ∷ b ∷ p ∷ c ∷ f ∷ g ∷ α ∷ [] ⟫

-- α ◁ q : f q ⇒ g q
whR : (a b f g α c q : Tm) → Tm
whR a b f g α c q =
  coh PWhR (arr (⋆⇒ 0 5) (comp₀ 0 1 2 5 6) (comp₀ 0 1 3 5 6))
    ⟪ a ∷ b ∷ f ∷ g ∷ α ∷ c ∷ q ∷ [] ⟫

-- α ; β : f ⇒ h
vcomp : (x y f g α h β : Tm) → Tm
vcomp x y f g α h β =
  coh PVComp (arr (⋆⇒ 0 1) (v 2) (v 5)) ⟪ x ∷ y ∷ f ∷ g ∷ α ∷ h ∷ β ∷ [] ⟫

-- Θ ; Ξ : α ⇛ γ
vcomp₃ : (x y f g α β Θ γ Ξ : Tm) → Tm
vcomp₃ x y f g α β Θ γ Ξ =
  coh PVComp₃ (arr (arr (⋆⇒ 0 1) (v 2) (v 3)) (v 4) (v 7))
    ⟪ x ∷ y ∷ f ∷ g ∷ α ∷ β ∷ Θ ∷ γ ∷ Ξ ∷ [] ⟫

-- z ◁₁ w : a ; w ⇛ b ; w
wh₃ : (c Y r s a b z s' w : Tm) → Tm
wh₃ c Y r s a b z s' w =
  coh PWh₃ (arr (arr (⋆⇒ 0 1) (v 2) (v 7))
                (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 7) (v 8))
                (vcomp (v 0) (v 1) (v 2) (v 3) (v 5) (v 7) (v 8)))
    ⟪ c ∷ Y ∷ r ∷ s ∷ a ∷ b ∷ z ∷ s' ∷ w ∷ [] ⟫

-- Inverse right unitor  ρ⁻¹_f : f ⇒ f · 1_y  (a full coherence over PD₁).
runitInv : (x y f : Tm) → Tm
runitInv x y f =
  coh PD₁ (arr (⋆⇒ 0 1) (v 2) (comp₀' 0 1 2 1))
    ⟪ x ∷ y ∷ f ∷ [] ⟫
  where
  comp₀' : Nat → Nat → Nat → Nat → Tm
  comp₀' x y f z = comp (v x) (v y) (v f) (v y) (idc (v y))

-- Naturality of ρ⁻¹ at a 2-cell a : r ⇒ s  (a full coherence over PD₂):
--   ρ⁻¹_r ; (a ◁ 1_Y)  ⇛  a ; ρ⁻¹_s
runitNat : (c Y r s a : Tm) → Tm
runitNat c Y r s a =
  coh PD₂ (arr (arr (⋆⇒ 0 1) (v 2) r1₃)
               (vcomp (v 0) (v 1) (v 2) r1₂ (runitInv (v 0) (v 1) (v 2)) r1₃
                      (whR (v 0) (v 1) (v 2) (v 3) (v 4) (v 1) (idc (v 1))))
               (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) r1₃ (runitInv (v 0) (v 1) (v 3))))
    ⟪ c ∷ Y ∷ r ∷ s ∷ a ∷ [] ⟫
  where
  r1₂ r1₃ : Tm
  r1₂ = comp (v 0) (v 1) (v 2) (v 1) (idc (v 1))
  r1₃ = comp (v 0) (v 1) (v 3) (v 1) (idc (v 1))
