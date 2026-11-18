------------------------------------------------------------------------
-- Examples for the discreteness filler (CaTTExp.GraphFiller).
--
-- Each `from-just (fill …)` typechecks only if the tactic produced a
-- term AND the certified checker accepted it as a cell of the stated
-- type, so every definition below is a genuine CaTT derivation.
------------------------------------------------------------------------
module CaTTExp.GraphFillerExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GraphFiller
import CaTTExp.Examples as Ex

v : Nat → Tm
v = var

-- Generic composition and identity over arbitrary arguments (the same
-- operations as in CaTTExp.Examples).
Comp₂ D₀ : Ctx
Comp₂ = chain 2
D₀    = chain 0

comp : Tm → Tm → Tm → Tm → Tm → Tm
comp x y f z g = coh Comp₂ (arr ⋆ (v 0) (v 3)) ⟪ x ∷ y ∷ f ∷ z ∷ g ∷ [] ⟫

id : Tm → Tm
id x = coh D₀ (arr ⋆ (v 0) (v 0)) ⟪ x ∷ [] ⟫

------------------------------------------------------------------------
-- The loop L = (x : ⋆, s : x → x): the presentation of ℕ.
-- Levels: x = 0, s = 1.

L : Ctx
L = ε ▸ ⋆ ▸ arr ⋆ (v 0) (v 0)

x s : Tm
x = v 0
s = v 1

_⨾_ : Tm → Tm → Tm
f ⨾ g = comp x x f x g

ss = s ⨾ s
[ss]s = (s ⨾ s) ⨾ s
s[ss] = s ⨾ (s ⨾ s)

hom : Ty
hom = arr ⋆ x x

-- Associativity of "3 = 2 + 1 = 1 + 2", with the loop traversed three
-- times: σ_p is not injective, which was the gap in the original
-- proof sketch.
assoc₃ : L ⊢tm _ ∶ arr hom [ss]s s[ss]
assoc₃ = snd (from-just (fill L [ss]s s[ss] hom))

-- The filler is exactly the associator of CaTTExp.Examples (over the
-- chain Θ₃ with full support), substituted along the path s, s, s.
_ : fst (from-just (fill L [ss]s s[ss] hom))
    ≡ coh Ex.Comp₃ Ex.assocTy ⟪ x ∷ x ∷ s ∷ x ∷ s ∷ x ∷ s ∷ [] ⟫
_ = refl

-- Units: 0 + 1 ⇒ 1 and 1 + 0 ⇒ 0 + 1.
lunit : L ⊢tm _ ∶ arr hom (id x ⨾ s) s
lunit = snd (from-just (fill L (id x ⨾ s) s hom))

unit-swap : L ⊢tm _ ∶ arr hom (s ⨾ id x) (id x ⨾ s)
unit-swap = snd (from-just (fill L (s ⨾ id x) (id x ⨾ s) hom))

-- Zero: id ⨾ id ⇒ id (the empty path).
zero-zero : L ⊢tm _ ∶ arr hom (id x ⨾ id x) (id x)
zero-zero = snd (from-just (fill L (id x ⨾ id x) (id x) hom))

-- A longer one, four letters, two bracketings with units inside.
long₁ long₂ : Tm
long₁ = ((s ⨾ id x) ⨾ s) ⨾ (s ⨾ s)
long₂ = s ⨾ (s ⨾ (id x ⨾ (s ⨾ s)))

long : L ⊢tm _ ∶ arr hom long₁ long₂
long = snd (from-just (fill L long₁ long₂ hom))

------------------------------------------------------------------------
-- Dimension 3: two parallel 2-cells over the same path are connected.
-- Take the associator itself and the associator composed with the
-- identity 2-cell on its target; the tactic produces a 3-cell.

a₃ : Tm
a₃ = fst (from-just (fill L [ss]s s[ss] hom))

-- Vertical composition of 2-cells α : f ⇒ g, β : g ⇒ h between x, y.
-- Over the pasting context x, y, f, g, α, h, β (levels 0..6).
VComp : Ctx
VComp = ctxOf (node (node (leaf ∷ leaf ∷ []) ∷ []))

vcomp : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
vcomp a b f g α h β =
  coh VComp (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 5)) ⟪ a ∷ b ∷ f ∷ g ∷ α ∷ h ∷ β ∷ [] ⟫

id₂ : Tm → Tm → Tm → Tm      -- identity 2-cell on f : a → b
id₂ a b f = coh (chain 1) (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 2)) ⟪ a ∷ b ∷ f ∷ [] ⟫

a₃' : Tm
a₃' = vcomp x x [ss]s s[ss] a₃ s[ss] (id₂ x x s[ss])

hom₂ : Ty
hom₂ = arr hom [ss]s s[ss]

-- Sanity: a₃' is a 2-cell of the same type as a₃.
_ : fst (from-just (infer L a₃')) ≡ hom₂
_ = refl

three-cell : L ⊢tm _ ∶ arr hom₂ a₃ a₃'
three-cell = snd (from-just (fill L a₃ a₃' hom₂))

-- Dimension 4: two different 3-cells a₃ ⇛ a₃'. The first is the
-- filler a₄ above; the second is the vertical composite of the filler
-- c₃₃ : a₃ ⇛ a₃ with a₄. The tactic connects them by a 4-cell.
a₄ c₃₃ : Tm
a₄  = fst (from-just (fill L a₃ a₃' hom₂))
c₃₃ = fst (from-just (fill L a₃ a₃ hom₂))

-- Vertical composition of 3-cells over x, y, f, g, α, β, Φ, γ, Ψ.
VComp₃ : Ctx
VComp₃ = ctxOf (node (node (node (leaf ∷ leaf ∷ []) ∷ []) ∷ []))

vcomp₃ : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
vcomp₃ a b f g α β Φ γ Ψ =
  coh VComp₃ (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)) (v 4) (v 7))
      ⟪ a ∷ b ∷ f ∷ g ∷ α ∷ β ∷ Φ ∷ γ ∷ Ψ ∷ [] ⟫

a₄' : Tm
a₄' = vcomp₃ x x [ss]s s[ss] a₃ a₃ c₃₃ a₃' a₄

hom₃ : Ty
hom₃ = arr hom₂ a₃ a₃'

_ : fst (from-just (infer L a₄')) ≡ hom₃
_ = refl

four-cell : L ⊢tm _ ∶ arr hom₃ a₄ a₄'
four-cell = snd (from-just (fill L a₄ a₄' hom₃))

------------------------------------------------------------------------
-- A graph with two vertices: x —f→ y —g→ x. Levels x0 y1 f2 g3.

G : Ctx
G = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1) ▸ arr ⋆ (v 1) (v 0)

fg-f f-gf : Tm
fg-f = comp (v 0) (v 0) (comp (v 0) (v 1) (v 2) (v 0) (v 3)) (v 1) (v 2)
f-gf = comp (v 0) (v 1) (v 2) (v 1) (comp (v 1) (v 0) (v 3) (v 1) (v 2))

graph-assoc : G ⊢tm _ ∶ arr (arr ⋆ (v 0) (v 1)) fg-f f-gf
graph-assoc = snd (from-just (fill G fg-f f-gf (arr ⋆ (v 0) (v 1))))

------------------------------------------------------------------------
-- Negative examples: the tactic rejects pairs whose paths differ.
-- (That no such cell exists in CaTT at all is the paper argument via the
-- path invariant, notes/ordinary-math.md §3.1; Agda only shows that the
-- tactic returns nothing.)

-- 2 vs 1: s ⨾ s and s.
_ : is-just (fill L ss s hom) ≡ false
_ = refl

-- 1 vs 0.
_ : is-just (fill L s (id x) hom) ≡ false
_ = refl

-- f ⨾ g and the identity on x are both loops at x in G, of different paths.
_ : is-just (fill G (comp (v 0) (v 1) (v 2) (v 0) (v 3)) (id (v 0)) (arr ⋆ (v 0) (v 0))) ≡ false
_ = refl
