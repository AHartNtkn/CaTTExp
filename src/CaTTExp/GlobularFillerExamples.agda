------------------------------------------------------------------------
-- Examples for the globular filler (CaTTExp.GlobularFiller, F2b).
--
-- Every cell below is returned with a derivation from the certified
-- checker, so it is a theorem of plain CaTT.
------------------------------------------------------------------------
module CaTTExp.GlobularFillerExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller
import CaTTExp.GraphFiller as GF
open import CaTTExp.GraphFillerExamples
  using (v; comp; id; L; x; s; hom; [ss]s; s[ss]; ss; vcomp; id₂)

------------------------------------------------------------------------
-- Graph contexts are globular: the dimension-2 examples of the graph
-- filler, and the same terms.

assoc₃ : L ⊢tm _ ∶ arr hom [ss]s s[ss]
assoc₃ = snd (from-just (fill L [ss]s s[ss] hom))

_ : fst (from-just (fill L [ss]s s[ss] hom)) ≡ fst (from-just (GF.fill L [ss]s s[ss] hom))
_ = refl

unit-swap : L ⊢tm _ ∶ arr hom (comp x x s x (id x)) (comp x x (id x) x s)
unit-swap = snd (from-just (fill L (comp x x s x (id x)) (comp x x (id x) x s) hom))

------------------------------------------------------------------------
-- Whiskering.

-- α ∗₀ g over x0 y1 f2 f'3 α4 z5 g6.
WhR : Ctx
WhR = ctxOf (node (node (leaf ∷ []) ∷ leaf ∷ []))

whR : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
whR a b f f' α c g =
  coh WhR (arr (arr ⋆ (v 0) (v 5)) (comp (v 0) (v 1) (v 2) (v 5) (v 6))
                                   (comp (v 0) (v 1) (v 3) (v 5) (v 6)))
      ⟪ a ∷ b ∷ f ∷ f' ∷ α ∷ c ∷ g ∷ [] ⟫

-- f ∗₀ β over x0 y1 f2 z3 g4 g'5 β6.
WhL : Ctx
WhL = ctxOf (node (leaf ∷ node (leaf ∷ []) ∷ []))

whL : Tm → Tm → Tm → Tm → Tm → Tm → Tm → Tm
whL a b f c g g' β =
  coh WhL (arr (arr ⋆ (v 0) (v 3)) (comp (v 0) (v 1) (v 2) (v 3) (v 4))
                                   (comp (v 0) (v 1) (v 2) (v 3) (v 5)))
      ⟪ a ∷ b ∷ f ∷ c ∷ g ∷ g' ∷ β ∷ [] ⟫

------------------------------------------------------------------------
-- Interchange. Γ is x0 y1 f2 f'3 α4 z5 g6 g'7 β8 with α : f ⇒ f',
-- β : g ⇒ g'. The two ways of composing α and β have the same strict
-- image (the horizontal composite), and the filler is an interchange
-- 3-cell.

I : Ctx
I = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1) ▸ arr ⋆ (v 0) (v 1) ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
      ▸ ⋆ ▸ arr ⋆ (v 1) (v 5) ▸ arr ⋆ (v 1) (v 5) ▸ arr (arr ⋆ (v 1) (v 5)) (v 6) (v 7)

private
  X Y Z F F' Α G G' Β : Tm
  X = v 0 ; Y = v 1 ; F = v 2 ; F' = v 3 ; Α = v 4 ; Z = v 5 ; G = v 6 ; G' = v 7 ; Β = v 8

  _⊙_ : Tm → Tm → Tm
  f ⊙ g = comp X Y f Z g

αβ βα : Tm
αβ = vcomp X Z (F ⊙ G) (F' ⊙ G) (whR X Y F F' Α Z G) (F' ⊙ G') (whL X Y F' Z G G' Β)
βα = vcomp X Z (F ⊙ G) (F ⊙ G') (whL X Y F Z G G' Β) (F' ⊙ G') (whR X Y F F' Α Z G')

homI : Ty
homI = arr (arr ⋆ X Z) (F ⊙ G) (F' ⊙ G')

_ : fst (from-just (infer I αβ)) ≡ homI
_ = refl

_ : fst (from-just (infer I βα)) ≡ homI
_ = refl

interchange : I ⊢tm _ ∶ arr homI αβ βα
interchange = snd (from-just (fill I αβ βα homI))

------------------------------------------------------------------------
-- A 2-loop: x0, s1 : x → x, α2 : s ⇒ s.

L₂ : Ctx
L₂ = L ▸ arr hom s s

private
  α : Tm
  α = v 2

  _·_ : Tm → Tm → Tm          -- vertical composite of 2-loops on s
  a · b = vcomp x x s s a s b

hom₂ : Ty
hom₂ = arr hom s s

-- Associativity of vertical composition.
v-assoc : L₂ ⊢tm _ ∶ arr hom₂ ((α · α) · α) (α · (α · α))
v-assoc = snd (from-just (fill L₂ ((α · α) · α) (α · (α · α)) hom₂))

-- Unit: α composed with the identity 2-cell on s.
v-unit : L₂ ⊢tm _ ∶ arr hom₂ (α · id₂ x x s) α
v-unit = snd (from-just (fill L₂ (α · id₂ x x s) α hom₂))

-- Interchange on the loop: (α ∗₀ s) · (s ∗₀ α) and (s ∗₀ α) · (α ∗₀ s)
-- both have strict image α ∗₀ α.
αs sα : Tm
αs = whR x x s s α x s
sα = whL x x s x s s α

homss : Ty
homss = arr hom (comp x x s x s) (comp x x s x s)

loop-interchange : L₂ ⊢tm _ ∶ arr homss (vcomp x x ss ss αs ss sα) (vcomp x x ss ss sα ss αs)
loop-interchange = snd (from-just (fill L₂ (vcomp x x ss ss αs ss sα) (vcomp x x ss ss sα ss αs) homss))

------------------------------------------------------------------------
-- Negative examples.

-- Different strict images: α · α and α.
_ : is-just (fill L₂ (α · α) α hom₂) ≡ false
_ = refl

-- A context that is not globular: x, β : 1_x ⇒ 1_x (the Eckmann–Hilton
-- context of ordinary-math.md §3.3). The tactic does not apply.
EH : Ctx
EH = ε ▸ ⋆ ▸ arr (arr ⋆ (v 0) (v 0)) (id (v 0)) (id (v 0))

_ : is-just (fill EH (v 1) (v 1) (arr (arr ⋆ (v 0) (v 0)) (id (v 0)) (id (v 0)))) ≡ false
_ = refl
