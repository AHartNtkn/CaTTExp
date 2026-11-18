------------------------------------------------------------------------
-- The Gray cube (notes/pseudo-vs-gray.md §3.4).
--
-- Γ₃ = ΣD¹ ∨ ΣD¹ ∨ ΣD¹ with α : f ⇒ f', β : g ⇒ g', γ : h ⇒ h'.
-- Its unfolding is the 3-cube D¹ ⊗ D¹ ⊗ D¹; the top generator α⊗β⊗γ
-- is a 4-cell of the ambient between two hexagons, each a vertical
-- composite of whiskered interchangers (and associators). The point
-- of the example: both hexagons are ordinary terms over pasting
-- contexts, and the 4-cell is a single operation-case coh, accepted in
-- one direction only.
------------------------------------------------------------------------
module CaTTExp.Gray.Cube where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure
open import CaTTExp.Gray.Examples using (vcomp)

v : Nat → Tm
v = var

------------------------------------------------------------------------
-- Ternary composite of 1-cells and the three single whiskerings.

-- x0 y1 f2 z3 g4 w5 h6
Comp₃ : Ctx
Comp₃ = ctxOf (node (leaf ∷ leaf ∷ leaf ∷ []))

c3 : (a0 a1 f a2 g a3 h : Tm) → Tm
c3 a0 a1 f a2 g a3 h = coh Comp₃ (arr ⋆ (v 0) (v 5)) ⟪ a0 ∷ a1 ∷ f ∷ a2 ∷ g ∷ a3 ∷ h ∷ [] ⟫

d0 d1 : Tree
d0 = leaf
d1 = node (leaf ∷ [])

-- a0 a1 f2 f'3 α4 a2 5 g6 a3 7 h8
WαCtx = ctxOf (node (d1 ∷ d0 ∷ d0 ∷ []))
Wα : (a0 a1 f f' α a2 g a3 h : Tm) → Tm
Wα a0 a1 f f' α a2 g a3 h =
  coh WαCtx (arr (arr ⋆ (v 0) (v 7)) (c3 (v 0) (v 1) (v 2) (v 5) (v 6) (v 7) (v 8))
                                     (c3 (v 0) (v 1) (v 3) (v 5) (v 6) (v 7) (v 8)))
      ⟪ a0 ∷ a1 ∷ f ∷ f' ∷ α ∷ a2 ∷ g ∷ a3 ∷ h ∷ [] ⟫

-- a0 a1 f2 a2 3 g4 g'5 β6 a3 7 h8
WβCtx = ctxOf (node (d0 ∷ d1 ∷ d0 ∷ []))
Wβ : (a0 a1 f a2 g g' β a3 h : Tm) → Tm
Wβ a0 a1 f a2 g g' β a3 h =
  coh WβCtx (arr (arr ⋆ (v 0) (v 7)) (c3 (v 0) (v 1) (v 2) (v 3) (v 4) (v 7) (v 8))
                                     (c3 (v 0) (v 1) (v 2) (v 3) (v 5) (v 7) (v 8)))
      ⟪ a0 ∷ a1 ∷ f ∷ a2 ∷ g ∷ g' ∷ β ∷ a3 ∷ h ∷ [] ⟫

-- a0 a1 f2 a2 3 g4 a3 5 h6 h'7 γ8
WγCtx = ctxOf (node (d0 ∷ d0 ∷ d1 ∷ []))
Wγ : (a0 a1 f a2 g a3 h h' γ : Tm) → Tm
Wγ a0 a1 f a2 g a3 h h' γ =
  coh WγCtx (arr (arr ⋆ (v 0) (v 5)) (c3 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
                                     (c3 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 7)))
      ⟪ a0 ∷ a1 ∷ f ∷ a2 ∷ g ∷ a3 ∷ h ∷ h' ∷ γ ∷ [] ⟫

------------------------------------------------------------------------
-- The three two-factor interchangers, with the third factor a point.

v2 : (a0 a3 P Q p R q : Tm) → Tm
v2 = vcomp

-- α, β, then h:  a0 0 a1 1 f2 f'3 α4 a2 5 g6 g'7 β8 a3 9 h10
IαβCtx = ctxOf (node (d1 ∷ d1 ∷ d0 ∷ []))
Iαβ : Sub → Tm
Iαβ σ = coh IαβCtx
  (arr (arr (arr ⋆ (v 0) (v 9)) fgh f'g'h)
       (v2 (v 0) (v 9) fgh fg'h (Wβ (v 0) (v 1) (v 2) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10))
                       f'g'h (Wα (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 7) (v 9) (v 10)))
       (v2 (v 0) (v 9) fgh f'gh (Wα (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 9) (v 10))
                       f'g'h (Wβ (v 0) (v 1) (v 3) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10))))
  σ
  where
  fgh fg'h f'gh f'g'h : Tm
  fgh   = c3 (v 0) (v 1) (v 2) (v 5) (v 6) (v 9) (v 10)
  fg'h  = c3 (v 0) (v 1) (v 2) (v 5) (v 7) (v 9) (v 10)
  f'gh  = c3 (v 0) (v 1) (v 3) (v 5) (v 6) (v 9) (v 10)
  f'g'h = c3 (v 0) (v 1) (v 3) (v 5) (v 7) (v 9) (v 10)

-- α, g, γ:  a0 0 a1 1 f2 f'3 α4 a2 5 g6 a3 7 h8 h'9 γ10
IαγCtx = ctxOf (node (d1 ∷ d0 ∷ d1 ∷ []))
Iαγ : Sub → Tm
Iαγ σ = coh IαγCtx
  (arr (arr (arr ⋆ (v 0) (v 7)) fgh f'gh')
       (v2 (v 0) (v 7) fgh fgh' (Wγ (v 0) (v 1) (v 2) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10))
                       f'gh' (Wα (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 9)))
       (v2 (v 0) (v 7) fgh f'gh (Wα (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8))
                       f'gh' (Wγ (v 0) (v 1) (v 3) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10))))
  σ
  where
  fgh fgh' f'gh f'gh' : Tm
  fgh   = c3 (v 0) (v 1) (v 2) (v 5) (v 6) (v 7) (v 8)
  fgh'  = c3 (v 0) (v 1) (v 2) (v 5) (v 6) (v 7) (v 9)
  f'gh  = c3 (v 0) (v 1) (v 3) (v 5) (v 6) (v 7) (v 8)
  f'gh' = c3 (v 0) (v 1) (v 3) (v 5) (v 6) (v 7) (v 9)

-- f, β, γ:  a0 0 a1 1 f2 a2 3 g4 g'5 β6 a3 7 h8 h'9 γ10
IβγCtx = ctxOf (node (d0 ∷ d1 ∷ d1 ∷ []))
Iβγ : Sub → Tm
Iβγ σ = coh IβγCtx
  (arr (arr (arr ⋆ (v 0) (v 7)) fgh fg'h')
       (v2 (v 0) (v 7) fgh fgh' (Wγ (v 0) (v 1) (v 2) (v 3) (v 4) (v 7) (v 8) (v 9) (v 10))
                       fg'h' (Wβ (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 9)))
       (v2 (v 0) (v 7) fgh fg'h (Wβ (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8))
                       fg'h' (Wγ (v 0) (v 1) (v 2) (v 3) (v 5) (v 7) (v 8) (v 9) (v 10))))
  σ
  where
  fgh fgh' fg'h fg'h' : Tm
  fgh   = c3 (v 0) (v 1) (v 2) (v 3) (v 4) (v 7) (v 8)
  fgh'  = c3 (v 0) (v 1) (v 2) (v 3) (v 4) (v 7) (v 9)
  fg'h  = c3 (v 0) (v 1) (v 2) (v 3) (v 5) (v 7) (v 8)
  fg'h' = c3 (v 0) (v 1) (v 2) (v 3) (v 5) (v 7) (v 9)

------------------------------------------------------------------------
-- Operations on 2- and 3-cells of the hom (a0, a3) of Γ₃. Cells carry
-- their boundaries so composites can be written without re-deriving
-- types by hand.

-- Γ₃: a0 0 a1 1 f2 f'3 α4 a2 5 g6 g'7 β8 a3 9 h10 h'11 γ12
Γ₃ : Ctx
Γ₃ = ctxOf (node (d1 ∷ d1 ∷ d1 ∷ []))

a0 a3 : Tm
a0 = v 0
a3 = v 9

record C2 : Set where
  constructor c2
  field
    m s t : Tm          -- m : s ⇒ t, with s t : a0 → a3
open C2

record C3 : Set where
  constructor c3'
  field
    M : Tm              -- M : Src ⇛ Tgt
    Src Tgt : C2
open C3

_⨾_ : C2 → C2 → C2
p ⨾ q = c2 (v2 a0 a3 (s p) (t p) (m p) (t q) (m q)) (s p) (t q)

-- x0 y1 X2 Y3 p4 p'5 Φ6 Z7 c8      (Φ : p ⇛ p', then c)
RW2 = ctxOf (node (node (node (leaf ∷ []) ∷ leaf ∷ []) ∷ []))
-- x0 y1 X2 Y3 a4 Z5 q6 q'7 Ψ8      (a, then Ψ : q ⇛ q')
LW2 = ctxOf (node (node (leaf ∷ node (leaf ∷ []) ∷ []) ∷ []))
-- x0 y1 X2 Y3 p4 q5 Φ6 r7 Ψ8       (Φ : p ⇛ q, Ψ : q ⇛ r)
V3  = ctxOf (node (node (node (leaf ∷ leaf ∷ []) ∷ []) ∷ []))
-- x0 y1 X2 Y3 a4 Z5 b6 W7 c8       (three 2-cells)
A3  = ctxOf (node (node (leaf ∷ leaf ∷ leaf ∷ []) ∷ []))

_▷_ : C3 → C2 → C3
Φ ▷ c = c3'
  (coh RW2 (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 7))
                (v2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 7) (v 8))
                (v2 (v 0) (v 1) (v 2) (v 3) (v 5) (v 7) (v 8)))
     ⟪ a0 ∷ a3 ∷ s (Src Φ) ∷ t (Src Φ) ∷ m (Src Φ) ∷ m (Tgt Φ) ∷ M Φ ∷ t c ∷ m c ∷ [] ⟫)
  (Src Φ ⨾ c) (Tgt Φ ⨾ c)

_◁_ : C2 → C3 → C3
a ◁ Ψ = c3'
  (coh LW2 (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 5))
                (v2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
                (v2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 7)))
     ⟪ a0 ∷ a3 ∷ s a ∷ t a ∷ m a ∷ t (Src Ψ) ∷ m (Src Ψ) ∷ m (Tgt Ψ) ∷ M Ψ ∷ [] ⟫)
  (a ⨾ Src Ψ) (a ⨾ Tgt Ψ)

infixr 4 _∙_
_∙_ : C3 → C3 → C3
Φ ∙ Ψ = c3'
  (coh V3 (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)) (v 4) (v 7))
     ⟪ a0 ∷ a3 ∷ s (Src Φ) ∷ t (Src Φ) ∷ m (Src Φ) ∷ m (Tgt Φ) ∷ M Φ ∷ m (Tgt Ψ) ∷ M Ψ ∷ [] ⟫)
  (Src Φ) (Tgt Ψ)

private
  aL aR : Tm   -- (a;b);c and a;(b;c) in A3
  aL = v2 (v 0) (v 1) (v 2) (v 5) (v2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) (v 7) (v 8)
  aR = v2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 7) (v2 (v 0) (v 1) (v 3) (v 5) (v 6) (v 7) (v 8))

  A3σ : C2 → C2 → C2 → Sub
  A3σ a b c = ⟪ a0 ∷ a3 ∷ s a ∷ t a ∷ m a ∷ t b ∷ m b ∷ t c ∷ m c ∷ [] ⟫

assoc assoc⁻¹ : C2 → C2 → C2 → C3
assoc   a b c = c3' (coh A3 (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 7)) aL aR) (A3σ a b c))
                    ((a ⨾ b) ⨾ c) (a ⨾ (b ⨾ c))
assoc⁻¹ a b c = c3' (coh A3 (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 7)) aR aL) (A3σ a b c))
                    (a ⨾ (b ⨾ c)) ((a ⨾ b) ⨾ c)

------------------------------------------------------------------------
-- The cells of the cube in Γ₃.

f f' g g' h h' : Tm
f = v 2 ; f' = v 3 ; g = v 6 ; g' = v 7 ; h = v 10 ; h' = v 11

C : Tm → Tm → Tm → Tm
C p q r = c3 a0 (v 1) p (v 5) q a3 r

-- 2-cells (atoms of dimension 1 in D¹⊗D¹⊗D¹)
αgh αg'h αgh' αg'h' fβh f'βh fβh' f'βh' fgγ f'gγ fg'γ f'g'γ : C2
αgh   = c2 (Wα a0 (v 1) f f' (v 4) (v 5) g  a3 h ) (C f g  h ) (C f' g  h )
αg'h  = c2 (Wα a0 (v 1) f f' (v 4) (v 5) g' a3 h ) (C f g' h ) (C f' g' h )
αgh'  = c2 (Wα a0 (v 1) f f' (v 4) (v 5) g  a3 h') (C f g  h') (C f' g  h')
αg'h' = c2 (Wα a0 (v 1) f f' (v 4) (v 5) g' a3 h') (C f g' h') (C f' g' h')
fβh   = c2 (Wβ a0 (v 1) f  (v 5) g g' (v 8) a3 h ) (C f  g h ) (C f  g' h )
f'βh  = c2 (Wβ a0 (v 1) f' (v 5) g g' (v 8) a3 h ) (C f' g h ) (C f' g' h )
fβh'  = c2 (Wβ a0 (v 1) f  (v 5) g g' (v 8) a3 h') (C f  g h') (C f  g' h')
f'βh' = c2 (Wβ a0 (v 1) f' (v 5) g g' (v 8) a3 h') (C f' g h') (C f' g' h')
fgγ   = c2 (Wγ a0 (v 1) f  (v 5) g  a3 h h' (v 12)) (C f  g  h) (C f  g  h')
f'gγ  = c2 (Wγ a0 (v 1) f' (v 5) g  a3 h h' (v 12)) (C f' g  h) (C f' g  h')
fg'γ  = c2 (Wγ a0 (v 1) f  (v 5) g' a3 h h' (v 12)) (C f  g' h) (C f  g' h')
f'g'γ = c2 (Wγ a0 (v 1) f' (v 5) g' a3 h h' (v 12)) (C f' g' h) (C f' g' h')

-- The six faces (whiskered interchangers): X ⊗ Y ⊗ point.
αβh αβh' αgγ αg'γ fβγ f'βγ : C3
αβh   = c3' (Iαβ ⟪ a0 ∷ v 1 ∷ f ∷ f' ∷ v 4 ∷ v 5 ∷ g ∷ g' ∷ v 8 ∷ a3 ∷ h  ∷ [] ⟫)
            (fβh ⨾ αg'h) (αgh ⨾ f'βh)
αβh'  = c3' (Iαβ ⟪ a0 ∷ v 1 ∷ f ∷ f' ∷ v 4 ∷ v 5 ∷ g ∷ g' ∷ v 8 ∷ a3 ∷ h' ∷ [] ⟫)
            (fβh' ⨾ αg'h') (αgh' ⨾ f'βh')
αgγ   = c3' (Iαγ ⟪ a0 ∷ v 1 ∷ f ∷ f' ∷ v 4 ∷ v 5 ∷ g  ∷ a3 ∷ h ∷ h' ∷ v 12 ∷ [] ⟫)
            (fgγ ⨾ αgh') (αgh ⨾ f'gγ)
αg'γ  = c3' (Iαγ ⟪ a0 ∷ v 1 ∷ f ∷ f' ∷ v 4 ∷ v 5 ∷ g' ∷ a3 ∷ h ∷ h' ∷ v 12 ∷ [] ⟫)
            (fg'γ ⨾ αg'h') (αg'h ⨾ f'g'γ)
fβγ   = c3' (Iβγ ⟪ a0 ∷ v 1 ∷ f  ∷ v 5 ∷ g ∷ g' ∷ v 8 ∷ a3 ∷ h ∷ h' ∷ v 12 ∷ [] ⟫)
            (fgγ ⨾ fβh') (fβh ⨾ fg'γ)
f'βγ  = c3' (Iβγ ⟪ a0 ∷ v 1 ∷ f' ∷ v 5 ∷ g ∷ g' ∷ v 8 ∷ a3 ∷ h ∷ h' ∷ v 12 ∷ [] ⟫)
            (f'gγ ⨾ f'βh') (f'βh ⨾ f'g'γ)

------------------------------------------------------------------------
-- The two hexagons, from γ;β;α to α;β;γ, both bracketed (_⨾_)⨾_ at
-- the ends.

-- ∂⁻ of the cube: faces fβγ, αg'γ, αβh.
hex⁻ : C3
hex⁻ =     (fβγ ▷ αg'h')
         ∙ assoc fβh fg'γ αg'h'
         ∙ (fβh ◁ αg'γ)
         ∙ assoc⁻¹ fβh αg'h f'g'γ
         ∙ (αβh ▷ f'g'γ)

-- ∂⁺ of the cube: faces αβh', αgγ, f'βγ.
hex⁺ : C3
hex⁺ =     assoc fgγ fβh' αg'h'
         ∙ (fgγ ◁ αβh')
         ∙ assoc⁻¹ fgγ αgh' f'βh'
         ∙ (αgγ ▷ f'βh')
         ∙ assoc αgh f'gγ f'βh'
         ∙ (αgh ◁ f'βγ)
         ∙ assoc⁻¹ αgh f'βh f'g'γ

-- Both are well-typed 3-cells, with the same boundary.
hex⁻-wf = snd (from-just (infer Γ₃ (M hex⁻)))
hex⁺-wf = snd (from-just (infer Γ₃ (M hex⁺)))

_ : Src hex⁻ ≡ Src hex⁺
_ = refl
_ : Tgt hex⁻ ≡ Tgt hex⁺
_ = refl

------------------------------------------------------------------------
-- The cube: a 4-cell hex⁻ ⇛ hex⁺, operation case over Γ₃.

cubeTy cubeTy⁻ : Ty
cubeTy  = arr (arr (arr (arr ⋆ a0 a3) (s (Src hex⁻)) (t (Src hex⁻))) (m (Src hex⁻)) (m (Tgt hex⁻)))
              (M hex⁻) (M hex⁺)
cubeTy⁻ = arr (arr (arr (arr ⋆ a0 a3) (s (Src hex⁻)) (t (Src hex⁻))) (m (Src hex⁻)) (m (Tgt hex⁻)))
              (M hex⁺) (M hex⁻)

cube-wf : Γ₃ ⊢tm coh Γ₃ cubeTy (idₛ Γ₃) ∶ cubeTy
cube-wf = snd (from-just (infer Γ₃ (coh Γ₃ cubeTy (idₛ Γ₃))))

-- The reverse 4-cell is not derivable as a coh, in any context.
cube⁻-side : graySide Γ₃ (arr (arr (arr ⋆ a0 a3) (s (Src hex⁻)) (t (Src hex⁻))) (m (Src hex⁻)) (m (Tgt hex⁻)))
                       (M hex⁺) (M hex⁻) ≡ false
cube⁻-side = refl

-- The generator-based and closure-based comparisons agree on both.
_ : agreeSide Γ₃ (arr (arr (arr ⋆ a0 a3) (s (Src hex⁻)) (t (Src hex⁻))) (m (Src hex⁻)) (m (Tgt hex⁻)))
              (M hex⁻) (M hex⁺) ≡ true
_ = refl
_ : agreeSide Γ₃ (arr (arr (arr ⋆ a0 a3) (s (Src hex⁻)) (t (Src hex⁻))) (m (Src hex⁻)) (m (Tgt hex⁻)))
              (M hex⁺) (M hex⁻) ≡ true
_ = refl

no-cube⁻ : ∀ {Γ σ B} → ¬ (Γ ⊢tm coh Γ₃ cubeTy⁻ σ ∶ B)
no-cube⁻ (coh-wf _ _ _ ok _) = subst T cube⁻-side ok
