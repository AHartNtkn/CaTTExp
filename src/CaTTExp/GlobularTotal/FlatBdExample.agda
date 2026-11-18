------------------------------------------------------------------------
-- A concrete inhabitant of FlatBd.Good, so the hypothesis of flat-bd
-- is not vacuous: the composable pair x →f y →g z (the tree of Comp,
-- labelled as idTree labels it: x=0, y=1, f=2, z=3, g=4) with the
-- identity images.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.FlatBdExample where

open import CaTTExp.Prelude
open import CaTTExp.GlobularFiller using (LT; lt; bd; bdL)
open import CaTTExp.GlobularTotal.TreeAlg using (WF)
open import CaTTExp.GlobularTotal.FlatBd

leaf : Nat → LT
leaf y = lt (y ∷ []) []

-- The labelled tree of x →f y →g z.
T₂ : LT
T₂ = lt (0 ∷ 1 ∷ 3 ∷ []) (leaf 2 ∷ leaf 4 ∷ [])

-- Identity images: objects are points, f and g are arrows.
I : Nat → Maybe LT
I 2 = just (lt (0 ∷ 1 ∷ []) (leaf 2 ∷ []))
I 4 = just (lt (1 ∷ 3 ∷ []) (leaf 4 ∷ []))
I y = just (leaf y)

private
  bd-leaf : ∀ β i y → bd β i (leaf y) ≡ leaf y
  bd-leaf false zero    y = refl
  bd-leaf true  zero    y = refl
  bd-leaf false (suc i) y = refl
  bd-leaf true  (suc i) y = refl

  dim-pt : ∀ y → Dim I 0 (leaf y)
  dim-pt y β i = bd-leaf β i y

  dim-arr : ∀ a b f → Dim I 1 (lt (a ∷ b ∷ []) (leaf f ∷ []))
  dim-arr a b f false i = cong (λ c → lt (a ∷ b ∷ []) (c ∷ [])) (bd-leaf false i f)
  dim-arr a b f true  i = cong (λ c → lt (a ∷ b ∷ []) (c ∷ [])) (bd-leaf true  i f)

  wf-pt : ∀ y → WF (leaf y)
  wf-pt y = refl , tt

  wf-arr : ∀ a b f → WF (lt (a ∷ b ∷ []) (leaf f ∷ []))
  wf-arr a b f = refl , wf-pt f , tt

good : Good I 0 (λ _ → ⊤) T₂
good =
  ( (leaf 0 , refl , wf-pt 0 , dim-pt 0 , tt)
  , (leaf 1 , refl , wf-pt 1 , dim-pt 1 , tt)
  , (leaf 3 , refl , wf-pt 3 , dim-pt 3 , tt)
  , tt )
  , ( ((_ , refl , wf-arr 0 1 2 , dim-arr 0 1 2 , refl , refl) , tt) , tt )
  , ( ((_ , refl , wf-arr 1 3 4 , dim-arr 1 3 4 , refl , refl) , tt) , tt )
  , tt

-- The composite is g ∘ f, and flat-bd applies.
gf : LT
gf = lt (0 ∷ 1 ∷ 3 ∷ []) (leaf 2 ∷ leaf 4 ∷ [])

flat-T₂ : flatG I 0 T₂ ≡ just gf
flat-T₂ = refl

src-gf : flatG I 0 (bd false 0 T₂) ≡ just (bd false 0 gf)
src-gf = snd (flat-bd I 0 (λ _ → ⊤) T₂ gf good refl) false 0
