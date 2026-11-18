------------------------------------------------------------------------
-- Examples for the orientation family L_ε (CaTTExp.Gray.Orient).
------------------------------------------------------------------------
module CaTTExp.Gray.OrientExamples where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure
open import CaTTExp.Gray.Orient ∅
open import CaTTExp.Gray.Examples using (HComp; Txz; fg; f'g'; βα; αβ)

v : Nat → Tm
v = var

-- Orientations: odd hom-dimensions reversed, even ones reversed, only 2.
oddO evenO only2 : Orient
oddO  = odd
evenO = λ i → not (odd i)
only2 = λ i → i ==ℕ 2

-- L: the lax interchanger βα ⇛ αβ, not its reverse.
_ : graySideε (λ _ → false) HComp (arr Txz fg f'g') βα αβ ≡ true
_ = refl
_ : graySideε (λ _ → false) HComp (arr Txz fg f'g') αβ βα ≡ false
_ = refl

-- Alternating ε is L^rev: the oplax interchanger αβ ⇛ βα only.
_ : graySideε oddO HComp (arr Txz fg f'g') βα αβ ≡ false
_ = refl
_ : graySideε oddO HComp (arr Txz fg f'g') αβ βα ≡ true
_ = refl
_ : graySideε evenO HComp (arr Txz fg f'g') βα αβ ≡ false
_ = refl
_ : graySideε evenO HComp (arr Txz fg f'g') αβ βα ≡ true
_ = refl

-- Reversing hom-dimension 2 only: the interchanger is itself a hom-2
-- cell, so it is reversed (D_{3} of L's interchanger), as for L^rev.
_ : graySideε only2 HComp (arr Txz fg f'g') βα αβ ≡ false
_ = refl
_ : graySideε only2 HComp (arr Txz fg f'g') αβ βα ≡ true
_ = refl

------------------------------------------------------------------------
-- The twisted tensor of closed-structure.md D.1, K = {2}, on D¹ ⊗ D³:
-- "α⊗s₂ gets the boundary orientation of ⊗^rev, not of ⊗; α⊗c₃ gets
-- the orientation of ⊗, not of ⊗^rev". α⊗s₂ is the total cell of
-- D¹ ⊗ D², α⊗c₃ that of D¹ ⊗ D³. We compare the codimension-1 chains.

private
  rev : ∀ {A : Set} → List A → List A
  rev []       = []
  rev (x ∷ xs) = rev xs ++ (x ∷ [])

  -- the table of the factor-reversed tensor, in the original coordinates
  chainRev : Bool → Nat → List Hom → TSet
  chainRev sg k hs = map rev (chainT sg k (rev hs))

  D : Nat → Tree
  D zero    = leaf
  D (suc n) = node (D n ∷ [])

  -- ΣDᵖ ∨ ΣD^q
  W : Nat → Nat → Ctx
  W p q = ctxOf (node (D p ∷ D q ∷ []))

  bd : (Bool → Nat → List Hom → TSet) → Nat → Nat → Bool → TSet
  bd ch p q sg = ch sg (p + q ∸ 1) (homs (W p q))

  sameT : TSet → TSet → Bool
  sameT = ≈T

-- α ⊗ s₂ (D¹ ⊗ D²): like ⊗^rev, unlike ⊗
_ : sameT (bd (chainTε only2) 1 2 false) (bd chainRev 1 2 false) ≡ true
_ = refl
_ : sameT (bd (chainTε only2) 1 2 true) (bd chainRev 1 2 true) ≡ true
_ = refl
_ : sameT (bd (chainTε only2) 1 2 false) (bd chainT 1 2 false) ≡ false
_ = refl

-- α ⊗ c₃ (D¹ ⊗ D³): like ⊗, unlike ⊗^rev
_ : sameT (bd (chainTε only2) 1 3 false) (bd chainT 1 3 false) ≡ true
_ = refl
_ : sameT (bd (chainTε only2) 1 3 true) (bd chainT 1 3 true) ≡ true
_ = refl
_ : sameT (bd (chainTε only2) 1 3 false) (bd chainRev 1 3 false) ≡ false
_ = refl

------------------------------------------------------------------------
-- Alternating ε is L^rev on whole tables: every codimension-1 chain of
-- T_ε equals that of the factor-reversed tensor, for wedges of globes.

private
  Wl : List Nat → Ctx
  Wl ds = ctxOf (node (map D ds))

  bdl : (Bool → Nat → List Hom → TSet) → List Nat → Bool → TSet
  bdl ch ds sg = ch sg (dimK (homs (Wl ds)) ∸ 1) (homs (Wl ds))

  isRev isL : Orient → List Nat → Bool
  isRev o ds = sameT (bdl (chainTε o) ds false) (bdl chainRev ds false)
             ∧ sameT (bdl (chainTε o) ds true) (bdl chainRev ds true)
  isL o ds   = sameT (bdl (chainTε o) ds false) (bdl chainT ds false)
             ∧ sameT (bdl (chainTε o) ds true) (bdl chainT ds true)

  shapes : List (List Nat)
  shapes = (1 ∷ 1 ∷ []) ∷ (1 ∷ 2 ∷ []) ∷ (2 ∷ 1 ∷ []) ∷ (2 ∷ 2 ∷ []) ∷ (1 ∷ 3 ∷ [])
         ∷ (3 ∷ 1 ∷ []) ∷ (1 ∷ 1 ∷ 1 ∷ []) ∷ (1 ∷ 2 ∷ 1 ∷ []) ∷ (2 ∷ 1 ∷ 1 ∷ []) ∷ []

_ : all (isRev oddO) shapes ≡ true
_ = refl
_ : all (isRev evenO) shapes ≡ true
_ = refl
-- …and the constant orientations are L (proved in general in Gray.Orient)
_ : all (isL (λ _ → true)) shapes ≡ true
_ = refl
-- the twisted orientation only2 is neither on D¹ ⊗ D² ⊗ D¹
_ : isL only2 (1 ∷ 2 ∷ 1 ∷ []) ≡ false
_ = refl
_ : isRev only2 (1 ∷ 2 ∷ 1 ∷ []) ≡ false
_ = refl
