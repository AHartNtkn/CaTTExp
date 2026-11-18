------------------------------------------------------------------------
-- The cut lemma (notes/conjectures/answered/
-- steiner-support-formalizable-2026-11-18.md, §2).
--
-- In a pasting context Γ, with the basis order _<ₒ_ of Strict.Order
-- (negative faces before, positive faces after), take adjacent rows
-- u = x_q⁻, v = x_q⁺ and c = x_{q+1} of a cell, so ∂⁺c + u = ∂⁻c + v.
-- For a tuple a, the cut
--
--     cut a u v c = (v + ∂⁻(c≥a))|_{<a} + (u + ∂⁺(c<a))|_{≥a}
--
-- is u + ∂(c<a) (`cut-eq`), it has coefficient u[a] + (∂⁺c)[a] at a
-- (`cut-at`), and replacing the top row of the q-cell (rows < q of x,
-- top u) by it gives a q-cell (`cut-cell`).
------------------------------------------------------------------------
module CaTTExp.Strict.Cut where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.DD
open import CaTTExp.Strict.TopCell using (_⊎_; inj₁; inj₂; Pos)
open import CaTTExp.Strict.CohCase using (count-∈L; All-∈L; ∈L-++r)
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.Gray.Cover using (Any) renaming (here to hereA; there to thereA)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_)

------------------------------------------------------------------------
-- Membership.

∈L-++ : ∀ A {B x} → x ∈L (A ++ B) → (x ∈L A) ⊎ (x ∈L B)
∈L-++ []      m          = inj₂ m
∈L-++ (a ∷ A) (hereA e)  = inj₁ (hereA e)
∈L-++ (a ∷ A) (thereA m) with ∈L-++ A m
... | inj₁ p = inj₁ (thereA p)
... | inj₂ q = inj₂ q

∈L-consB : ∀ v Y {z} → z ∈L consB v Y → Σ Tuple λ z' → (z ≡ v ∷ z') × (z' ∈L Y)
∈L-consB v (y ∷ Y) (hereA refl) = y , refl , hereA refl
∈L-consB v (y ∷ Y) (thereA m) with ∈L-consB v Y m
... | z' , e , m' = z' , e , thereA m'

------------------------------------------------------------------------
-- Faces of basis elements are basis elements one degree lower.

private
  data VShape (Γ : Ctx) (v : Nat) : Set where
    flatS : facesTy (lookup Γ v) ≡ nothing → VShape Γ v
    deep  : ∀ B a b s t → lookup Γ v ≡ just (arr (arr B a b) (var s) (var t)) →
            lookup Γ s ≡ just (arr B a b) → lookup Γ t ≡ just (arr B a b) → VShape Γ v

  vshape : ∀ {Γ} → PsInv Γ → ∀ v → VShape Γ v
  vshape {Γ} inv v = go (lookup Γ v) refl
    where
    go : ∀ m → lookup Γ v ≡ m → VShape Γ v
    go nothing            e = flatS (cong facesTy e)
    go (just ⋆)           e = flatS (cong facesTy e)
    go (just (arr ⋆ _ _)) e = flatS (cong facesTy e)
    go (just (arr (arr B a b) s t)) e with inv v _ e
    ... | (i , j , refl , refl , li , lj) = deep B a b i j e li lj

face-wft : ∀ {Γ} → PsInv Γ → ∀ σ x y w {z} → WFT Γ x y w → z ∈L ∂T Γ σ w →
           WFT Γ x y z × (suc (deg Γ z) ≡ deg Γ w)
face-wft inv σ x y [] _ ()
face-wft {Γ} inv σ x y (v ∷ w) {z} (m , ev , p) mz
  with ∈L-++ (here σ (facesTy (lookup Γ v)) w) mz
... | inj₂ mc with ∈L-consB v (∂T Γ (flipN (hdimV Γ v) σ) w) mc
...   | z' , refl , m' with face-wft inv (flipN (hdimV Γ v) σ) m y w p m'
...     | wz , dz = (m , ev , wz) , trans (sym (+-suc (hdimV Γ v) (deg Γ z'))) (cong (hdimV Γ v +_) dz)
face-wft {Γ} inv σ x y (v ∷ w) {z} (m , ev , p) mz | inj₁ mh with vshape inv v
... | flatS e = ⊥-elim (none (subst (λ F → z ∈L here σ F w) e mh))
  where
  none : z ∈L [] → ⊥
  none ()
... | deep B a b s t lv ls lt = go σ (subst (λ F → z ∈L here σ F w) (cong facesTy lv) mh)
  where
  ev' : endsV (arr B a b) ≡ just (x , m)
  ev' = trans (cong endsL (sym lv)) ev
  hv : hdimV Γ v ≡ suc (hdimV Γ s)
  hv = trans (cong hdimTy lv) (cong (λ q → suc (hdimTy q)) (sym ls))
  go : ∀ σ' → z ∈L here σ' (just (s , t)) w → WFT Γ x y z × (suc (deg Γ z) ≡ deg Γ (v ∷ w))
  go true  (hereA refl) =
    (m , trans (cong endsL lt) ev' , p) ,
    cong (_+ deg Γ w) (trans (cong (λ q → suc (hdimTy q)) (trans lt (sym ls))) (sym hv))
  go false (hereA refl) =
    (m , trans (cong endsL ls) ev' , p) , cong (_+ deg Γ w) (sym hv)
  go true  (thereA ())
  go false (thereA ())

face-basis : ∀ {Γ} → PsInv Γ → ∀ σ x y k w {z} → Basis Γ x y (suc k) w → z ∈L ∂T Γ σ w → Basis Γ x y k z
face-basis inv σ x y k w (wf , dw) mz with face-wft inv σ x y w wf mz
... | wz , dz = wz , suc-inj (trans dz dw)
  where
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl
