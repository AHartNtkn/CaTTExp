------------------------------------------------------------------------
-- DES examples, checked by the certified checker with plain CaTT's
-- side condition and the mark judgment of rule (MARK) only
-- (CaTTExp.Binder.Typing). Every statement is `refl`.
--
--  * On a 1-cell f : x → y marked inv: f⁻ˡ, f⁻ʳ : y → x, and
--    λ_f : f⁻ˡ ; f → id_y, ρ_f : f ; f⁻ʳ → id_x. Their types are pinned,
--    and the checker accepts each type as well formed. So the
--    composites over the disk are derivable.
--  * The same on a 2-cell α : f ⇒ g marked inv.
--  * Rejections: f unmarked, or marked ps only (the inv premise of
--    (DES) fails); dimension 0; a non-zero selector; a non-empty
--    telescope; the wrong number of arguments.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Des
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (extend)

module CaTTExp.Binder.DesExamples where

𝕊 : Signature
𝕊 = extend P.∅ (desBinders P.K)

open Signature 𝕊
open DesConstruction K DesF (λ b → b) using (comp; idc)
open import CaTTExp.Binder.Typing 𝕊
open import CaTTExp.Binder.CheckWith 𝕊 cattSide varMark

inferTy : Ctx → Tm → Maybe Ty
inferTy Γ t = infer Γ t >>= λ r → just (fst r)

-- The inferred type, if any, is well formed.
wellTyped : Ctx → Tm → Bool
wellTyped Γ t with ctx? Γ | inferTy Γ t
... | just w | just A = is-just (checkTy (sizeTy A) Γ w A)
... | _      | _      = false

v : Nat → Tm
v = var

------------------------------------------------------------------------
-- A 1-cell.

Γ₁ : List Mark → Ctx
Γ₁ ms = ε ▸ ⋆ ▸ ⋆ ▸[ ms ] arr ⋆ (v 0) (v 1)

xyf : Sub
xyf = ⟨⟩ ,ₛ v 0 ,ₛ v 1 ,ₛ v 2

d1 : DesF → Tm
d1 b = bnd b 0 ε xyf

inv1 = Γ₁ (minv ∷ [])

linv-ty : inferTy inv1 (d1 (linv 1)) ≡ just (arr ⋆ (v 1) (v 0))
linv-ty = refl

rinv-ty : inferTy inv1 (d1 (rinv 1)) ≡ just (arr ⋆ (v 1) (v 0))
rinv-ty = refl

-- λ_f : f⁻ˡ ; f → id_y
unitL-ty : inferTy inv1 (d1 (unitL 1)) ≡
  just (arr (arr ⋆ (v 1) (v 1)) (comp 0 ⟨⟩ (v 1) (v 0) (d1 (linv 1)) (v 1) (v 2)) (idc 0 ⟨⟩ (v 1)))
unitL-ty = refl

-- ρ_f : f ; f⁻ʳ → id_x
unitR-ty : inferTy inv1 (d1 (unitR 1)) ≡
  just (arr (arr ⋆ (v 0) (v 0)) (comp 0 ⟨⟩ (v 0) (v 1) (v 2) (v 0) (d1 (rinv 1))) (idc 0 ⟨⟩ (v 0)))
unitR-ty = refl

wt1 : (wellTyped inv1 (d1 (linv 1)) ∷ wellTyped inv1 (d1 (rinv 1)) ∷
       wellTyped inv1 (d1 (unitL 1)) ∷ wellTyped inv1 (d1 (unitR 1)) ∷ [])
    ≡ (true ∷ true ∷ true ∷ true ∷ [])
wt1 = refl

-- The inv premise: unmarked, or marked ps only, is rejected.
no-mark : (is-just (infer (Γ₁ []) (d1 (linv 1))) ∷ is-just (infer (Γ₁ (mps ∷ [])) (d1 (unitL 1))) ∷ [])
        ≡ (false ∷ false ∷ [])
no-mark = refl

-- Dimension 0, selector ≠ 0, non-empty telescope, too few arguments.
no-shape : ( is-just (infer inv1 (bnd (linv 0) 0 ε (⟨⟩ ,ₛ v 0)))
           ∷ is-just (infer inv1 (bnd (linv 1) 1 ε xyf))
           ∷ is-just (infer inv1 (bnd (linv 1) 0 (ε ▸ ⋆) xyf))
           ∷ is-just (infer inv1 (bnd (linv 1) 0 ε (⟨⟩ ,ₛ v 0 ,ₛ v 1))) ∷ [])
         ≡ (false ∷ false ∷ false ∷ false ∷ [])
no-shape = refl

------------------------------------------------------------------------
-- A 2-cell α : f ⇒ g marked inv.

Γ₂ : Ctx
Γ₂ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1) ▸ arr ⋆ (v 0) (v 1)
       ▸[ minv ∷ [] ] arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)

d2 : DesF → Tm
d2 b = bnd b 0 ε (⟨⟩ ,ₛ v 0 ,ₛ v 1 ,ₛ v 2 ,ₛ v 3 ,ₛ v 4)

linv2-ty : inferTy Γ₂ (d2 (linv 2)) ≡ just (arr (arr ⋆ (v 0) (v 1)) (v 3) (v 2))
linv2-ty = refl

wt2 : (wellTyped Γ₂ (d2 (linv 2)) ∷ wellTyped Γ₂ (d2 (rinv 2)) ∷
       wellTyped Γ₂ (d2 (unitL 2)) ∷ wellTyped Γ₂ (d2 (unitR 2)) ∷ [])
    ≡ (true ∷ true ∷ true ∷ true ∷ [])
wt2 = refl

-- A 1-cell destructor does not apply to the 2-cell's arguments.
no-dim : is-just (infer Γ₂ (d2 (linv 1))) ≡ false
no-dim = refl
