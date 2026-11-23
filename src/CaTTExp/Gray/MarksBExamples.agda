------------------------------------------------------------------------
-- Gray marks with destructors (CaTTExp.Gray.MarksB) on the DES
-- instance (CaTTExp.Binder.Des), checked by the certified checker with
-- L's side condition on binder syntax (graySideD) and the derived mark
-- judgment. Every statement is `refl`.
--
--  * (DES-inv), (DES): on f : x → y marked inv, f⁻ˡ and f⁻ʳ are inv, and
--    λ_f, ρ_f are inv and ps (2-cells, INV⇒PS).
--  * (COH-inv) through a destructor: f⁻ˡ ; f is inv.
--  * The derived judgment is what the kernel checks: with f, g marked
--    inv, (f ; g)⁻ˡ is accepted, because f ; g is inv by (COH-inv);
--    plain (MARK) (CaTTExp.Binder.DesExamples, varMark) rejects it.
--  * Unmarked f: f⁻ˡ is still rejected, and f is not inv.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Des
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (extend)

module CaTTExp.Gray.MarksBExamples where

𝕊 : Signature
𝕊 = extend P.∅ (desBinders P.K)

open Signature 𝕊
open DesConstruction K DesF (λ b → b) using (comp; idc)

desMarks : DesF → Nat → Ctx → List Mark
desMarks _ _ _ = minv ∷ []

open import CaTTExp.Gray.MarksB P.∅ (desBinders P.K) cellArgD desMarks
  using (mark; judgeT)
open import CaTTExp.Gray.DesSide P.∅ (desBinders P.K) cellArgD using (graySideD)
open import CaTTExp.Binder.CheckWith 𝕊 graySideD mark
open import CaTTExp.Binder.Typing 𝕊 using (cattSide)
import CaTTExp.Binder.CheckWith 𝕊 cattSide varMark as Plain

v : Nat → Tm
v = var

------------------------------------------------------------------------
-- f : x → y.

Γ₁ : List Mark → Ctx
Γ₁ ms = ε ▸ ⋆ ▸ ⋆ ▸[ ms ] arr ⋆ (v 0) (v 1)

inv1 = Γ₁ (minv ∷ [])

d1 : DesF → Tm
d1 b = bnd b 0 ε (⟨⟩ ,ₛ v 0 ,ₛ v 1 ,ₛ v 2)

marks : Ctx → Tm → List Bool
marks Γ t = mark Γ minv t ∷ mark Γ mps t ∷ []

-- f⁻ˡ, f⁻ʳ inv (1-cells: ps is not derived); λ_f, ρ_f inv and ps.
des-marks : (marks inv1 (d1 (linv 1)) ∷ marks inv1 (d1 (rinv 1)) ∷
             marks inv1 (d1 (unitL 1)) ∷ marks inv1 (d1 (unitR 1)) ∷ [])
          ≡ ((true ∷ false ∷ []) ∷ (true ∷ false ∷ []) ∷
             (true ∷ true ∷ []) ∷ (true ∷ true ∷ []) ∷ [])
des-marks = refl

-- f⁻ˡ ; f : y → y is inv by (COH-inv).
linv-f : Tm
linv-f = comp 0 ⟨⟩ (v 1) (v 0) (d1 (linv 1)) (v 1) (v 2)

coh-inv : mark inv1 minv linv-f ≡ true
coh-inv = refl

accepted : (is-just (infer inv1 (d1 (linv 1))) ∷ is-just (infer inv1 (d1 (unitL 1))) ∷
            is-just (infer inv1 linv-f) ∷ [])
         ≡ (true ∷ true ∷ true ∷ [])
accepted = refl

-- Unmarked f: not inv, and f⁻ˡ is rejected.
unmarked : (mark (Γ₁ []) minv (v 2) ∷ is-just (infer (Γ₁ []) (d1 (linv 1))) ∷ [])
         ≡ (false ∷ false ∷ [])
unmarked = refl

------------------------------------------------------------------------
-- f : x → y, g : y → z marked inv; f ; g is inv by (COH-inv), so its
-- left inverse is well formed. Plain (MARK) only sees variables.

Γfg : Ctx
Γfg = ε ▸ ⋆ ▸ ⋆ ▸[ minv ∷ [] ] arr ⋆ (v 0) (v 1) ▸ ⋆ ▸[ minv ∷ [] ] arr ⋆ (v 1) (v 3)

fg : Tm
fg = comp 0 ⟨⟩ (v 0) (v 1) (v 2) (v 3) (v 4)

linv-fg : Tm
linv-fg = bnd (linv 1) 0 ε (⟨⟩ ,ₛ v 0 ,ₛ v 3 ,ₛ fg)

composite : (mark Γfg minv fg ∷ is-just (infer Γfg linv-fg) ∷ is-just (Plain.infer Γfg linv-fg) ∷ [])
          ≡ (true ∷ true ∷ false ∷ [])
composite = refl
