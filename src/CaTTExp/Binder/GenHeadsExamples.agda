------------------------------------------------------------------------
-- Examples for the generic diagram η_Γ (CaTTExp.Binder.GenHeads),
-- checked by the certified checker with plain CaTT's side condition
-- and rule (MARK). Every statement is `refl`.
--
--  * Γ = D¹ (x, y, f : x → y): η_x, η_y : ⊤ → ⟦D¹⟧ and
--    η_f : η_x ⇒ η_y, a 2-cell between elements of ⟦D¹⟧; each is well
--    typed (its type is checked as well).
--  * Γ = (x, y, f, z, g, h : x → z, α : f ; g ⇒ h): η_α's type has the
--    suspended composite of η_f and η_g as its source, a coherence in
--    the hom 𝒦(⊤, ⟦Γ⟧); η_α is well typed.
--  * Rejections: an entry past the end of Γ; an ill-formed Γ; a
--    telescope on η or ⊤.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.GenHeads
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (extend)
open import CaTTExp.Examples using (Comp₂; comp)

module CaTTExp.Binder.GenHeadsExamples where

𝕊 : Signature
𝕊 = extend P.∅ (genBinders P.K)

open Signature 𝕊
open GenConstruction K GenF (λ b → b)
open import CaTTExp.Binder.Typing 𝕊
open import CaTTExp.Binder.CheckWith 𝕊 cattSide varMark

inferTy : Ctx → Tm → Maybe Ty
inferTy Γ t = infer Γ t >>= λ r → just (fst r)

wellTyped : Ctx → Tm → Bool
wellTyped Γ t with ctx? Γ | inferTy Γ t
... | just w | just A = is-just (checkTy (sizeTy A) Γ w A)
... | _      | _      = false

pv : Nat → P.Tm
pv = P.var

------------------------------------------------------------------------
-- D¹.

D1 : P.Ctx
D1 = P.ε P.▸ P.⋆ P.▸ P.⋆ P.▸ P.arr P.⋆ (pv 0) (pv 1)

η : Nat → Tm
η = genId D1

el : Ty
el = arr ⋆ topT (freeP D1)

d1-types : (inferTy ε (η 0) ∷ inferTy ε (η 1) ∷ inferTy ε (η 2) ∷ [])
         ≡ (just el ∷ just el ∷ just (arr el (η 0) (η 1)) ∷ [])
d1-types = refl

d1-wf : (wellTyped ε (η 0) ∷ wellTyped ε (η 1) ∷ wellTyped ε (η 2) ∷ []) ≡ (true ∷ true ∷ true ∷ [])
d1-wf = refl

-- In a context: η_f still has its type (the heads are closed).
d1-ctx : inferTy (ε ▸ ⋆ ▸ arr ⋆ (var 0) (var 0)) (η 2) ≡ just (arr el (η 0) (η 1))
d1-ctx = refl

------------------------------------------------------------------------
-- A 2-cell whose source is a composite.

Γc : P.Ctx
Γc = Comp₂ P.▸ P.arr P.⋆ (pv 0) (pv 3)
           P.▸ P.arr (P.arr P.⋆ (pv 0) (pv 3)) (comp (pv 0) (pv 1) (pv 2) (pv 3) (pv 4)) (pv 5)

ηc : Nat → Tm
ηc = genId Γc

comp-wf : (wellTyped ε (ηc 4) ∷ wellTyped ε (ηc 5) ∷ wellTyped ε (ηc 6) ∷ []) ≡ (true ∷ true ∷ true ∷ [])
comp-wf = refl

------------------------------------------------------------------------
-- Rejections.

bad : P.Ctx
bad = P.ε P.▸ P.⋆ P.▸ P.arr P.⋆ (pv 0) (pv 1)   -- y not declared

rejected : ( is-just (inferTy ε (η 3))                                   -- no entry 3
           ∷ is-just (inferTy ε (genId bad 0))                           -- Γ ill formed
           ∷ is-just (inferTy ε (bnd (gen D1) 0 (ε ▸ ⋆) ⟨⟩))             -- a telescope
           ∷ is-just (inferTy ε (bnd unit 0 (ε ▸ ⋆) ⟨⟩))                 -- a telescope on ⊤
           ∷ [])
         ≡ (false ∷ false ∷ false ∷ false ∷ [])
rejected = refl
