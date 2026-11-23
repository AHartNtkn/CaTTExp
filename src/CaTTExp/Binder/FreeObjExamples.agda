------------------------------------------------------------------------
-- Examples for the free-object head (CaTTExp.Binder.FreeObj), checked
-- by the certified checker with plain CaTT's side condition and rule
-- (MARK). Every statement is `refl`.
--
--  * ⟦D⁰⟧, ⟦D¹⟧, ⟦D²⟧ and the free object on a composable pair are
--    objects; the free object on an arrow with its cell marked inv
--    (the walking isomorphism's presentation) is accepted.
--  * Maps ⟦D⁰⟧ → ⟦D¹⟧ (the two endpoint inclusions, as variables) and
--    a 2-cell between them are typed in a context.
--  * Rejections: an open Γ (it mentions a variable of the surrounding
--    context); an ill-formed Γ (f : x → y with y not declared); a
--    non-zero selector; an argument.
--  * Conservativity over plain CaTT.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.FreeObj
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (extend)

module CaTTExp.Binder.FreeObjExamples where

𝕊 : Signature
𝕊 = extend P.∅ (freeBinders P.K)

open Signature 𝕊
open FreeConstruction K FreeF (λ b → b)
open import CaTTExp.Binder.Typing 𝕊
open import CaTTExp.Binder.CheckWith 𝕊 cattSide varMark

inferTy : Ctx → Tm → Maybe Ty
inferTy Γ t = infer Γ t >>= λ r → just (fst r)

b : Nat → Tm
b = bvar 0

D0 D1 D2 pair arrowInv : Ctx
D0 = ε ▸ ⋆
D1 = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (b 0) (b 1)
D2 = D1 ▸ arr ⋆ (b 0) (b 1) ▸ arr (arr ⋆ (b 0) (b 1)) (b 2) (b 3)
pair = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (b 0) (b 1) ▸ ⋆ ▸ arr ⋆ (b 1) (b 3)
arrowInv = ε ▸ ⋆ ▸ ⋆ ▸[ minv ∷ [] ] arr ⋆ (b 0) (b 1)

objects : ( inferTy ε ⟦ D0 ⟧ ∷ inferTy ε ⟦ D1 ⟧ ∷ inferTy ε ⟦ D2 ⟧
          ∷ inferTy ε ⟦ pair ⟧ ∷ inferTy ε ⟦ arrowInv ⟧ ∷ [])
        ≡ (just ⋆ ∷ just ⋆ ∷ just ⋆ ∷ just ⋆ ∷ just ⋆ ∷ [])
objects = refl

-- s, t : ⟦D⁰⟧ → ⟦D¹⟧ and a 2-cell α : s ⇒ t.
Γst : Ctx
Γst = ε ▸ arr ⋆ ⟦ D0 ⟧ ⟦ D1 ⟧ ▸ arr ⋆ ⟦ D0 ⟧ ⟦ D1 ⟧ ▸ arr (arr ⋆ ⟦ D0 ⟧ ⟦ D1 ⟧) (var 0) (var 1)

maps-ctx : is-just (ctx? Γst) ≡ true
maps-ctx = refl

maps : inferTy Γst (var 2) ≡ just (arr (arr ⋆ ⟦ D0 ⟧ ⟦ D1 ⟧) (var 0) (var 1))
maps = refl

-- Rejections.
open-Γ bad-Γ : Ctx
open-Γ = ε ▸ arr ⋆ (var 0) (var 0)                 -- mentions var 0 of Θ
bad-Γ  = ε ▸ ⋆ ▸ arr ⋆ (b 0) (b 1)                 -- b 1 is not declared yet

rejected : ( is-just (infer (ε ▸ ⋆) ⟦ open-Γ ⟧)
           ∷ is-just (infer ε ⟦ bad-Γ ⟧)
           ∷ is-just (infer ε (bnd free 1 D1 ⟨⟩))
           ∷ is-just (infer (ε ▸ ⋆) (bnd free 0 D1 (⟨⟩ ,ₛ var 0)))
           ∷ [])
         ≡ (false ∷ false ∷ false ∷ false ∷ [])
rejected = refl

------------------------------------------------------------------------
-- Conservativity over plain CaTT (no constants).

open import CaTTExp.Binder.Embed using (module CaTT)
open CaTT P.∅ (freeBinders P.K) using (tm-iff; ctx-iff; ty-iff; sub-iff) public
