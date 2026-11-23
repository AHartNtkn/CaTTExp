------------------------------------------------------------------------
-- Examples for the Gray object formers (CaTTExp.Binder.GrayForm),
-- checked by the certified checker with plain CaTT's side condition
-- and the mark judgment of rule (MARK) (CaTTExp.Binder.Typing). Every
-- statement is `refl`.
--
--  * In (A B C : ⋆): A ⊗ B, A\C, C/A and nested formulas such as
--    (A ⊗ B)\C and A\(C/B) are objects, and their types are well formed.
--  * A 1-cell f : A ⊗ B → C (an ambient map out of the tensor) and a
--    2-cell between two such maps are typed.
--  * Rejections: a 1-cell argument (not an object); a non-zero
--    selector; a non-empty telescope; one or three arguments.
--  * The image of a biclosed formula (CaTTExp.Binder.GrayFormEmbed)
--    is checked.
--  * Conservativity: plain CaTT with these formers is conservative
--    over plain CaTT (CaTTExp.Binder.Embed, instantiated).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.GrayForm
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (extend)
import CaTTExp.Binder.Embed as Embed
import CaTTExp.Gray.Biclosed.Syntax as GB

module CaTTExp.Binder.GrayFormExamples where

𝕊 : Signature
𝕊 = extend P.∅ (grayFormBinders P.K)

open Signature 𝕊
open GrayFormConstruction K GBF (λ b → b)
open import CaTTExp.Binder.Typing 𝕊
open import CaTTExp.Binder.CheckWith 𝕊 cattSide varMark
open import CaTTExp.Binder.GrayFormEmbed P.∅ using (fmTm)

inferTy : Ctx → Tm → Maybe Ty
inferTy Γ t = infer Γ t >>= λ r → just (fst r)

wellTyped : Ctx → Tm → Bool
wellTyped Γ t with ctx? Γ | inferTy Γ t
... | just w | just A = is-just (checkTy (sizeTy A) Γ w A)
... | _      | _      = false

v : Nat → Tm
v = var

-- Three objects A, B, C.
Γ₃ : Ctx
Γ₃ = ε ▸ ⋆ ▸ ⋆ ▸ ⋆

a b c : Tm
a = v 0
b = v 1
c = v 2

objects : ( inferTy Γ₃ (a ⊗ᵗ b) ∷ inferTy Γ₃ (a \\ᵗ c) ∷ inferTy Γ₃ (c //ᵗ a)
          ∷ inferTy Γ₃ ((a ⊗ᵗ b) \\ᵗ c) ∷ inferTy Γ₃ (a \\ᵗ (c //ᵗ b))
          ∷ inferTy Γ₃ ((a ⊗ᵗ b) ⊗ᵗ (c ⊗ᵗ a)) ∷ [])
        ≡ (just ⋆ ∷ just ⋆ ∷ just ⋆ ∷ just ⋆ ∷ just ⋆ ∷ just ⋆ ∷ [])
objects = refl

objects-wf : ( wellTyped Γ₃ (a ⊗ᵗ b) ∷ wellTyped Γ₃ ((a ⊗ᵗ b) \\ᵗ c)
             ∷ wellTyped Γ₃ (a \\ᵗ (c //ᵗ b)) ∷ [])
           ≡ (true ∷ true ∷ true ∷ [])
objects-wf = refl

-- a map f : a ⊗ b → c and a 2-cell α : f ⇒ g.
Γmap : Ctx
Γmap = Γ₃ ▸ arr ⋆ (a ⊗ᵗ b) c ▸ arr ⋆ (a ⊗ᵗ b) c
          ▸ arr (arr ⋆ (a ⊗ᵗ b) c) (v 3) (v 4)

maps : ( inferTy Γmap (v 3) ∷ inferTy Γmap (v 5) ∷ [])
     ≡ ( just (arr ⋆ (a ⊗ᵗ b) c) ∷ just (arr (arr ⋆ (a ⊗ᵗ b) c) (v 3) (v 4)) ∷ [])
maps = refl

maps-ctx : is-just (ctx? Γmap) ≡ true
maps-ctx = refl

-- Rejections.
Γf : Ctx
Γf = Γ₃ ▸ arr ⋆ a b

rejected : ( is-just (infer Γf (a ⊗ᵗ v 3))                              -- a 1-cell argument
           ∷ is-just (infer Γ₃ (bnd tensor 1 ε (⟨⟩ ,ₛ a ,ₛ b)))         -- selector 1
           ∷ is-just (infer Γ₃ (bnd tensor 0 (ε ▸ ⋆) (⟨⟩ ,ₛ a ,ₛ b)))   -- a telescope
           ∷ is-just (infer Γ₃ (bnd lhom 0 ε (⟨⟩ ,ₛ a)))                -- one argument
           ∷ is-just (infer Γ₃ (bnd rhom 0 ε (⟨⟩ ,ₛ a ,ₛ b ,ₛ c)))       -- three arguments
           ∷ [])
         ≡ (false ∷ false ∷ false ∷ false ∷ false ∷ [])
rejected = refl

-- a biclosed formula, (obj 0 ⊗ obj 1) \\ obj 2, and one with a
-- representable (no image).
fm₁ : GB.Fm
fm₁ = (GB.obj 0 GB.⊗ GB.obj 1) GB.\\ GB.obj 2

fm-image : fmTm var fm₁ ≡ just ((a ⊗ᵗ b) \\ᵗ c)
fm-image = refl

fm-image-ty : (fmTm var fm₁ >>= inferTy Γ₃) ≡ just ⋆
fm-image-ty = refl

fm-rep : fmTm var (GB.obj 0 GB.⊗ GB.rep (GB.disk 1)) ≡ nothing
fm-rep = refl

------------------------------------------------------------------------
-- Conservativity over plain CaTT (no constants): a binder-free
-- judgment holds with the Gray formers iff it holds without them.

open Embed.CaTT P.∅ (grayFormBinders P.K) using (tm-iff; ctx-iff; ty-iff; sub-iff) public
