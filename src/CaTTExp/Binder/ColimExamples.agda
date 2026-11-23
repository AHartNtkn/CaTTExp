------------------------------------------------------------------------
-- Examples for CaTTExp.Binder.Colim, checked by the certified checker
-- with plain CaTT's side condition: the colimit of an arrow and its
-- universal cocone (the cocone cell reverses the leg), the coproduct
-- as the colimit over two points (typing only, without couni), limits beside colimits in the same
-- signature, and rejections. Every statement is `refl`.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.LimHeads
open import CaTTExp.Binder.Colim
import CaTTExp.Binder.HeadSpec as HS


module CaTTExp.Binder.ColimExamples where

open HS.Laws P.∅ (limColimSpec P.K)

open Signature 𝕊
open import CaTTExp.Binder.Typing 𝕊
open import CaTTExp.Binder.CheckWith 𝕊 cattSide varMark

inferTy : Ctx → Tm → Maybe Ty
inferTy Γ t = infer Γ t >>= λ r → just (fst r)

wellTyped : Ctx → Tm → Bool
wellTyped Γ t with ctx? Γ | inferTy Γ t
... | just w | just A = is-just (checkTy (sizeTy A) Γ w A)
... | _      | _      = false

-- The arrow x → y as a diagram base.
Arr : P.Ctx
Arr = P.ε P.▸ P.⋆ P.▸ P.⋆ P.▸ P.arr P.⋆ (P.var 0) (P.var 1)

-- A diagram: A, B : ⋆, F : A → B.
Θ : Ctx
Θ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1)

γ : Sub
γ = ⟨⟩ ,ₛ var 0 ,ₛ var 1 ,ₛ var 2

C : Tm
C = bnd (colimH (limF Arr)) 0 ε γ

q : Nat → Tm
q g = bnd (colimH (legF Arr)) g ε γ

-- x0 y1 f2 z3 g4 ↦ f ; g
compPC : Ctx
compPC = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ ⋆ ▸ arr ⋆ (var 1) (var 3)

comp : Tm → Tm → Tm → Tm → Tm → Tm
comp x y f z g = coh compPC (arr ⋆ (var 0) (var 3)) (⟨⟩ ,ₛ x ,ₛ y ,ₛ f ,ₛ z ,ₛ g)

-- colim_{x→y}[A, B, F] : ⋆.
colim-ty : inferTy Θ C ≡ just ⋆
colim-ty = refl

-- q_x : A → C, q_y : B → C.
qx-ty : inferTy Θ (q 0) ≡ just (arr ⋆ (var 0) C)
qx-ty = refl

qy-ty : inferTy Θ (q 1) ≡ just (arr ⋆ (var 1) C)
qy-ty = refl

-- q_f : q_x ⇒ F ; q_y  (the cocone cell reverses the leg, spec §6.3).
qf-ty : inferTy Θ (q 2) ≡ just (arr (arr ⋆ (var 0) C) (q 0) (comp (var 0) (var 1) (var 2) C (q 1)))
qf-ty = refl

qf-wf : wellTyped Θ (q 2) ≡ true
qf-wf = refl

-- The limit heads are still there, in the same signature.
L : Tm
L = bnd (limH (limF Arr)) 0 ε γ

legx-ty : inferTy Θ (bnd (limH (legF Arr)) 0 ε γ) ≡ just (arr ⋆ L (var 0))
legx-ty = refl

-- Two points: the coproduct A + B with its coprojections (typing
-- only: that it is universal needs couni, which is not encoded).
Two : P.Ctx
Two = P.ε P.▸ P.⋆ P.▸ P.⋆

Sum : Tm
Sum = bnd (colimH (limF Two)) 0 ε (⟨⟩ ,ₛ var 0 ,ₛ var 1)

ι₁-ty : inferTy (ε ▸ ⋆ ▸ ⋆) (bnd (colimH (legF Two)) 0 ε (⟨⟩ ,ₛ var 0 ,ₛ var 1)) ≡ just (arr ⋆ (var 0) Sum)
ι₁-ty = refl

ι₂-ty : inferTy (ε ▸ ⋆ ▸ ⋆) (bnd (colimH (legF Two)) 1 ε (⟨⟩ ,ₛ var 0 ,ₛ var 1)) ≡ just (arr ⋆ (var 1) Sum)
ι₂-ty = refl

-- The initial object: the colimit over the empty base (typing only,
-- as above).
bot-ty : inferTy ε (bnd (colimH (limF P.ε)) 0 ε ⟨⟩) ≡ just ⋆
bot-ty = refl

-- Rejections: no fourth cocone cell; selector 0 only; the wrong
-- number of arguments.
no-q3 : inferTy Θ (q 3) ≡ nothing
no-q3 = refl

no-sel : inferTy Θ (bnd (colimH (limF Arr)) 1 ε γ) ≡ nothing
no-sel = refl

no-args : inferTy Θ (bnd (colimH (limF Arr)) 0 ε (⟨⟩ ,ₛ var 0 ,ₛ var 1)) ≡ nothing
no-args = refl

------------------------------------------------------------------------
-- Conservativity over plain CaTT (no constants).

open import CaTTExp.Binder.Embed using (module CaTT)
open CaTT P.∅ (HS.specBinders (limColimSpec P.K)) using (tm-iff; ctx-iff; ty-iff; sub-iff) public
