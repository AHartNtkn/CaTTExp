------------------------------------------------------------------------
-- Examples for CaTTExp.Binder.LimHeads, checked by the certified
-- checker with plain CaTT's side condition (CaTTExp.Binder.Typing):
-- the limit of an arrow F : A → B and its universal cone, with the
-- specified cone of CaTTExp.Cones as the shape. Every statement is
-- `refl`.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Cones using (Ex; ExTy; ExCtx; v; ob; hom; evCtx; module ConeOf)
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.LimHeads
import CaTTExp.Binder.HeadSpec as HS

module CaTTExp.Binder.LimHeadsExamples where

-- Globular pure contexts as expression contexts.
toExTy : P.Ty → Maybe ExTy
toExTy P.⋆ = just ob
toExTy (P.arr A (P.var i) (P.var j)) = toExTy A >>= λ E → just (hom E (v i) (v j))
toExTy _ = nothing

toExCtx : P.Ctx → Maybe ExCtx
toExCtx P.ε       = just []
toExCtx (Γ P.▸ A) = toExCtx Γ >>= λ E → toExTy A >>= λ X → just (E ++ (X ∷ []))

-- The specified cone (Mikhail, Thm 3.3) over a globular base.
coneShape : P.Ctx → Maybe P.Ctx
coneShape Γ = toExCtx Γ >>= λ E → just (evCtx (ConeOf.cone E))

open HS.Laws P.∅ (limSpec P.K coneShape)

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

L : Tm
L = bnd (limF Arr) 0 ε γ

leg : Nat → Tm
leg g = bnd (legF Arr) g ε γ

-- x0 y1 f2 z3 g4 ↦ f ; g
compPC : Ctx
compPC = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ ⋆ ▸ arr ⋆ (var 1) (var 3)

comp : Tm → Tm → Tm → Tm → Tm → Tm
comp x y f z g = coh compPC (arr ⋆ (var 0) (var 3)) (⟨⟩ ,ₛ x ,ₛ y ,ₛ f ,ₛ z ,ₛ g)

-- lim_{x→y}[A, B, F] : ⋆.
lim-ty : inferTy Θ L ≡ just ⋆
lim-ty = refl

-- λ_x : L → A, λ_y : L → B.
legx-ty : inferTy Θ (leg 0) ≡ just (arr ⋆ L (var 0))
legx-ty = refl

legy-ty : inferTy Θ (leg 1) ≡ just (arr ⋆ L (var 1))
legy-ty = refl

-- λ_f : λ_y ⇒ λ_x ; F  (the lax cone cell over f).
legf-ty : inferTy Θ (leg 2) ≡ just (arr (arr ⋆ L (var 1)) (leg 1) (comp L (var 0) (leg 0) (var 1) (var 2)))
legf-ty = refl

-- The inferred types are well formed.
legf-wf : wellTyped Θ (leg 2) ≡ true
legf-wf = refl

-- Rejections: there is no fourth cell; lim takes selector 0 only; the
-- wrong number of arguments; a base that is not a well-formed context
-- (f : x → z with z out of scope).
no-leg3 : inferTy Θ (leg 3) ≡ nothing
no-leg3 = refl

no-sel : inferTy Θ (bnd (limF Arr) 1 ε γ) ≡ nothing
no-sel = refl

no-args : inferTy Θ (bnd (limF Arr) 0 ε (⟨⟩ ,ₛ var 0 ,ₛ var 1)) ≡ nothing
no-args = refl

Bad : P.Ctx
Bad = P.ε P.▸ P.⋆ P.▸ P.arr P.⋆ (P.var 0) (P.var 5)

no-bad : inferTy (ε ▸ ⋆ ▸ arr ⋆ (var 0) (var 0)) (bnd (limF Bad) 0 ε (⟨⟩ ,ₛ var 0 ,ₛ var 1)) ≡ nothing
no-bad = refl

-- The point: lim over the empty base is a typed object, a head with
-- empty arity, i.e. a constant. That it is terminal (spec §6.5) is
-- uni's universal property, not encoded here (ledger S27 (e)).
top-ty : inferTy ε (bnd (limF P.ε) 0 ε ⟨⟩) ≡ just ⋆
top-ty = refl

-- Two points: the product A × B with its projections (spec §6.5).
Two : P.Ctx
Two = P.ε P.▸ P.⋆ P.▸ P.⋆

Prod : Tm
Prod = bnd (limF Two) 0 ε (⟨⟩ ,ₛ var 0 ,ₛ var 1)

π₁-ty : inferTy (ε ▸ ⋆ ▸ ⋆) (bnd (legF Two) 0 ε (⟨⟩ ,ₛ var 0 ,ₛ var 1)) ≡ just (arr ⋆ Prod (var 0))
π₁-ty = refl

π₂-ty : inferTy (ε ▸ ⋆ ▸ ⋆) (bnd (legF Two) 1 ε (⟨⟩ ,ₛ var 0 ,ₛ var 1)) ≡ just (arr ⋆ Prod (var 1))
π₂-ty = refl
