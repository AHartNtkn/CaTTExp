------------------------------------------------------------------------
-- Examples for CaTTExp.Binder.UniHeads: the universal filler over the
-- arrow x → y, for n = 0 and n = 1, with the horns of CaTTExp.Lim.Horn
-- (the only horns built in Agda so far; ledger S27 (e)) and the
-- specified cone of CaTTExp.Cones. Checked by the certified checker
-- with plain CaTT's side condition and rule (MARK). Every statement is
-- `refl`.
--
-- n = 0: arity x, y, f, c, p_x, p_y, p_f (a cone over the arrow with
--        apex c); uni^w : c → lim, and the comparison components
--        m_x, m_y, m_f of the cone morphism to the universal cone.
-- n = 1: arity x, y, f, c, u⁻, u⁺, m_x, m_y, m_f (two maps into the
--        limit and a cone-morphism between their images), with m_f
--        marked inv (CaTT's setting, Lim/Horn's marksP₁); uni^w is the
--        2-cell u⁻ ⇒ u⁺. Arguments whose m_f entry is not inv are
--        rejected.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Cones using (ExTy; ExCtx; v; ob; hom; evCtx; module ConeOf)
import CaTTExp.Lim.Horn as Horn
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.LimHeads
open import CaTTExp.Binder.UniHeads
import CaTTExp.Binder.HeadSpec as HS

module CaTTExp.Binder.UniHeadsExamples where

toExTy : P.Ty → Maybe ExTy
toExTy P.⋆ = just ob
toExTy (P.arr A (P.var i) (P.var j)) = toExTy A >>= λ E → just (hom E (v i) (v j))
toExTy _ = nothing

toExCtx : P.Ctx → Maybe ExCtx
toExCtx P.ε       = just []
toExCtx (Γ P.▸ A) = toExCtx Γ >>= λ E → toExTy A >>= λ X → just (E ++ (X ∷ []))

coneShape : P.Ctx → Maybe P.Ctx
coneShape Γ = toExCtx Γ >>= λ E → just (evCtx (ConeOf.cone E))

Arr : P.Ctx
Arr = P.ε P.▸ P.⋆ P.▸ P.⋆ P.▸ P.arr P.⋆ (P.var 0) (P.var 1)

-- The horns of Lim/Horn: J2₀ (cone, 4 horn entries, w, 3 components)
-- and J2₁ (cone, 6 horn entries, w, 3 components; m_f at level 12 is
-- marked).
hornShape : P.Ctx → Nat → Maybe UShape
hornShape Γ zero          = if Γ P.==Ctx Arr then just (ush Horn.J2₀ 4 []) else nothing
hornShape Γ (suc zero)    = if Γ P.==Ctx Arr then just (ush Horn.J2₁ 6 Horn.marksP₁) else nothing
hornShape Γ (suc (suc _)) = nothing

-- The shapes are Lim/Horn's: its cone prefix is the cone shape.
pre-is-cone : coneShape Arr ≡ just Horn.Pre
pre-is-cone = refl

open HS.Laws P.∅ (uniSpec P.K coneShape hornShape)

open Signature 𝕊
open import CaTTExp.Binder.Typing 𝕊
open import CaTTExp.Binder.CheckWith 𝕊 cattSide varMark

inferTy : Ctx → Tm → Maybe Ty
inferTy Γ t = infer Γ t >>= λ r → just (fst r)

wellTyped : Ctx → Tm → Bool
wellTyped Γ t with ctx? Γ | inferTy Γ t
... | just w | just A = is-just (checkTy (sizeTy A) Γ w A)
... | _      | _      = false

-- lim over the arrow, and its legs, at the identity of the first three
-- variables.
L : Tm
L = bnd (base (limF Arr)) 0 ε (fresh 0 3)

λx λy : Tm
λx = bnd (base (legF Arr)) 0 ε (fresh 0 3)
λy = bnd (base (legF Arr)) 1 ε (fresh 0 3)

------------------------------------------------------------------------
-- n = 0.

H₀ : Ctx
H₀ = hctx (uniF Arr 0) 0
  where open HS.HeadSpec (uniSpec P.K coneShape hornShape)

uni₀ : Nat → Tm
uni₀ y = bnd (uniF Arr 0) y ε (fresh 0 7)

-- The arity is a well-formed context: x, y, f, c, then the cone
-- p_x : c → x, p_y : c → y, p_f over f.
H₀-ok : is-just (ctx? H₀) ≡ true
H₀-ok = refl

H₀-c : lookup H₀ 4 ≡ just (arr ⋆ (var 3) (var 0))
H₀-c = refl

-- uni^w : c → lim.
uni₀-ty : inferTy H₀ (uni₀ 0) ≡ just (arr ⋆ (var 3) L)
uni₀-ty = refl

-- The comparison components are well typed.
uni₀-y-wf : (wellTyped H₀ (uni₀ 1) ∧ wellTyped H₀ (uni₀ 2) ∧ wellTyped H₀ (uni₀ 3)) ≡ true
uni₀-y-wf = refl

no-uni₀-4 : inferTy H₀ (uni₀ 4) ≡ nothing
no-uni₀-4 = refl

------------------------------------------------------------------------
-- n = 1.

H₁ : Ctx
H₁ = hctx (uniF Arr 1) 0
  where open HS.HeadSpec (uniSpec P.K coneShape hornShape)

uni₁ : Nat → Tm
uni₁ y = bnd (uniF Arr 1) y ε (fresh 0 9)

H₁-ok : is-just (ctx? H₁) ≡ true
H₁-ok = refl

-- m_f (the last horn entry) is marked inv; the others are not.
H₁-marks : (marksAt H₁ 8 ∷ marksAt H₁ 7 ∷ []) ≡ ((minv ∷ []) ∷ [] ∷ [])
H₁-marks = refl

-- uni^w : u⁻ ⇒ u⁺, both c → lim.
uni₁-ty : inferTy H₁ (uni₁ 0) ≡ just (arr (arr ⋆ (var 3) L) (var 4) (var 5))
uni₁-ty = refl

uni₁-y-wf : (wellTyped H₁ (uni₁ 1) ∧ wellTyped H₁ (uni₁ 2) ∧ wellTyped H₁ (uni₁ 3)) ≡ true
uni₁-y-wf = refl

-- The same arguments in the arity with m_f's inv mark dropped: the mark
-- premise fails, so the filler is rejected.
unmark : Ctx → Ctx
unmark ε = ε
unmark (Γ ▸[ _ ] A) = unmark Γ ▸ A

H₁-unmarked-ok : is-just (ctx? (unmark H₁)) ≡ true
H₁-unmarked-ok = refl

no-uni₁-unmarked : inferTy (unmark H₁) (uni₁ 0) ≡ nothing
no-uni₁-unmarked = refl

-- Rejections: no horn for n = 2 here, and no horn over another base.
no-uni₂ : inferTy H₁ (bnd (uniF Arr 2) 0 ε (fresh 0 9)) ≡ nothing
no-uni₂ = refl

no-uni-pt : inferTy (ε ▸ ⋆) (bnd (uniF (P.ε P.▸ P.⋆) 0) 0 ε (fresh 0 1)) ≡ nothing
no-uni-pt = refl

------------------------------------------------------------------------
-- A use: the filler for the universal cone itself, in the context of a
-- diagram A → B. Its horn data is (A, B, F; L, λ_x, λ_y, λ_f), and
-- uni^w is then an endomorphism of L.

Θ : Ctx
Θ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1)

LΘ : Tm
LΘ = bnd (base (limF Arr)) 0 ε (fresh 0 3)

legΘ : Nat → Tm
legΘ g = bnd (base (legF Arr)) g ε (fresh 0 3)

uni-self : inferTy Θ (bnd (uniF Arr 0) 0 ε (fresh 0 3 ,ₛ LΘ ,ₛ legΘ 0 ,ₛ legΘ 1 ,ₛ legΘ 2))
           ≡ just (arr ⋆ LΘ LΘ)
uni-self = refl

------------------------------------------------------------------------
-- Presupposition (CaTTExp.Binder.UniPresup) applied to the checker's
-- derivation of the n = 1 filler: its type is well formed.

open import CaTTExp.Binder.VarMark 𝕊 cattSide using (markRen; markSub; markVar)
open import CaTTExp.Binder.UniPresup coneShape hornShape varMark markRen markSub markVar using (uni-tm-ty)

uni₁-presup : H₁ ⊢ty arr (arr ⋆ (var 3) L) (var 4) (var 5)
uni₁-presup = uni-tm-ty (snd (from-just (infer H₁ (uni₁ 0))))
