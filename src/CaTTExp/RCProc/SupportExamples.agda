------------------------------------------------------------------------
-- A check of support restriction (CaTTExp.RCProc.Support): the
-- interchange query of GlobularFillerExamples, asked in a context that
-- is not globular because of an extra cell γ : f ∗₀ g ⇒ f ∗₀ g whose
-- type has composite ends. rcP on the whole context has no case for
-- it; rcS restricts to the support (which omits γ, so is globular) and
-- answers. Both facts are checked by evaluation.
------------------------------------------------------------------------
module CaTTExp.RCProc.SupportExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.RCProc
open import CaTTExp.GraphFillerExamples using (v; comp)
open import CaTTExp.GlobularFillerExamples using (I; αβ; βα; homI)

-- γ : f ∗₀ g ⇒ f ∗₀ g (levels: x0 y1 f2 z5 g6).
Γ : Ctx
Γ = I ▸ arr (arr ⋆ (v 0) (v 5)) (comp (v 0) (v 1) (v 2) (v 5) (v 6)) (comp (v 0) (v 1) (v 2) (v 5) (v 6))

dαβ : Γ ⊢tm αβ ∶ homI
dαβ = subst (Γ ⊢tm αβ ∶_) refl (snd (from-just (infer Γ αβ)))

dβα : Γ ⊢tm βα ∶ homI
dβα = subst (Γ ⊢tm βα ∶_) refl (snd (from-just (infer Γ βα)))

-- The whole context is not globular, and the query is 2-dimensional,
-- so stage 1 alone returns nothing ...
_ : is-just (rcP dαβ dβα) ≡ false
_ = refl

-- ... while restricting to the support answers it.
_ : is-just (rcS dαβ dβα) ≡ true
_ = refl

-- The support context is I itself (γ dropped).
_ : Sup.Γ′ dαβ dβα ≡ I
_ = refl
