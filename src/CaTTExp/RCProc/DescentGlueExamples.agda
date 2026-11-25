------------------------------------------------------------------------
-- A check of RCProc.DescentGlue by evaluation: the interchange cell
-- αβ ⇛ βα of GlobularFillerExamples as a glue cell over its pasting
-- context I, pulled back along the identity substitution of I (built
-- from typed entries by RCProc.TypedSub.buildSub), is answered.  The
-- test inputs' derivations come from the checker; the glue does not.
------------------------------------------------------------------------
module CaTTExp.RCProc.DescentGlueExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.DescentGlue
open import CaTTExp.GlobularFillerExamples using (I; αβ; βα; homI)

private
  dαβ : I ⊢tm αβ ∶ homI
  dαβ = snd (from-just (infer I αβ))

  dβα : I ⊢tm βα ∶ homI
  dβα = snd (from-just (infer I βα))

  ent : Nat → Maybe (TTm I)
  ent n = infer I (var n) >>= λ r → just tt[ var n ∶ fst r , snd r ]

  vars : Nat → Maybe (List (TTm I))
  vars zero    = just []
  vars (suc n) = vars n >>= λ es → ent n >>= λ e → just (es ++ (e ∷ []))

  wI : I ⊢ctx
  wI = tm-ctx′ dαβ
    where
    tm-ctx′ : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ctx
    tm-ctx′ (var-wf w _) = w
    tm-ctx′ (coh-wf _ _ _ _ s) = sub-ctx s
      where
      sub-ctx : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → Γ ⊢ctx
      sub-ctx (⟨⟩-wf w) = w
      sub-ctx (,-wf s _) = sub-ctx s
    tm-ctx′ (cst-wf w _) = w

  idI : TSub I I
  idI = from-just (vars (len I) >>= buildSub wI I)

_ : is-just (vars (len I) >>= buildSub wI I) ≡ true
_ = refl

_ : is-just (glueCell dαβ dβα (snd idI)) ≡ true
_ = refl
