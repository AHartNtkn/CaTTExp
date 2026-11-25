------------------------------------------------------------------------
-- Glue for the descent (ledger S20 (i), stage 4b; notes/rc-generator.md
-- §1, stage 4 plan), each typed by proof.
--
-- The strips of tools/rc_descent.py use generic coherences over small
-- pasting contexts (`_gcoh`: reassociation, unit, interchange along a
-- cut).  Here such a cell needs no shape-by-shape typing proof: its two
-- ends are typed terms of a pasting context P, which is globular, so
-- the formalized procedure rcP answers it there with a derivation, and
-- the answer is pulled back along a typed substitution into Γ.
--
--   glueCell : P ⊢tm a ∶ B → P ⊢tm b ∶ B → Γ ⊢sub σ ∶ P →
--              Maybe (Ans Γ (B[σ]) (a[σ]) (b[σ]))
--   whiskRA  : an answer s → t whiskered on the right by h along cut k,
--              an answer (s ▹ₖ h) → (t ▹ₖ h)            (rwT-ty)
--   whiskLA  : the same on the left, (h ◃ₖ s) → (h ◃ₖ t)  (lwT-ty)
--
-- A `nothing` from glueCell only makes the descent return `nothing`;
-- every `just` is typed.  (Totality for the fixed shapes the strips use
-- is rcP-glob: equal normal forms.)
------------------------------------------------------------------------
module CaTTExp.RCProc.DescentGlue where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (nB; wK; lK)
open import CaTTExp.DerivedBoundary using (rwT; rwT-wf; rwT-ty; tyK; tgtK; σR;
  lwT; lwT-wf; lwT-ty; hL; σL)
open import CaTTExp.RCProc using (rcP)
open import CaTTExp.RCProc.Glue using (Ans; pullA; transA)

glueCell : ∀ {Γ P B a b σ} → P ⊢tm a ∶ B → P ⊢tm b ∶ B → Γ ⊢sub σ ∶ P →
           Maybe (Ans Γ (B [ σ ]ty) (a [ σ ]tm) (b [ σ ]tm))
glueCell da db dσ = rcP da db >>= λ w → just (pullA dσ w)

whiskRA : ∀ k j {Γ C′ s t z h} → dim C′ ≡ nB k j →
          Γ ⊢tm h ∶ arr (tyK k (arr C′ s t)) (tgtK k (arr C′ s t)) z →
          Ans Γ C′ s t →
          Ans Γ (wK k j [ σR s C′ z h ]ty) (rwT k j s C′ z h) (rwT k j t C′ z h)
whiskRA k j {Γ} {C′} {s} {t} {z} {h} e dh (c , dc) =
  rwT k (suc j) c (arr C′ s t) z h ,
  subst (Γ ⊢tm rwT k (suc j) c (arr C′ s t) z h ∶_) (rwT-ty k j c C′ s t z h e)
    (rwT-wf k (suc j) dc (cong suc e) dh)

whiskLA : ∀ k j {Γ C′ s t x h} → dim C′ ≡ nB k j →
          Γ ⊢tm h ∶ hL k x (arr C′ s t) →
          Ans Γ C′ s t →
          Ans Γ (lK k j [ σL k j h x s C′ ]ty) (lwT k j h x s C′) (lwT k j h x t C′)
whiskLA k j {Γ} {C′} {s} {t} {x} {h} e dh (c , dc) =
  lwT k (suc j) h x c (arr C′ s t) ,
  subst (Γ ⊢tm lwT k (suc j) h x c (arr C′ s t) ∶_) (lwT-ty k j h x c C′ s t e)
    (lwT-wf k (suc j) dc (cong suc e) dh)
