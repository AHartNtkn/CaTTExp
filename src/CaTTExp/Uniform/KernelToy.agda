------------------------------------------------------------------------
-- A toy instance of CaTTExp.Uniform.Kernel: its hypotheses are
-- satisfiable, and the checker built from them accepts a coherence.
--
-- The layer has one cell, no letters, and the support "true", which is
-- full. Every term is interpreted as that cell. So the side condition
-- holds everywhere: this is not a model of V + S, only a check that
-- Kernel's parameters (Layer, Graded, ⟦_⟧) can be supplied and that
-- the resulting checker runs. The checker accepts the identity-shaped
-- coherence coh_{(x : ⋆), x → x}[x] in the context (x : ⋆).
------------------------------------------------------------------------
module CaTTExp.Uniform.KernelToy where

open import CaTTExp.Prelude
open import CaTTExp.Join.Finite using (z≤n; _≤_)
open import CaTTExp.Pure using (∅)
open import CaTTExp.Signature
open import CaTTExp.Uniform.Rule
import CaTTExp.Uniform.Kernel
open import CaTTExp.Join.Quiver using (yes)

open Signature ∅ using (Ctx; Ty; Tm; ε; _▸_; ⋆; arr; var; coh; ⟨⟩; _,ₛ_)

toy : Layer
toy = record
  { Cell   = ⊤
  ; _≟_    = λ { tt tt → yes refl }
  ; Letter = ⊥
  ; out    = λ _ → []
  ; tgt    = λ ()
  ; Supp   = Bool
  ; supp   = λ _ → true
  ; suppL  = λ ()
  ; _∪_    = _∧_
  ; full   = λ b → b
  }

toyGraded : Graded toy
toyGraded = record { bound = λ _ _ → 0 ; graded = g }
  where
  g : ∀ {x z} (p : Path toy x z) → _≤_ (lenP toy p) 0
  g ε = z≤n
  g (() ◅[ _ ] _)

module K = CaTTExp.Uniform.Kernel ∅ (λ _ _ → toy) (λ _ _ → toyGraded) (λ _ _ _ → just tt)

point : Ctx
point = ε ▸ ⋆

-- coh_{(x : ⋆), x → x}[x], in the context (x : ⋆).
idx : Tm
idx = coh point (arr ⋆ (var 0) (var 0)) (⟨⟩ ,ₛ var 0)

side-holds : K.side point ⋆ (var 0) (var 0) ≡ true
side-holds = refl

accepted : T (is-just (K.Checker.checkCtx point >>= λ w → K.Checker.inferTm point w idx))
accepted = tt
