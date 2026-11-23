------------------------------------------------------------------------
-- Elab.assoc and assoc⁻ are correct (ledger S20 (ii)): for every
-- typed chain f, g, h (the images of a typed σ₀ : ctxOf Comp₃T), the
-- associator is defined and well typed. No check per use.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.ElabCorrect.Assoc where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab using (assoc; assoc⁻; assocB; Comp₃T)
open import CaTTExp.GrayCtx.ElabCorrect.Coh
open import CaTTExp.GrayCtx.ElabCorrect.Shape

assoc-shape : ∀ inv → ShapeOK Comp₃T (assocB inv)
assoc-shape false = cert (shape? Comp₃T (assocB false)) tt
assoc-shape true  = cert (shape? Comp₃T (assocB true)) tt

private
  P₃ = ctxOf Comp₃T
  cellOf : Bool → Sub → Tm
  cellOf inv σ₀ = let sh = assoc-shape inv in coh P₃ (arr (ty sh) (src sh) (tgt sh)) σ₀
  tyOfC : Bool → Sub → Ty
  tyOfC inv σ₀ = let sh = assoc-shape inv in arr (ty sh) (src sh) (tgt sh) [ σ₀ ]ty

-- f, g, h = σ₀(2), σ₀(4), σ₀(6): the three arrows of the chain.
assoc-ok : ∀ {Γ σ₀} → Γ ⊢sub σ₀ ∶ P₃ →
           (assoc Γ (lookupₛ σ₀ 2) (lookupₛ σ₀ 4) (lookupₛ σ₀ 6) ≡ just (cellOf false σ₀))
           × (Γ ⊢tm cellOf false σ₀ ∶ tyOfC false σ₀)
assoc-ok s = cohT-ok Comp₃T (assocB false) (assoc-shape false) s

assoc⁻-ok : ∀ {Γ σ₀} → Γ ⊢sub σ₀ ∶ P₃ →
            (assoc⁻ Γ (lookupₛ σ₀ 2) (lookupₛ σ₀ 4) (lookupₛ σ₀ 6) ≡ just (cellOf true σ₀))
            × (Γ ⊢tm cellOf true σ₀ ∶ tyOfC true σ₀)
assoc⁻-ok s = cohT-ok Comp₃T (assocB true) (assoc-shape true) s
