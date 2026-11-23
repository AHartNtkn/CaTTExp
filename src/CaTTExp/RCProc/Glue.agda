------------------------------------------------------------------------
-- Glue for building relative-coherence answers from smaller ones
-- (ledger S20 (i), stage 3; notes/rc-generator.md §1), each typed by
-- proof:
--
--   transA : Ans Γ A t s → Ans Γ A s u → Ans Γ A t u
--            (vertical composite of the two cells, Derived's composite)
--   pullA  : Δ ⊢sub θ ∶ P → Ans P B t′ u′ → Ans Δ (B[θ]) (t′[θ]) (u′[θ])
--            (an answer over a context P pulled back along θ)
------------------------------------------------------------------------
module CaTTExp.RCProc.Glue where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed; tm[])
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.Derived using (sphSub; aL-sph)
open import CaTTExp.DerivedBoundary using (rwT; rwT-wf; rwT-ty0; tyK; tgtK; srcK; σR)

Ans : Ctx → Ty → Tm → Tm → Set
Ans Γ A t u = Σ Tm λ w → Γ ⊢tm w ∶ arr A t u

private
  arr-inj : ∀ {A A′ s s′ t t′} → arr A s t ≡ arr A′ s′ t′ → (A ≡ A′) × (s ≡ s′) × (t ≡ t′)
  arr-inj refl = refl , refl , refl

-- The boundary of a cell type C = arr A t s, read through its sphere.
module _ (A : Ty) (t s : Tm) where
  private
    e = arr-inj (aL-sph (arr A t s))

  tyK-arr : tyK (dim A) (arr A t s) ≡ A
  tyK-arr = fst e

  srcK-arr : srcK (dim A) (arr A t s) ≡ t
  srcK-arr = fst (snd e)

  tgtK-arr : tgtK (dim A) (arr A t s) ≡ s
  tgtK-arr = snd (snd e)

-- Vertical composite of two answers.
transA : ∀ {Γ A t s u} → Ans Γ A t s → Ans Γ A s u → Ans Γ A t u
transA {Γ} {A} {t} {s} {u} (c , dc) (h , dh) =
  rwT k 0 c C u h ,
  subst (Γ ⊢tm rwT k 0 c C u h ∶_)
    (trans (rwT-ty0 k c C u h refl)
           (cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) (tyK-arr A t s) (cong₂ _,_ (srcK-arr A t s) refl)))
    (rwT-wf k 0 dc refl
      (subst (Γ ⊢tm h ∶_)
        (sym (cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) (tyK-arr A t s) (cong₂ _,_ (tgtK-arr A t s) refl)))
        dh))
  where
  k = dim A
  C = arr A t s

-- Pull an answer over P back along a typed substitution.
pullA : ∀ {Δ P θ B t u} → Δ ⊢sub θ ∶ P → Ans P B t u → Ans Δ (B [ θ ]ty) (t [ θ ]tm) (u [ θ ]tm)
pullA dθ (w , dw) = w [ _ ]tm , tm[] dw dθ
