------------------------------------------------------------------------
-- A CaTT-shaped coherence case for two-tier L (S30 repair candidate,
-- notes/lax-sc-completeness.md §4).
--
-- graySide's coherence case asks that supp(t : A) and supp(u : A) are
-- both the *full Gray support* of Θ. The candidate rule keeps the
-- operation case and replaces the coherence case by Finster–Mimram's
-- shape plus image equality:
--
--   cohCaseV Θ A t u  =  endsOK Θ A
--                      ∧ ↓supp(t : A) = ↓supp(u : A)      (image equality, by (B))
--                      ∧ every hom variable of Θ is used    (Var(t : A) = Var(Θ))
--
-- What is checked here:
--  * `cohV-tower`: in the strict model, cohCaseV's support clause makes
--    the two images equal (whole towers). This is the only place where
--    the soundness proof `Strict.Soundness` uses the coherence-case
--    hypothesis (`coh-top`); it is (B), `Strict.Recon.b-supp`, applied
--    to the two terms. A soundness proof for graySideV needs more than
--    this replacement: the support function `topS` (Gray.Support)
--    decides between identity and total-cell image using graySide's
--    `cohCase`, so it must be redefined with `cohCaseV`; the case split
--    in `Soundness.cohX`/`cellX` must follow it, and the lemmas about
--    `supp` (Strict.L, Strict.Hyp.flat-supp, Gray.Graded) must be
--    re-checked at that definition. This is NOT carried out here
--    (Strict.L and Strict.Hyp are instantiated at graySide's typing);
--    see the note. (The evaluation checks below are unaffected: every
--    coh occurring inside the tested terms is classified the same way
--    by both rules.)
--  * by evaluation: graySideV accepts the gap example of
--    Gray.CohCaseGap in both directions, still rejects the reverse
--    interchanger, and agrees with graySide on the Gray.Examples heads.
------------------------------------------------------------------------
module CaTTExp.Gray.CohCaseVar where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Hyp using (flat-supp)
open import CaTTExp.Strict.Recon using (b-supp)
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.Gray.Examples
  using (HComp; Txz; fg; f'g'; βα; αβ; ichTy; ich)
open import CaTTExp.Gray.CohCaseGap using (βα₂)

------------------------------------------------------------------------
-- The rule.

-- variable i occurs as an entry of some tuple of S
usesVar : Nat → TSet → Bool
usesVar i S = any (λ tup → any (λ j → i ==ℕ j) tup) S

isObj : Ctx → Nat → Bool
isObj Θ i = any (λ j → i ==ℕ j) (objs Θ)

-- every non-object variable of Θ occurs in the closed support
varFull : Ctx → TSet → Bool
varFull Θ S = all (λ i → isObj Θ i ∨ usesVar i (down Θ S)) (upto (len Θ ∸ 1))

cohCaseV : Ctx → Ty → Tm → Tm → Bool
cohCaseV Θ ⋆ t u = false
cohCaseV Θ A@(arr _ _ _) t u =
  endsOK Θ A ∧ sameDownClosure Θ (supp t A) (supp u A)
             ∧ varFull Θ (supp t A) ∧ varFull Θ (supp u A)

graySideV : Ctx → Ty → Tm → Tm → Bool
graySideV Θ A t u = cohCaseV Θ A t u ∨ opCase Θ A t u

------------------------------------------------------------------------
-- Strict-model soundness of the new coherence case: equal images.

cohV-tower : ∀ {Δ} → Δ ⊢ps → ∀ A₀ a₀ b₀ t u e₁ e₂ →
             IsCellL Δ e₁ e₂ (dim A₀) (towerOf t (arr A₀ a₀ b₀)) →
             IsCellL Δ e₁ e₂ (dim A₀) (towerOf u (arr A₀ a₀ b₀)) →
             T (sameDownClosure Δ (supp t (arr A₀ a₀ b₀)) (supp u (arr A₀ a₀ b₀))) →
             towerOf t (arr A₀ a₀ b₀) ≈w towerOf u (arr A₀ a₀ b₀)
cohV-tower P A₀ a₀ b₀ t u e₁ e₂ cT cU eq =
  b-supp P e₁ e₂ (dim A₀) (towerOf t (arr A₀ a₀ b₀)) (towerOf u (arr A₀ a₀ b₀))
         (supp t (arr A₀ a₀ b₀)) (supp u (arr A₀ a₀ b₀)) cT cU
         (flat-supp t A₀ a₀ b₀) (flat-supp u A₀ a₀ b₀) eq

top-≈w : ∀ X Y → X ≈w Y → top X ≈ top Y
top-≈w (base c)     (base c')       e           = e
top-≈w (step _ _ c) (step _ _ c')   (_ , _ , e) = e
top-≈w (base _)     (step _ _ _)    ()
top-≈w (step _ _ _) (base _)        ()

-- The exact statement coh-top provides to Strict.Soundness.
cohV-top : ∀ {Δ} → Δ ⊢ps → ∀ A₀ a₀ b₀ t u e₁ e₂ →
           IsCellL Δ e₁ e₂ (dim A₀) (towerOf t (arr A₀ a₀ b₀)) →
           IsCellL Δ e₁ e₂ (dim A₀) (towerOf u (arr A₀ a₀ b₀)) →
           T (cohCaseV Δ (arr A₀ a₀ b₀) t u) →
           top (towerOf t (arr A₀ a₀ b₀)) ≈ top (towerOf u (arr A₀ a₀ b₀))
cohV-top {Δ} P A₀ a₀ b₀ t u e₁ e₂ cT cU ok =
  top-≈w _ _ (cohV-tower P A₀ a₀ b₀ t u e₁ e₂ cT cU
               (∧-fst (∧-snd {endsOK Δ (arr A₀ a₀ b₀)} ok)))

------------------------------------------------------------------------
-- Evaluation checks.

A₁ : Ty
A₁ = arr Txz fg f'g'

-- the gap example is accepted, both directions
_ : graySideV HComp A₁ βα βα₂ ≡ true
_ = refl
_ : graySideV HComp A₁ βα₂ βα ≡ true
_ = refl
-- …and still rejected by graySide (Gray.CohCaseGap.gap)
_ : graySide HComp A₁ βα βα₂ ≡ false
_ = refl

-- the interchanger keeps its direction
_ : graySideV HComp A₁ βα αβ ≡ true
_ = refl
_ : graySideV HComp A₁ αβ βα ≡ false
_ = refl

-- the horizontal composite stays absent
open import CaTTExp.Gray.Examples using (comp; x; y; f; f'; z; g; g')
_ : graySideV HComp (arr ⋆ x z) (comp x y f z g) (comp x y f' z g') ≡ false
_ = refl

-- a coherence over the interchanger's own type: full Gray support,
-- accepted by both rules
_ : graySide  HComp ichTy ich ich ≡ true
_ = refl
_ : graySideV HComp ichTy ich ich ≡ true
_ = refl
